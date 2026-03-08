#!/usr/bin/env python3
"""
Ingenico LLT Multi-Terminal Loader v4.0
=======================================

Desktop application that automates loading packages and parameters onto
Ingenico POS terminals using LLT's command-line mode (cmdLine.bat / cmdLine.sh).

PARALLEL LOADING ARCHITECTURE
-----------------------------
The LLT User Guide states: "only one terminal connection is possible at one
time per LLT instance." This means a single cmdLine.bat process can only talk
to one terminal at a time.

To load N terminals simultaneously, this app:
  1. Launches N independent worker threads via ThreadPoolExecutor
     (one thread per terminal).
  2. Each thread independently:
       a. Generates its own XML with <connect device="COMx"/> for that port.
       b. Writes it to XML Folder (or system temp) as _loader_COMx.xml.
       c. cd's to llt_path and runs:
            cmdLine.bat /q [/v] /p COMx <abs_path_to_xml>
       d. Deletes the temp XML file when done.
  3. Results are collected per-terminal, displayed in status cards + log.

XML SCENARIO FORMAT (LLT 5.4 User Guide, Section 7)
----------------------------------------------------
Uses ANT standard XML. Key rules:
  - Single backslashes in paths are correct: C:\path\file.ext (LLT parses them correctly)
  - Encoding must be ISO-8859-1
  - cmdLine flags: /q = quiet, /v = verbose, /p port = COM port
  - If target is omitted in download, LLT auto-predicts by extension

TERMINAL FILE TREE (LLT 5.4 User Guide, Section 1.2)
-----------------------------------------------------
  Telium Tetra:   /package/ (signed apps)   /import/ (params)
  Telium 1 & 2:   /SWAP/    (signed apps)   /HOST/   (params)

AVAILABLE ACTIONS (LLT 5.4 User Guide, Section 7.1)
----------------------------------------------------
  terminals, connect, download, upload, delete, query,
  parse, activity, clean, enable, disable, disconnect

ERROR CODES (LLT 5.4 User Guide, Section 7.1.1)
-------------------------------------------------
   0  OK               -19  Unknown terminal port
  -1  Missing param    -20  Catalogue not adapted
  -2  Catalogue access -21  File not for this range
  -3  Target access    -22  Download error
  -4  File access      -23  Upload error
 -15  Activity failed  -24  Dest unreachable
 -25  Terminal file    -26  Source file access  -99  Unexpected

PERSISTENT CONFIG: ~/.llt_loader_config.json
  Saves: LLT path, folder path, file names, terminals, all options, geometry.
  Files stored as full absolute paths — supports files from multiple folders.

USAGE:  python llt_loader.py
BUILD:  pyinstaller --onefile --windowed --name LLT_Loader llt_loader.py
REQUIRES: Python 3.10+ (only built-in modules: tkinter, json, os, subprocess)
"""

import os
import re
import json
import csv
import glob
import subprocess
import threading
import platform
from pathlib import Path
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor, as_completed
import tempfile

import tkinter as tk
from tkinter import ttk, filedialog, messagebox


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  CONSTANTS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

APP_NAME = "Emilio's LLT Multi-Terminal Loader"
APP_VER  = "Test"
CFG_FILE = os.path.join(str(Path.home()), ".llt_loader_config.json")

# File extensions per LLT User Guide Section 1.2
PKG_EXT = {".P3A",".P3L",".P3O",".P3P",".P3S",".P3T",".AGN",".LGN",".PGN",".PKG"}
PAR_EXT = {".INI",".CFG",".TXT",".DAT",".XML",".JSON",".CSV",".BIN",".PAR",".BMP"}
ALL_EXT = PKG_EXT | PAR_EXT

# LLT error codes (User Guide Section 7.1.1)
LLT_ERRORS = {
    0:"OK", -1:"Missing parameter", -2:"Catalogue access problem",
    -3:"Target file access problem", -4:"Downloadable files access problem",
    -15:"Activity badly finished", -19:"Unknown terminal port",
    -20:"Catalogue not adapted", -21:"File not for this range",
    -22:"Error during download", -23:"Error during upload",
    -24:"Destination unreachable", -25:"Cannot access terminal file",
    -26:"Cannot access source file", -99:"Unexpected error",
}

# Actionable hints shown in the log when a known error code is returned
LLT_HINTS = {
    -3:  "Target file access problem — check Output Folder path and permissions.",
    -4:  "Check folder path — do the files exist?",
    -15: "Activity change failed — check terminal state.",
    -19: "Terminal not in LLT mode or wrong COM port selected.",
    -21: "File not for this range — check the Range option (Tetra vs T1/T2).",
    -22: "Download error — file may be corrupted or path is wrong.",
    -24: "Destination unreachable — terminal disconnected mid-transfer?",
    -25: "Cannot access terminal file — check terminal file system state.",
    -26: "Cannot access source file — verify file exists and path is correct.",
}


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  HELPERS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def is_catalogue(ext: str) -> bool:
    """
    Check if extension is a catalogue file (.Mnn or .MXX).
    Catalogue format per User Guide Section 5.1: .Mnn where nn = product code.
    .MXX targets all terminals.
    """
    e = ext.upper()
    return (len(e) == 4 and e.startswith(".M")
            and (e[2:].isdigit() or e[2:] == "XX"))


def get_dest(filename: str, terminal_range: str) -> str:
    """
    Determine target directory on terminal for a file.
    Rules from User Guide Section 1.2:
      Packages (.P3A etc) + catalogues (.Mnn) → /package/ (Tetra) or /SWAP/ (T1/T2)
      Parameters (.INI etc)                   → /import/  (Tetra) or /HOST/ (T1/T2)
    """
    ext = os.path.splitext(filename)[1].upper()
    is_pkg = ext in PKG_EXT or is_catalogue(ext)
    if terminal_range == "Telium Tetra":
        return "/package/" if is_pkg else "/import/"
    return "/SWAP/" if is_pkg else "/HOST/"


def esc(path: str) -> str:
    """
    Escape path for LLT XML attribute values.
    - Escapes XML special chars (&, ") so the generated XML is well-formed
    - Single backslashes only — LLT parses them correctly, doubling causes file-not-found
    """
    path = path.replace("&", "&amp;")
    path = path.replace('"', "&quot;")
    return path


def detect_ingenico_ports() -> dict:
    """
    Detect COM/serial ports and identify their device descriptions.
    Returns {port: description} for every detected port.
    Ports with 'Ingenico' in the description are Ingenico POS devices.

    Windows: WMI Win32_PnPEntity (device friendly name + COM port)
             Falls back to registry HARDWARE\\DEVICEMAP\\SERIALCOMM if WMI fails.
    Linux:   /dev/ttyUSB* + /dev/ttyACM*  — udevadm used for device model.
    macOS:   /dev/tty.usbserial* + /dev/tty.usbmodem*
    """
    port_info = {}
    s = platform.system()
    if s == "Windows":
        try:
            r = subprocess.run(
                ["wmic", "path", "Win32_PnPEntity",
                 "where", "Name like '%(COM%'", "get", "Name"],
                capture_output=True, text=True, timeout=8,
                creationflags=subprocess.CREATE_NO_WINDOW)
            for line in r.stdout.splitlines():
                line = line.strip()
                m = re.search(r'\(COM(\d+)\)', line)
                if m:
                    port = f"COM{m.group(1)}"
                    desc = line[:line.rfind('(COM')].strip().rstrip('(').strip()
                    port_info[port] = desc
        except Exception:
            pass
        if not port_info:  # WMI unavailable — fall back to registry (no descriptions)
            try:
                import winreg
                key = winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE,
                                     r"HARDWARE\DEVICEMAP\SERIALCOMM")
                i = 0
                while True:
                    try:
                        _, val, _ = winreg.EnumValue(key, i)
                        if val: port_info[str(val)] = ""
                        i += 1
                    except OSError:
                        break
                winreg.CloseKey(key)
            except Exception:
                pass
    elif s == "Linux":
        for pat in ("/dev/ttyUSB*", "/dev/ttyACM*"):
            for p in sorted(glob.glob(pat)):
                desc = ""
                try:
                    r = subprocess.run(
                        ["udevadm", "info", "--query=property", f"--name={p}"],
                        capture_output=True, text=True, timeout=3)
                    m = re.search(r'ID_MODEL=(.+)', r.stdout)
                    if m: desc = m.group(1).replace('_', ' ').strip()
                except Exception:
                    pass
                port_info[p] = desc
    elif s == "Darwin":
        for pat in ("/dev/tty.usbserial*", "/dev/tty.usbmodem*"):
            for p in sorted(glob.glob(pat)):
                port_info[p] = ""
    return port_info


def load_config() -> dict:
    """Load config from ~/.llt_loader_config.json"""
    try:
        with open(CFG_FILE, "r", encoding="utf-8") as f: return json.load(f)
    except Exception:
        return {}

def save_config(cfg: dict):
    """Save config to ~/.llt_loader_config.json"""
    try:
        with open(CFG_FILE, "w", encoding="utf-8") as f: json.dump(cfg, f, indent=2)
    except Exception:
        pass


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  XML GENERATION — ONE XML PER TERMINAL
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def build_xml(files: list[dict], port: str, opts: dict) -> str:
    """
    Generate XML scenario for ONE terminal on a specific COM port.

    CRITICAL: Each terminal must get its own XML because <connect device="COMx"/>
    is hardcoded per port. This is why parallel loading works — N XMLs, N processes.

    Args:
        files: [{"path": "C:\\pkg\\MyApp.P3A", "dest": "/package/"}, ...]
        port:  "COM5" or "" for auto-detect
        opts:  dict of option flags from _opts()
    """
    I = "    "  # 4-space indent inside <target>
    t = ""    # accumulate task lines

    def task(**attrs) -> str:
        """Build a single-line <jllt.commandLineTask .../> matching working XML format."""
        parts = " ".join(f'{k}="{v}"' for k, v in attrs.items())
        return f'{I}<jllt.commandLineTask {parts}/>\n'

    # ── Pre-connect: list terminals ──
    if opts.get("list_terminals"):
        tp = esc(os.path.join(opts.get("out_dir", tempfile.gettempdir()), f"Terminals_{port or 'auto'}.txt"))
        t += task(action="terminals", target=tp)

    # ── Connect ──
    if port:
        t += task(action="connect", device=port)
    else:
        t += task(action="connect")

    # ── Post-connect options (must come after connect) ──
    if opts.get("ignore_errors"):
        t += task(action="enable", option="ignore errors")
    if opts.get("force_uppercase"):
        t += task(action="enable", option="force uppercase")
    if opts.get("result_file"):
        rp = esc(os.path.join(opts.get("out_dir", tempfile.gettempdir()), f"result_{port or 'auto'}.log"))
        t += task(action="enable", option="result file", target=rp)

    # ── Query terminal info ──
    if opts.get("query_info"):
        lbl = port or "auto"
        od = opts.get("out_dir", tempfile.gettempdir())
        t += task(action="query", property="Manufacturing Code",  target=esc(os.path.join(od, f"MfgCode_{lbl}.txt")))
        t += task(action="query", property="Islero Serial Number", target=esc(os.path.join(od, f"Serial_{lbl}.txt")))

    # ── Clean terminal ──
    if opts.get("clean_before"):
        if opts.get("uninstall_packages"):
            t += task(action="clean", option="uninstall packages")
        else:
            t += task(action="clean")

    # ── Downloads (the main payload) ──
    for fi in files:
        if opts.get("auto_dest"):
            t += task(action="download", source=esc(fi["path"]))
        else:
            t += task(action="download", source=esc(fi["path"]), target=fi["dest"])

    # ── Upload config from terminal ──
    if opts.get("upload_config"):
        lbl = port or "auto"
        if opts.get("range") == "Telium Tetra":
            src, dest_name = "/SYST/HTERMINAL.INI", f"HTERMINAL_{lbl}.INI"
        else:
            src, dest_name = "/HOST/APPRESET.DIA", f"APPRESET_{lbl}.DIA"
        ud = esc(os.path.join(opts.get("out_dir", tempfile.gettempdir()), dest_name))
        t += task(action="upload", source=src, target=ud)

    # ── Activity change ──
    if opts.get("activity"):
        t += task(action="activity", mode=opts["activity"])

    # ── Disconnect — commits transaction, validates packages ──
    if opts.get("auto_disconnect", True):
        t += task(action="disconnect")

    lbl = port or "auto"
    return (f'<project name="Loader" basedir="." default="Load{lbl}">\n'
            f'<target name="Load{lbl}">\n{t}'
            f'</target>\n</project>\n')


def build_batch(llt_path: str, port: str, xml_name: str, opts: dict) -> str:
    """Generate batch script for ONE terminal."""
    v = " /v" if opts.get("verbose") else ""
    p = f" /p {port}" if port else ""
    return (f'@echo off\nchcp 65001 >nul\n'
            f'echo ============================================\n'
            f'echo   LLT Loader [{port or "auto"}]\n'
            f'echo ============================================\n'
            f'echo.\n\n'
            f'if not exist "{llt_path}\\cmdLine.bat" (\n'
            f'    echo [ERROR] cmdLine.bat not found in: "{llt_path}"\n'
            f'    pause & exit /b 1\n)\n\n'
            f'cd /d "{llt_path}"\n'
            f'cmdLine.bat /q{v}{p} "%~dp0{xml_name}"\n\n'
            f'set R=%ERRORLEVEL%\necho.\n'
            f'if %R% EQU 0 (echo [SUCCESS]) else (\n'
            f'    echo [ERROR] Code: %R%\n'
            f'    if %R% EQU -4  echo   File access problem - check folder path\n'
            f'    if %R% EQU -15 echo   Activity badly finished\n'
            f'    if %R% EQU -19 echo   Unknown port - terminal in LLT mode?\n'
            f'    if %R% EQU -21 echo   File not for this range - check Tetra vs T1/T2\n'
            f'    if %R% EQU -22 echo   Download error - file corrupted or path wrong\n'
            f'    if %R% EQU -24 echo   Destination unreachable\n)\n'
            f'echo.\npause\nexit /b %R%\n')


def update_terminal_log(out_dir: str, label: str, opts: dict) -> str:
    """
    Update terminal_log.csv in out_dir after a successful load.

    CSV format:
      Manufacturing Code
      1234567890
      9876543210
      Total devices: 2

    - One row per unique device (Manufacturing Code = unique key).
    - No duplicates — if the code already exists, nothing changes.
    - Total count is always recalculated and written at the bottom.
    - Only runs when 'query_info' option is enabled (LLT must write MfgCode file).

    Returns a status message string (empty string if query_info is off or code already exists).
    """
    if not opts.get("query_info"):
        return ""

    # Read the Manufacturing Code written by LLT
    mfg_file = os.path.join(out_dir, f"MfgCode_{label}.txt")
    try:
        with open(mfg_file, "r", encoding="utf-8", errors="replace") as f:
            mfg = f.read().strip()
    except Exception:
        return "Query info ON but MfgCode file not found — was the terminal queried?"
    if not mfg:
        return "MfgCode file is empty — LLT may not have returned a value."

    csv_path = os.path.join(out_dir, "terminal_log.csv")

    # Read existing codes (skip the "Total devices:" summary row)
    codes = []
    if os.path.isfile(csv_path):
        try:
            with open(csv_path, "r", newline="", encoding="utf-8") as f:
                reader = csv.reader(f)
                next(reader, None)  # skip header
                for row in reader:
                    if row and not row[0].startswith("Total devices:"):
                        codes.append(row[0].strip())
        except Exception:
            codes = []

    # Already recorded — no duplicate
    if mfg in codes:
        return ""

    codes.append(mfg)

    # Write back: header + codes + total
    try:
        with open(csv_path, "w", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            writer.writerow(["Manufacturing Code"])
            for code in codes:
                writer.writerow([code])
            writer.writerow([f"Total devices: {len(codes)}"])
        return f"Logged to terminal_log.csv — total devices: {len(codes)}"
    except Exception as e:
        return f"Could not write terminal_log.csv: {e}"


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  PARALLEL ENGINE — RUNS ONE CMDLINE.BAT PER TERMINAL
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def run_terminal(llt_path: str, port: str, files: list, opts: dict,
                 on_log, xml_dir: str = "") -> tuple:
    """
    Execute cmdLine for ONE terminal. Called by ThreadPoolExecutor.

    Flow:
      1. Build XML for this terminal (port-specific <connect device="COMx"/>)
      2. Write XML to temp file in xml_dir (defaults to system temp if not set)
      3. cd to llt_path, run: cmdLine.bat /q [/v] [/p COMx] <abs_xml_path>
      4. Capture stdout+stderr, return (label, exit_code, output)
      5. Delete temp XML

    This function runs in a worker thread. Use on_log() for thread-safe logging.
    """
    label = port or "auto"
    verbose = opts.get("verbose", False)
    is_win = platform.system() == "Windows"
    cmd_exe = os.path.join(llt_path, "cmdLine.bat" if is_win else "cmdLine.sh")

    # 1. Generate XML for this specific terminal
    xml_str = build_xml(files, port, opts)

    # 2. Write temp XML to xml_dir (never inside the LLT install folder)
    _xml_dir = xml_dir if xml_dir and os.path.isdir(xml_dir) else tempfile.gettempdir()
    xml_path = os.path.join(_xml_dir, f"_loader_{label}.xml")
    try:
        # Outer finally ensures cleanup even if the write itself fails partway through
        try:
            with open(xml_path, "w", encoding="ISO-8859-1") as f:
                f.write(xml_str)
        except Exception as e:
            return label, -99, f"Cannot write XML: {e}"

        # 3. Build command
        args = [cmd_exe, "/q"]
        if verbose: args.append("/v")
        if port: args.extend(["/p", port])
        args.append(xml_path)

        on_log(f"[{label}] Running: {os.path.basename(cmd_exe)} /q"
               f"{' /v' if verbose else ''}{f' /p {port}' if port else ''}"
               f" _loader_{label}.xml")

        # 4. Execute subprocess
        try:
            kw = {}
            if is_win:
                kw["creationflags"] = subprocess.CREATE_NO_WINDOW
            proc = subprocess.run(args, cwd=llt_path, capture_output=True,
                                  text=True, errors="replace", timeout=600, **kw)
            return label, proc.returncode, (proc.stdout + proc.stderr).strip()
        except subprocess.TimeoutExpired:
            return label, -99, "Timeout (600s)"
        except Exception as e:
            return label, -99, str(e)
    finally:
        try: os.remove(xml_path)
        except OSError: pass


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  THEME
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class Theme:
    BG   = "#1a1a1a"; BG2 = "#222"; BG3 = "#2a2a2a"
    FG   = "#d4d4d4"; FG2 = "#999"; FG3 = "#666"
    GRN  = "#16a34a"; GRL = "#4ade80"
    RED  = "#f87171"; YEL = "#fbbf24"; BLU = "#60a5fa"
    BRD  = "#333"; INP = "#111"
    FN   = ("Segoe UI", 10); FS = ("Segoe UI", 9)
    FXS  = ("Segoe UI", 8); MO = ("Consolas", 9)

    @staticmethod
    def apply(root):
        s = ttk.Style(); s.theme_use("clam"); T = Theme
        s.configure(".", background=T.BG, foreground=T.FG,
                     fieldbackground=T.INP, borderwidth=0, focusthickness=0)
        s.configure("TFrame", background=T.BG)
        s.configure("TLabel", background=T.BG, foreground=T.FG, font=T.FN)
        s.configure("Dim.TLabel", foreground=T.FG3, font=T.FXS)
        s.configure("TLabelframe", background=T.BG, foreground=T.FG2,
                     bordercolor=T.BRD, lightcolor=T.BRD, darkcolor=T.BRD)
        s.configure("TLabelframe.Label", background=T.BG, foreground=T.FG2,
                     font=("Segoe UI Semibold", 9))
        s.configure("TButton", background=T.BG3, foreground=T.FG,
                     padding=(12, 6), font=T.FS, relief="flat")
        s.map("TButton", background=[("active", "#3e3e3e")])
        s.configure("Go.TButton", background=T.GRN, foreground="white",
                     font=("Segoe UI Semibold", 11), padding=(20, 10))
        s.map("Go.TButton", background=[("active", "#15803d")])
        s.configure("Scan.TButton", background="#1a3a5c", foreground=T.BLU,
                     font=("Segoe UI Semibold", 9), padding=(10, 5))
        s.map("Scan.TButton", background=[("active", "#1e4a7a")])
        s.configure("TCheckbutton", background=T.BG, foreground=T.FG, font=T.FS)
        s.map("TCheckbutton", background=[("active", T.BG)])
        s.configure("TCombobox", fieldbackground=T.INP, foreground=T.FG, font=T.FS)
        s.map("TCombobox",
              fieldbackground=[("readonly", T.INP), ("disabled", T.BG)],
              foreground=[("readonly", T.FG), ("disabled", T.FG2)],
              selectbackground=[("readonly", T.INP)],
              selectforeground=[("readonly", T.FG)])
        s.configure("TEntry", fieldbackground=T.INP, foreground=T.FG,
                     font=T.FS, insertcolor=T.FG)
        s.configure("Treeview", background=T.INP, foreground=T.FG,
                     fieldbackground=T.INP, rowheight=26, font=T.FS)
        s.configure("Treeview.Heading", background=T.BG3, foreground=T.FG2,
                     font=("Segoe UI Semibold", 9))
        s.map("Treeview", background=[("selected", "#1e3a1e")],
              foreground=[("selected", T.GRL)])
        s.configure("Vertical.TScrollbar", background=T.BG3, troughcolor=T.BG)
        s.configure("Horizontal.TScrollbar", background=T.BG3, troughcolor=T.BG)
        root.configure(bg=T.BG)
        root.option_add("*TCombobox*Listbox.background", T.INP)
        root.option_add("*TCombobox*Listbox.foreground", T.FG)
        root.option_add("*TCombobox*Listbox.selectBackground", T.GRN)


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  MAIN APP
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class LLTApp:
    """
    Main application. Scrollable single-page UI:
      Paths → Terminals + Options → Files → Actions → Log
    """

    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title(f"{APP_NAME} v{APP_VER}")
        self.root.minsize(850, 550)
        cfg = load_config()
        # Restore saved geometry only if position is on-screen (prevents off-screen window
        # when config was saved on a different monitor layout or PC)
        geo = cfg.get("geometry", "1050x750")
        try:
            m = re.match(r'(\d+)x(\d+)\+(-?\d+)\+(-?\d+)', geo)
            if m:
                x, y = int(m.group(3)), int(m.group(4))
                sw, sh = root.winfo_screenwidth(), root.winfo_screenheight()
                if x < -100 or y < -100 or x > sw or y > sh:
                    geo = f"{m.group(1)}x{m.group(2)}"  # keep size, drop position
        except Exception:
            geo = "1050x750"
        self.root.geometry(geo)
        Theme.apply(root)

        # Tk variables (restored from config)
        self.llt_path     = tk.StringVar(value=cfg.get("llt_path", r"C:\Program Files\Ingenico\LLT"))
        self.xml_dir      = tk.StringVar(value=cfg.get("xml_dir", ""))
        self.out_dir      = tk.StringVar(value=cfg.get("out_dir", ""))
        _range = cfg.get("range", "Telium Tetra")
        if _range not in ("Telium Tetra", "Telium 1 & 2"):
            _range = "Telium Tetra"
        self.range_var    = tk.StringVar(value=_range)
        self.ignore_err   = tk.BooleanVar(value=cfg.get("ignore_errors", False))
        self.force_upper  = tk.BooleanVar(value=cfg.get("force_uppercase", False))
        self.auto_disc    = tk.BooleanVar(value=cfg.get("auto_disconnect", True))
        self.verbose      = tk.BooleanVar(value=cfg.get("verbose", False))
        self.auto_dest    = tk.BooleanVar(value=cfg.get("auto_dest", False))
        self.clean_before = tk.BooleanVar(value=cfg.get("clean_before", False))
        self.uninstall_pk = tk.BooleanVar(value=cfg.get("uninstall_pkg", False))
        self.query_info   = tk.BooleanVar(value=cfg.get("query_info", False))
        self.list_terms   = tk.BooleanVar(value=cfg.get("list_terminals", False))
        self.result_file  = tk.BooleanVar(value=cfg.get("result_file", False))
        self.upload_cfg   = tk.BooleanVar(value=cfg.get("upload_config", False))
        self.activity_var = tk.StringVar(value=cfg.get("activity", ""))

        _raw_names = cfg.get("saved_files", [])
        _folder = cfg.get("folder_path", "")
        # Migrate old format: bare filenames → full paths using saved folder_path
        self.saved_names: list[str] = [
            p if os.path.isabs(p) else os.path.join(_folder, p)
            for p in _raw_names
        ]
        # Package folders: load from config, fall back to legacy single folder_path
        _saved_folders = cfg.get("pkg_folders", [])
        if not _saved_folders and _folder:
            _saved_folders = [_folder]
        self._init_folders: list[str] = _saved_folders  # consumed by _build_ui
        self._folder_svars: list[tk.StringVar] = []     # populated by _add_pkg_folder
        self.terminals: list[dict] = cfg.get("terminals", [{"port": "", "enabled": True}])
        self.detected_ports: list[str] = []
        self.port_descriptions: dict = {}
        self.is_loading = False
        self._detecting = False
        self._alive = True          # set False on close to stop root.after() calls
        self._term_bvars: list = []
        self._term_svars: list = []

        self._build_ui()
        if self.saved_names:
            self._rebuild_tree()
        self.root.after(300, self._detect_ports)
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

    # ── Config ─────────────────────────────────────────────────────

    def _opts(self) -> dict:
        """Collect all option flags into dict for XML generation."""
        return dict(
            ignore_errors=self.ignore_err.get(), force_uppercase=self.force_upper.get(),
            auto_disconnect=self.auto_disc.get(), verbose=self.verbose.get(),
            auto_dest=self.auto_dest.get(), clean_before=self.clean_before.get(),
            uninstall_packages=self.uninstall_pk.get(), query_info=self.query_info.get(),
            list_terminals=self.list_terms.get(), result_file=self.result_file.get(),
            upload_config=self.upload_cfg.get(), activity=self.activity_var.get(),
            range=self.range_var.get(),
            out_dir=os.path.normpath(self.out_dir.get()) if self.out_dir.get() and os.path.isdir(self.out_dir.get()) else tempfile.gettempdir(),
        )

    def _save_cfg(self):
        save_config(dict(
            llt_path=self.llt_path.get(),
            pkg_folders=self._get_pkg_folders(),
            folder_path=self._first_folder(),  # backward compat for old installs
            xml_dir=self.xml_dir.get(), out_dir=self.out_dir.get(),
            range=self.range_var.get(), ignore_errors=self.ignore_err.get(),
            force_uppercase=self.force_upper.get(), auto_disconnect=self.auto_disc.get(),
            verbose=self.verbose.get(), auto_dest=self.auto_dest.get(),
            clean_before=self.clean_before.get(), uninstall_pkg=self.uninstall_pk.get(),
            query_info=self.query_info.get(), list_terminals=self.list_terms.get(),
            result_file=self.result_file.get(), upload_config=self.upload_cfg.get(),
            activity=self.activity_var.get(), saved_files=self.saved_names,
            terminals=self.terminals, geometry=self.root.geometry(),
        ))

    def _on_close(self):
        if self.is_loading:
            if not messagebox.askyesno(
                    "Load in progress",
                    "A load operation is still running.\nClose anyway and abort?"):
                return
        self._alive = False
        self._save_cfg()
        self.root.destroy()

    # ── UI ─────────────────────────────────────────────────────────

    def _build_ui(self):
        """Build full scrollable interface."""
        outer = ttk.Frame(self.root)
        outer.pack(fill=tk.BOTH, expand=True)

        self.canvas = tk.Canvas(outer, bg=Theme.BG, highlightthickness=0)
        vsb = ttk.Scrollbar(outer, orient=tk.VERTICAL, command=self.canvas.yview)
        self.inner = ttk.Frame(self.canvas)
        self.inner.bind("<Configure>",
                        lambda _: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        self._cw = self.canvas.create_window((0, 0), window=self.inner, anchor="nw")
        self.canvas.configure(yscrollcommand=vsb.set)
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)
        self.canvas.bind("<Configure>",
                         lambda e: self.canvas.itemconfig(self._cw, width=e.width))
        self.canvas.bind_all("<MouseWheel>",
                             lambda e: self.canvas.yview_scroll(int(-1*(e.delta/120)), "units"))
        self.canvas.bind_all("<Button-4>", lambda _: self.canvas.yview_scroll(-3, "units"))
        self.canvas.bind_all("<Button-5>", lambda _: self.canvas.yview_scroll(3, "units"))

        f = self.inner
        P = dict(padx=16, pady=(6, 4))

        # Header
        hdr = ttk.Frame(f); hdr.pack(fill=tk.X, padx=16, pady=(14, 10))
        ttk.Label(hdr, text="⬢", foreground=Theme.GRL, font=("Segoe UI", 20)).pack(side=tk.LEFT)
        ttk.Label(hdr, text=f"  {APP_NAME}", font=("Segoe UI Semibold", 15)).pack(side=tk.LEFT)
        ttk.Label(hdr, text=f"  v{APP_VER} · LLT 5.4", foreground=Theme.FG3,
                  font=Theme.FXS).pack(side=tk.LEFT, padx=6)

        # ── PATHS ──
        pf = ttk.LabelFrame(f, text="  Paths  ", padding=12)
        pf.pack(fill=tk.X, **P)
        r1 = ttk.Frame(pf); r1.pack(fill=tk.X, pady=(0, 6))
        ttk.Label(r1, text="LLT Install:", width=16, anchor="e").pack(side=tk.LEFT)
        ttk.Entry(r1, textvariable=self.llt_path).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=6)
        ttk.Button(r1, text="Browse", command=self._br_llt).pack(side=tk.LEFT)
        r2 = ttk.Frame(pf); r2.pack(fill=tk.X, pady=(6, 0))
        ttk.Label(r2, text="Pkg Folders:", width=16, anchor="e").pack(side=tk.LEFT, anchor="nw", pady=8)
        self.pkg_folder_frame = ttk.Frame(r2)
        self.pkg_folder_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)
        for _folder_init in (self._init_folders or [""]):
            self._add_pkg_folder(_folder_init)
        r3 = ttk.Frame(pf); r3.pack(fill=tk.X, pady=(6, 0))
        ttk.Label(r3, text="XML Folder:", width=16, anchor="e").pack(side=tk.LEFT)
        ttk.Entry(r3, textvariable=self.xml_dir).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=6)
        ttk.Button(r3, text="Browse", command=self._br_xml_dir).pack(side=tk.LEFT)
        r4 = ttk.Frame(pf); r4.pack(fill=tk.X, pady=(6, 0))
        ttk.Label(r4, text="Output Folder:", width=16, anchor="e").pack(side=tk.LEFT)
        ttk.Entry(r4, textvariable=self.out_dir).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=6)
        ttk.Button(r4, text="Browse", command=self._br_out_dir).pack(side=tk.LEFT)
        ttk.Label(pf, text="Pkg Folders: add as many source folders as needed, then click Scan All. "
                  "XML Folder: temp XMLs during load (defaults to system temp). "
                  "Output Folder: query results, terminal list, result file, upload config (defaults to system temp).",
                  style="Dim.TLabel").pack(anchor="w", pady=(6, 0))

        # ── TERMINALS + OPTIONS ──
        mid = ttk.Frame(f); mid.pack(fill=tk.X, **P)
        mid.columnconfigure(0, weight=3); mid.columnconfigure(1, weight=2)

        tf = ttk.LabelFrame(mid, text="  Terminals  ", padding=10)
        tf.grid(row=0, column=0, sticky="nsew", padx=(0, 6))
        self.term_frame = ttk.Frame(tf); self.term_frame.pack(fill=tk.X)
        self._refresh_terms()
        tb = ttk.Frame(tf); tb.pack(fill=tk.X, pady=(6, 0))
        self.detect_btn = ttk.Button(tb, text="Detect", command=self._detect_ports)
        self.detect_btn.pack(side=tk.LEFT)
        ttk.Button(tb, text="+ Add", command=self._add_term).pack(side=tk.LEFT, padx=6)
        self.status_frame = ttk.Frame(tf)
        self.status_frame.pack(fill=tk.X, pady=(6, 0))
        ttk.Label(tf, text="Each terminal = separate cmdLine.bat process (true parallel).",
                  style="Dim.TLabel").pack(anchor="w", pady=(4, 0))

        of = ttk.LabelFrame(mid, text="  Options  ", padding=10)
        of.grid(row=0, column=1, sticky="nsew", padx=(6, 0))
        rf = ttk.Frame(of); rf.pack(fill=tk.X, pady=(0, 4))
        ttk.Label(rf, text="Range:").pack(side=tk.LEFT)
        rc = ttk.Combobox(rf, textvariable=self.range_var,
                          values=["Telium Tetra", "Telium 1 & 2"], state="readonly", width=14)
        rc.pack(side=tk.LEFT, padx=4)
        rc.bind("<<ComboboxSelected>>", lambda _: self._rebuild_tree())
        af = ttk.Frame(of); af.pack(fill=tk.X, pady=(0, 4))
        ttk.Label(af, text="Activity:").pack(side=tk.LEFT)
        ttk.Combobox(af, textvariable=self.activity_var,
                     values=["", "download", "diagnostic", "maintenance"],
                     state="readonly", width=14).pack(side=tk.LEFT, padx=4)

        for var, lbl, tip in [
            (self.force_upper,  "Force uppercase",   "T1/T2 full name · Tetra ext"),
            (self.ignore_err,   "Ignore errors",     "Non-blocking failures"),
            (self.auto_disc,    "Auto-disconnect",   "Commit & install"),
            (self.verbose,      "Verbose /v",        "Debug output"),
            (self.auto_dest,    "Auto-destination",  "LLT detects by ext"),
            (self.clean_before, "Clean before load", "Wipe terminal first"),
            (self.uninstall_pk, "Uninstall pkgs", "Remove packages too"),
            (self.query_info,   "Query info",        "Mfg Code + Serial"),
            (self.list_terms,   "List terminals",    "Port/Range/State"),
            (self.result_file,  "Result file",       "Error log per terminal"),
            (self.upload_cfg,   "Upload config",     "HTERMINAL / APPRESET"),
        ]:
            ro = ttk.Frame(of); ro.pack(fill=tk.X, pady=1)
            ttk.Checkbutton(ro, variable=var, text=lbl).pack(side=tk.LEFT)
            ttk.Label(ro, text=tip, style="Dim.TLabel").pack(side=tk.RIGHT)

        # ── FILES ──
        ff = ttk.LabelFrame(f, text="  Files  ", padding=10)
        ff.pack(fill=tk.BOTH, expand=True, **P)
        ab = ttk.Frame(ff); ab.pack(fill=tk.X, pady=(0, 6))
        ttk.Label(ab, text="Add:").pack(side=tk.LEFT)
        self.file_entry = ttk.Entry(ab, width=30)
        self.file_entry.pack(side=tk.LEFT, padx=6, fill=tk.X, expand=True)
        self.file_entry.bind("<Return>", lambda _: self._add_manual())
        ttk.Button(ab, text="Add", command=self._add_manual).pack(side=tk.LEFT)
        ttk.Button(ab, text="Browse…", command=self._br_files).pack(side=tk.LEFT, padx=6)
        ttk.Button(ab, text="Clear", command=self._clear_files).pack(side=tk.RIGHT)

        tf2 = ttk.Frame(ff); tf2.pack(fill=tk.BOTH, expand=True)
        cols = ("name", "path", "dest", "type")
        self.tree = ttk.Treeview(tf2, columns=cols, show="headings", height=8)
        self.tree.heading("name", text="Filename")
        self.tree.heading("path", text="Full Path")
        self.tree.heading("dest", text="Destination")
        self.tree.heading("type", text="Type")
        self.tree.column("name", width=180, minwidth=100)
        self.tree.column("path", width=300, minwidth=120)
        self.tree.column("dest", width=90, minwidth=60)
        self.tree.column("type", width=50, minwidth=40)
        tsb = ttk.Scrollbar(tf2, orient=tk.VERTICAL, command=self.tree.yview)
        self.tree.configure(yscrollcommand=tsb.set)
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        tsb.pack(side=tk.RIGHT, fill=tk.Y)
        self.tree.bind("<Delete>", lambda _: self._rm_selected())
        self.tree.bind("<MouseWheel>",
                       lambda e: (self.tree.yview_scroll(int(-1*(e.delta/120)), "units"), "break")[1])
        self.tree.bind("<Button-4>", lambda _: (self.tree.yview_scroll(-3, "units"), "break")[1])
        self.tree.bind("<Button-5>", lambda _: (self.tree.yview_scroll(3, "units"), "break")[1])
        ttk.Label(ff, text="PKG: .P3A .P3L .P3O .P3P .P3S .P3T .AGN .LGN .PGN .PKG  |  "
                  "PAR: .INI .CFG .TXT .DAT .XML .JSON .CSV .BIN .PAR .BMP  |  CAT: .Mnn .MXX",
                  style="Dim.TLabel").pack(anchor="w", pady=(6, 0))

        # ── ACTIONS ──
        bf = ttk.Frame(f); bf.pack(fill=tk.X, padx=16, pady=(10, 4))
        self.run_btn = ttk.Button(bf, text="▶  Generate & Load", style="Go.TButton",
                                  command=self._run)
        self.run_btn.pack(side=tk.LEFT)
        self.query_btn = ttk.Button(bf, text="⬡  Query Only", command=self._run_query)
        self.query_btn.pack(side=tk.LEFT, padx=10)
        ttk.Button(bf, text="Preview XML", command=self._preview).pack(side=tk.LEFT)
        ttk.Button(bf, text="Export Scripts…", command=self._export).pack(side=tk.LEFT, padx=10)
        ttk.Button(bf, text="Open Output", command=self._open_out_dir).pack(side=tk.LEFT)

        # ── LOG ──
        lf = ttk.LabelFrame(f, text="  Log  ", padding=8)
        lf.pack(fill=tk.X, padx=16, pady=(4, 14))
        log_hdr = ttk.Frame(lf); log_hdr.pack(fill=tk.X, pady=(0, 4))
        ttk.Button(log_hdr, text="Clear Log", command=self._clear_log).pack(side=tk.RIGHT)
        log_frm = ttk.Frame(lf); log_frm.pack(fill=tk.X)
        log_sb = ttk.Scrollbar(log_frm, orient=tk.VERTICAL)
        self.log_text = tk.Text(log_frm, height=10, bg=Theme.INP, fg=Theme.FG,
                                insertbackground=Theme.FG, font=Theme.MO,
                                relief="flat", wrap=tk.WORD, borderwidth=0,
                                yscrollcommand=log_sb.set)
        log_sb.config(command=self.log_text.yview)
        log_sb.pack(side=tk.RIGHT, fill=tk.Y)
        self.log_text.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.log_text.bind("<MouseWheel>",
                           lambda e: (self.log_text.yview_scroll(int(-1*(e.delta/120)), "units"), "break")[1])
        self.log_text.bind("<Button-4>", lambda _: (self.log_text.yview_scroll(-3, "units"), "break")[1])
        self.log_text.bind("<Button-5>", lambda _: (self.log_text.yview_scroll(3, "units"), "break")[1])
        self.log_text.tag_config("err", foreground=Theme.RED)
        self.log_text.tag_config("ok",  foreground=Theme.GRL)
        self.log_text.tag_config("warn", foreground=Theme.YEL)
        self.log_text.tag_config("info", foreground=Theme.FG3)
        self.log_text.config(state="disabled")

        # ── STATUS BAR ──
        self.status = tk.Label(self.root, text="Ready", bg="#111",
                               fg=Theme.FG3, anchor="w", padx=10, pady=3, font=Theme.FXS)
        self.status.pack(fill=tk.X, side=tk.BOTTOM)

    # ── Terminals ──────────────────────────────────────────────────

    def _refresh_terms(self):
        """Rebuild terminal rows from self.terminals list."""
        self._term_bvars = []  # hold refs to prevent BooleanVar garbage collection
        self._term_svars = []  # hold refs to prevent StringVar garbage collection
        for w in self.term_frame.winfo_children(): w.destroy()
        for i, t in enumerate(self.terminals):
            row = ttk.Frame(self.term_frame); row.pack(fill=tk.X, pady=2)
            ev = tk.BooleanVar(value=t.get("enabled", True))
            self._term_bvars.append(ev)
            ttk.Checkbutton(row, variable=ev,
                            command=lambda idx=i, v=ev: self._upd_term(idx, "enabled", v.get())
                            ).pack(side=tk.LEFT)
            ttk.Label(row, text=f"T{i+1}", foreground=Theme.FG3,
                      font=Theme.FXS, width=3).pack(side=tk.LEFT)
            # Build initial display value matching dropdown labels so selection shows correctly
            saved_port = t.get("port", "")
            if saved_port and saved_port in self.port_descriptions:
                d = self.port_descriptions.get(saved_port, "")
                if "ingenico" in d.lower():
                    initial_val = f"⬢ {saved_port} [Ingenico]"
                else:
                    initial_val = f"● {saved_port}"
            elif not saved_port:
                initial_val = "(auto)"
            else:
                initial_val = saved_port  # manually entered port not in detected list
            pv = tk.StringVar(value=initial_val)
            self._term_svars.append(pv)
            vals = ["(auto)"]
            for p in self.detected_ports:
                d = self.port_descriptions.get(p, "")
                if "ingenico" in d.lower():
                    vals.append(f"⬢ {p} [Ingenico]")
                else:
                    vals.append(f"● {p}")
            vals += [f"COM{j}" for j in range(1, 21) if f"COM{j}" not in self.detected_ports]
            c = ttk.Combobox(row, textvariable=pv, values=vals, width=22)
            c.pack(side=tk.LEFT, padx=4)
            c.bind("<<ComboboxSelected>>",
                   lambda _, idx=i, v=pv: self._upd_term(
                       idx, "port",
                       "" if v.get() == "(auto)" else
                       v.get().lstrip("⬢● ").split(" [")[0]))
            c.bind("<FocusOut>",
                   lambda _, idx=i, v=pv: self._upd_term(
                       idx, "port",
                       "" if v.get().strip() in ("(auto)", "") else
                       v.get().strip().lstrip("⬢● ").split(" [")[0].strip()))
            if len(self.terminals) > 1:
                ttk.Button(row, text="×",
                           command=lambda idx=i: self._rm_term(idx)).pack(side=tk.RIGHT)

    def _upd_term(self, i, k, v):
        if 0 <= i < len(self.terminals):
            self.terminals[i][k] = v

    def _add_term(self):
        self.terminals.append({"port": "", "enabled": True})
        self._refresh_terms()

    def _rm_term(self, i):
        if len(self.terminals) > 1:
            self.terminals.pop(i)
            self._refresh_terms()

    def _detect_ports(self):
        """Start port detection in background thread to avoid freezing the UI."""
        if self._detecting:
            return
        self._detecting = True
        self.detect_btn.config(state="disabled", text="Detecting…")
        self.status.config(text="Detecting ports...", fg=Theme.YEL)

        def _worker():
            result = detect_ingenico_ports()
            if self._alive:
                self.root.after(0, lambda: self._on_ports_detected(result))

        threading.Thread(target=_worker, daemon=True).start()

    def _on_ports_detected(self, port_descriptions: dict):
        """Called on the main thread once background port detection completes."""
        self._detecting = False
        self.detect_btn.config(state="normal", text="Detect")
        self.port_descriptions = port_descriptions
        _pnum = lambda p: (lambda m: int(m.group()) if m else 0)(re.search(r'\d+', p))
        self.detected_ports = sorted(self.port_descriptions.keys(), key=_pnum)
        ingenico = sorted(
            [p for p, d in self.port_descriptions.items() if "ingenico" in d.lower()],
            key=_pnum)
        if ingenico:
            self._log(f"Ingenico device(s) found: {', '.join(ingenico)}", "ok")
            for p in self.detected_ports:
                d = self.port_descriptions.get(p, "")
                tag = "ok" if "ingenico" in d.lower() else "info"
                self._log(f"  {p}: {d or 'Unknown device'}", tag)
            if self.terminals and not self.terminals[0].get("port"):
                self.terminals[0]["port"] = ingenico[0]
                self.terminals[0]["enabled"] = True
        elif self.detected_ports:
            self._log(f"Ports found (no Ingenico identified): {', '.join(self.detected_ports)}", "warn")
            for p in self.detected_ports:
                d = self.port_descriptions.get(p, "")
                self._log(f"  {p}: {d or 'Unknown device'}", "info")
            if self.terminals and not self.terminals[0].get("port"):
                self.terminals[0]["port"] = self.detected_ports[0]
        else:
            self._log("No COM ports detected — is terminal in LLT mode + USB?", "warn")
        self._refresh_terms()
        self.status.config(
            text=(f"{len(ingenico)} Ingenico / {len(self.detected_ports)} port(s) detected"
                  if self.detected_ports else "No ports detected"),
            fg=Theme.FG3)

    # ── Files ──────────────────────────────────────────────────────

    def _br_llt(self):
        p = filedialog.askdirectory(title="LLT Install", initialdir=self.llt_path.get())
        if p: self.llt_path.set(os.path.normpath(p))

    # ── Package Folder list ─────────────────────────────────────────

    def _get_pkg_folders(self) -> list[str]:
        """Return all non-empty folder paths from the dynamic folder list."""
        return [sv.get().strip() for sv in self._folder_svars if sv.get().strip()]

    def _first_folder(self) -> str:
        """Return the first valid folder path (used as initialdir fallback)."""
        for f in self._get_pkg_folders():
            if os.path.isdir(f): return f
        return ""

    def _add_pkg_folder(self, path: str = ""):
        """Add one folder row to the Pkg Folders list."""
        sv = tk.StringVar(value=path)
        self._folder_svars.append(sv)
        row = tk.Frame(self.pkg_folder_frame, bg=Theme.BG3, padx=8, pady=5)
        row.pack(fill=tk.X, pady=2)
        row.columnconfigure(1, weight=1)
        tk.Label(row, text="📁", bg=Theme.BG3, fg=Theme.FG2,
                 font=("Segoe UI", 11)).grid(row=0, column=0, padx=(0, 6))
        ttk.Entry(row, textvariable=sv).grid(row=0, column=1, sticky="ew", padx=(0, 6))
        ttk.Button(row, text="Browse",
                   command=lambda v=sv: self._br_pkg_folder(v)).grid(row=0, column=2)
        def _rm(r=row, v=sv):
            if v in self._folder_svars: self._folder_svars.remove(v)
            r.destroy()
            if not self._folder_svars: self._add_pkg_folder("")
        tk.Button(row, text="✕", command=_rm, bg=Theme.BG3, fg=Theme.FG3,
                  activebackground=Theme.BG3, activeforeground=Theme.RED,
                  relief="flat", font=("Segoe UI", 9), cursor="hand2",
                  bd=0).grid(row=0, column=3, padx=(6, 0))
        ttk.Button(row, text="＋", width=3,
                   command=lambda: self._add_pkg_folder("")).grid(row=0, column=4, padx=(6, 0))
        ttk.Button(row, text="⟳", style="Scan.TButton", width=3,
                   command=self._scan_all).grid(row=0, column=5, padx=(2, 0))

    def _br_pkg_folder(self, sv: tk.StringVar):
        p = filedialog.askdirectory(title="Package Folder",
                                    initialdir=sv.get() or self._first_folder() or None)
        if p: sv.set(os.path.normpath(p))

    def _scan_all(self):
        """Scan all listed Package Folders and replace the file list."""
        folders = self._get_pkg_folders()
        if not folders:
            self._log("No Package Folders set — add at least one folder first", "warn"); return
        valid   = [f for f in folders if os.path.isdir(f)]
        invalid = [f for f in folders if not os.path.isdir(f)]
        if invalid:
            self._log(f"Not found: {', '.join(os.path.basename(f) for f in invalid)}", "warn")
        if not valid:
            self._log("No valid folders to scan", "err"); return
        self.saved_names.clear()
        total = 0
        for folder in valid:
            try:
                entries = sorted(os.listdir(folder))
            except OSError as e:
                self._log(f"Cannot read {os.path.basename(folder)}: {e}", "err"); continue
            for fn in entries:
                fp = os.path.join(folder, fn)
                if not os.path.isfile(fp): continue
                ext = os.path.splitext(fn)[1].upper()
                if (ext in ALL_EXT or is_catalogue(ext)) and fp not in self.saved_names:
                    self.saved_names.append(fp); total += 1
        self._rebuild_tree()
        self._log(f"Scanned {len(valid)} folder(s): {total} file(s)", "ok" if total else "warn")

    def _br_xml_dir(self):
        p = filedialog.askdirectory(title="XML Temp Folder", initialdir=self.xml_dir.get() or None)
        if p: self.xml_dir.set(os.path.normpath(p))

    def _br_out_dir(self):
        p = filedialog.askdirectory(title="Output Folder", initialdir=self.out_dir.get() or None)
        if p: self.out_dir.set(os.path.normpath(p))

    def _open_out_dir(self):
        """Open the output folder in the system file explorer."""
        d = self.out_dir.get()
        if not d or not os.path.isdir(d):
            d = tempfile.gettempdir()
        try:
            if platform.system() == "Windows":
                os.startfile(d)
            elif platform.system() == "Darwin":
                subprocess.Popen(["open", d])
            else:
                subprocess.Popen(["xdg-open", d])
        except Exception as e:
            self._log(f"Cannot open folder: {e}", "err")

    def _br_files(self):
        exts = " ".join(f"*{e}" for e in ALL_EXT)
        # Include catalogue wildcard (*.M?? covers .MXX, .M01 … .M99)
        files = filedialog.askopenfilenames(
            title="Select Files", initialdir=self._first_folder() or None,
            filetypes=[("LLT files", f"{exts} *.M?? *.m??"), ("All", "*.*")])
        added = 0
        for fp in files:
            fp = os.path.normpath(fp)
            if fp not in self.saved_names:
                self.saved_names.append(fp); added += 1
        if added:
            self._rebuild_tree(); self._log(f"+ {added} file(s)", "ok")

    def _add_manual(self):
        raw = self.file_entry.get().strip()
        if not raw: return
        # Accept a full path or bare filename (resolved against first pkg folder)
        if os.path.isabs(raw):
            fp = os.path.normpath(raw)
        else:
            folder = self._first_folder()
            if not folder:
                self._log("No Package Folder set — enter a full path or set a folder first.", "err")
                return
            fp = os.path.normpath(os.path.join(folder, raw))
        fn = os.path.basename(fp)
        ext = os.path.splitext(fn)[1].upper()
        if ext not in ALL_EXT and not is_catalogue(ext):
            self._log(f"Unsupported: {ext}", "err"); return
        if fp in self.saved_names:
            self._log(f"Already listed: {fn}", "warn"); return
        self.saved_names.append(fp)
        self._rebuild_tree()
        self.file_entry.delete(0, tk.END)
        self._log(f"+ {fn} → {get_dest(fn, self.range_var.get())}", "ok")

    def _rm_selected(self):
        count = 0
        for item in self.tree.selection():
            fp = self.tree.item(item, "values")[1]  # full path is column index 1
            if fp in self.saved_names: self.saved_names.remove(fp)
            self.tree.delete(item)
            count += 1
        if count:
            self._log(f"Removed {count} file(s)", "info")

    def _clear_files(self):
        count = len(self.saved_names)
        if not count: return
        self.saved_names.clear()
        for item in self.tree.get_children(): self.tree.delete(item)
        self._log(f"Cleared {count} file(s)", "info")

    def _clear_log(self):
        self.log_text.config(state="normal")
        self.log_text.delete("1.0", tk.END)
        self.log_text.config(state="disabled")

    def _rebuild_tree(self):
        """Rebuild treeview from saved_names (full paths) + range."""
        for item in self.tree.get_children(): self.tree.delete(item)
        rng = self.range_var.get()
        for fp in self.saved_names:
            fn = os.path.basename(fp)
            ext = os.path.splitext(fn)[1].upper()
            dest = get_dest(fn, rng)
            ftype = "PKG" if ext in PKG_EXT else ("CAT" if is_catalogue(ext) else "PAR")
            self.tree.insert("", tk.END, values=(fn, fp, dest, ftype))

    def _get_files(self) -> list[dict]:
        """Get file list from treeview as dicts for XML generation."""
        return [{"name": v[0], "path": v[1], "dest": v[2]}
                for item in self.tree.get_children()
                for v in [self.tree.item(item, "values")]]

    # ── Preview / Export ───────────────────────────────────────────

    def _preview(self):
        """Show generated XML for ALL active terminals in a popup."""
        files = self._get_files()
        if not files: self._log("No files", "err"); return
        active = [t for t in self.terminals if t.get("enabled")]
        if not active: self._log("No terminals enabled", "err"); return
        opts = self._opts()
        llt = os.path.normpath(self.llt_path.get())

        win = tk.Toplevel(self.root)
        n = len(active)
        win.title(f"Preview — {n} terminal{'s' if n > 1 else ''}")
        win.geometry("750x600"); win.configure(bg=Theme.BG)
        win.bind("<Escape>", lambda _: win.destroy())
        frm = tk.Frame(win, bg=Theme.BG)
        frm.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        sb_y = ttk.Scrollbar(frm, orient=tk.VERTICAL)
        sb_x = ttk.Scrollbar(frm, orient=tk.HORIZONTAL)
        txt = tk.Text(frm, bg=Theme.INP, fg=Theme.FG, font=Theme.MO,
                      wrap=tk.NONE, relief="flat",
                      yscrollcommand=sb_y.set, xscrollcommand=sb_x.set)
        sb_y.config(command=txt.yview)
        sb_x.config(command=txt.xview)
        sb_y.pack(side=tk.RIGHT, fill=tk.Y)
        sb_x.pack(side=tk.BOTTOM, fill=tk.X)
        txt.pack(fill=tk.BOTH, expand=True)
        txt.bind("<MouseWheel>",
                 lambda e: (txt.yview_scroll(int(-1*(e.delta/120)), "units"), "break")[1])
        txt.bind("<Button-4>", lambda _: (txt.yview_scroll(-3, "units"), "break")[1])
        txt.bind("<Button-5>", lambda _: (txt.yview_scroll(3, "units"), "break")[1])

        for t in active:
            port = t.get("port", "")
            lbl = port or "auto"
            xml = build_xml(files, port, opts)
            bat = build_batch(llt, port, f"load_{lbl}.xml", opts)
            txt.insert(tk.END, f"{'='*60}\n  XML for {lbl}\n{'='*60}\n\n{xml}\n")
            txt.insert(tk.END, f"{'='*60}\n  Batch for {lbl}\n{'='*60}\n\n{bat}\n")

        txt.config(state="disabled")
        btn_frm = ttk.Frame(win); btn_frm.pack(fill=tk.X, padx=10, pady=(0, 10))
        ttk.Button(btn_frm, text="Copy to Clipboard",
                   command=lambda: (win.clipboard_clear(),
                                    win.clipboard_append(txt.get("1.0", tk.END)))
                   ).pack(side=tk.LEFT)
        ttk.Button(btn_frm, text="Close", command=win.destroy).pack(side=tk.RIGHT)

    def _export(self):
        """Export XML + batch scripts to a chosen folder."""
        files = self._get_files()
        if not files: self._log("No files", "err"); return
        missing = [fi["name"] for fi in files if not os.path.isfile(fi["path"])]
        if missing:
            self._log(
                f"Warning: {len(missing)} file(s) not found on disk: "
                f"{', '.join(missing[:3])}{'...' if len(missing) > 3 else ''}",
                "warn")
        active = [t for t in self.terminals if t.get("enabled")]
        if not active:
            self._log("No terminals enabled", "err"); return
        labels = [t.get("port") or "auto" for t in active]
        if len(labels) != len(set(labels)):
            dupes = sorted(set(l for l in labels if labels.count(l) > 1))
            self._log(f"Duplicate ports: {', '.join(dupes)} — each terminal needs a unique port", "err")
            return
        d = filedialog.askdirectory(title="Export To")
        if not d: return
        opts = self._opts()
        exported = []
        for t in active:
            port = t.get("port", "")
            lbl = port or "auto"
            xml_name = f"load_{lbl}.xml"
            xml = build_xml(files, port, opts)
            bat = build_batch(os.path.normpath(self.llt_path.get()), port, xml_name, opts)
            try:
                with open(os.path.join(d, xml_name), "w", encoding="ISO-8859-1") as f:
                    f.write(xml)
                with open(os.path.join(d, f"run_{lbl}.bat"), "w", encoding="utf-8") as f:
                    f.write(bat)
            except Exception as e:
                self._log(f"Export failed for {lbl}: {e}", "err")
                messagebox.showerror("Export Error", f"Could not write files for {lbl}:\n{e}")
                return
            exported.append(lbl)
        self._log(f"Exported for: {', '.join(exported)}", "ok")
        messagebox.showinfo("Exported", f"Saved {len(exported)} script set(s) to:\n{d}")

    # ── PARALLEL LOADING ───────────────────────────────────────────

    def _update_status_cards(self, statuses: dict):
        """
        Refresh per-terminal status cards in the UI.
        statuses: {port_label: {"state": "idle|running|ok|fail", "msg": str}}
        """
        for w in self.status_frame.winfo_children(): w.destroy()
        for lbl, info in statuses.items():
            st = info.get("state", "idle")
            color = {
                "idle": Theme.FG3, "running": Theme.YEL,
                "ok": Theme.GRL, "fail": Theme.RED,
            }.get(st, Theme.FG3)
            icon = {"idle": "○", "running": "◌", "ok": "✓", "fail": "✗"}.get(st, "?")
            card = tk.Frame(self.status_frame, bg=Theme.BG2, highlightbackground=color,
                            highlightthickness=1, padx=8, pady=4)
            card.pack(side=tk.LEFT, padx=(0, 6), pady=2)
            tk.Label(card, text=f"{icon} {lbl}", bg=Theme.BG2, fg=color,
                     font=Theme.FS).pack(side=tk.LEFT)
            if info.get("msg"):
                tk.Label(card, text=f" {info['msg'][:30]}", bg=Theme.BG2,
                         fg=Theme.FG3, font=Theme.FXS).pack(side=tk.LEFT)

    def _run(self):
        """
        Generate & Load — the main action.

        PARALLEL LOADING FLOW:
          1. Get active terminals and file list
          2. Verify cmdLine.bat exists
          3. Launch all terminals in ThreadPoolExecutor (one thread per terminal)
          4. Each thread calls run_terminal() which builds its own XML (port-specific
             <connect device="COMx"/>), writes it to xml_dir, runs cmdLine.bat, then
             deletes the temp XML
          5. Results collected via as_completed() and shown in status cards + log
        """
        if self.is_loading:
            self._log("Already loading", "warn"); return
        files = self._get_files()
        if not files:
            self._log("No files to load", "err"); return
        missing = [fi["name"] for fi in files if not os.path.isfile(fi["path"])]
        if missing:
            self._log(
                f"Warning: {len(missing)} file(s) not found on disk: "
                f"{', '.join(missing[:3])}{'...' if len(missing) > 3 else ''}",
                "warn")
        active = [t for t in self.terminals if t.get("enabled")]
        if not active:
            self._log("No terminals enabled", "err"); return

        # Validate: each terminal must use a unique port label
        labels = [t.get("port") or "auto" for t in active]
        if len(labels) != len(set(labels)):
            dupes = sorted(set(l for l in labels if labels.count(l) > 1))
            self._log(f"Duplicate ports: {', '.join(dupes)} — each terminal needs a unique port", "err")
            return

        llt = os.path.normpath(self.llt_path.get())
        is_win = platform.system() == "Windows"
        cmd_file = "cmdLine.bat" if is_win else "cmdLine.sh"
        cmd_path = os.path.join(llt, cmd_file)
        if not os.path.isfile(cmd_path):
            self._log(f"{cmd_file} not found in: {llt}", "err")
            messagebox.showerror("Error", f"{cmd_file} not found:\n{cmd_path}")
            return

        xml_dir_val = self.xml_dir.get()
        if xml_dir_val and not os.path.isdir(xml_dir_val):
            self._log(f"XML Folder not found: {xml_dir_val} — falling back to system temp", "warn")
        out_dir_val = self.out_dir.get()
        if out_dir_val and not os.path.isdir(out_dir_val):
            self._log(f"Output Folder not found: {out_dir_val} — falling back to system temp", "warn")

        self.is_loading = True
        self.run_btn.config(state="disabled", text="◌  Loading...")
        self.query_btn.config(state="disabled")
        opts = self._opts()
        n = len(active)
        self.status.config(text=f"Loading {n} terminal(s)...", fg=Theme.YEL)
        self._log(f"{'='*50}", "info")
        self._log(f"Starting parallel load: {len(files)} files × {n} terminal(s)", "info")
        self._log(f"{'='*50}", "info")

        # Initialize status cards
        statuses = {}
        for t in active:
            lbl = t.get("port") or "auto"
            statuses[lbl] = {"state": "running", "msg": "Starting..."}
        self._update_status_cards(statuses)

        def _run_all():
            """Background thread: launch all terminals in parallel."""
            try:
                with ThreadPoolExecutor(max_workers=n) as pool:
                    futures = {}
                    for t in active:
                        port = t.get("port", "")
                        fut = pool.submit(
                            run_terminal, llt, port, files, opts,
                            self._log_safe, xml_dir_val
                        )
                        futures[fut] = port or "auto"

                    for fut in as_completed(futures):
                        try:
                            lbl, code, output = fut.result()
                        except Exception as e:
                            lbl = futures[fut]
                            statuses[lbl] = {"state": "fail", "msg": "Internal error"}
                            self._log_safe(f"[{lbl}] ✗ Internal error: {e}", "err")
                            if self._alive:
                                self.root.after(0, lambda s=dict(statuses): self._update_status_cards(s))
                            continue
                        if code == 0:
                            statuses[lbl] = {"state": "ok", "msg": "Success"}
                            self._log_safe(f"[{lbl}] ✓ Loading completed!", "ok")
                            msg = update_terminal_log(opts.get("out_dir", tempfile.gettempdir()), lbl, opts)
                            if msg:
                                tag = "warn" if msg.startswith("Could not") or "not found" in msg or "empty" in msg else "info"
                                self._log_safe(f"  [{lbl}] {msg}", tag)
                        else:
                            err_msg = LLT_ERRORS.get(code, f"Code {code}")
                            statuses[lbl] = {"state": "fail", "msg": err_msg}
                            self._log_safe(f"[{lbl}] ✗ FAILED: {err_msg}", "err")
                            if code in LLT_HINTS:
                                self._log_safe(f"  [{lbl}] Hint: {LLT_HINTS[code]}", "warn")
                        # Show subprocess output (first 8 meaningful lines)
                        if output:
                            for line in output.split("\n")[:8]:
                                line = line.strip()
                                if line:
                                    self._log_safe(f"  [{lbl}] {line}", "info")
                        # Update status cards after each terminal finishes
                        if self._alive:
                            self.root.after(0, lambda s=dict(statuses): self._update_status_cards(s))
            finally:
                # Always reset loading state — even if an unexpected error occurs
                if self._alive:
                    self.root.after(0, lambda: self._finish_loading(statuses))

        threading.Thread(target=_run_all, daemon=True).start()

    def _run_query(self):
        """
        Query Only — connects to each terminal, reads Manufacturing Code,
        updates terminal_log.csv, then disconnects. No files needed.
        """
        if self.is_loading:
            self._log("Already loading", "warn"); return
        if not self.query_info.get():
            self._log("Query info is not enabled — tick 'Query info' in Options first.", "warn")
            return
        active = [t for t in self.terminals if t.get("enabled")]
        if not active:
            self._log("No terminals enabled", "err"); return

        llt = os.path.normpath(self.llt_path.get())
        is_win = platform.system() == "Windows"
        cmd_file = "cmdLine.bat" if is_win else "cmdLine.sh"
        cmd_path = os.path.join(llt, cmd_file)
        if not os.path.isfile(cmd_path):
            self._log(f"{cmd_file} not found in: {llt}", "err")
            messagebox.showerror("Error", f"{cmd_file} not found:\n{cmd_path}")
            return

        # Validate: each terminal must use a unique port label
        labels = [t.get("port") or "auto" for t in active]
        if len(labels) != len(set(labels)):
            dupes = sorted(set(l for l in labels if labels.count(l) > 1))
            self._log(f"Duplicate ports: {', '.join(dupes)} — each terminal needs a unique port", "err")
            return

        xml_dir_val = self.xml_dir.get()
        if xml_dir_val and not os.path.isdir(xml_dir_val):
            self._log(f"XML Folder not found: {xml_dir_val} — falling back to system temp", "warn")
        self.is_loading = True
        self.run_btn.config(state="disabled")
        self.query_btn.config(state="disabled", text="◌  Querying...")
        opts = self._opts()
        n = len(active)
        self.status.config(text=f"Querying {n} terminal(s)...", fg=Theme.YEL)
        self._log(f"{'='*50}", "info")
        self._log(f"Query only: {n} terminal(s) — no files will be loaded", "info")
        self._log(f"{'='*50}", "info")

        statuses = {}
        for t in active:
            lbl = t.get("port") or "auto"
            statuses[lbl] = {"state": "running", "msg": "Querying..."}
        self._update_status_cards(statuses)

        def _query_all():
            try:
                with ThreadPoolExecutor(max_workers=n) as pool:
                    futures = {}
                    for t in active:
                        port = t.get("port", "")
                        fut = pool.submit(
                            run_terminal, llt, port, [], opts,
                            self._log_safe, xml_dir_val
                        )
                        futures[fut] = port or "auto"

                    for fut in as_completed(futures):
                        try:
                            lbl, code, output = fut.result()
                        except Exception as e:
                            lbl = futures[fut]
                            statuses[lbl] = {"state": "fail", "msg": "Internal error"}
                            self._log_safe(f"[{lbl}] ✗ Internal error: {e}", "err")
                            if self._alive:
                                self.root.after(0, lambda s=dict(statuses): self._update_status_cards(s))
                            continue
                        if code == 0:
                            statuses[lbl] = {"state": "ok", "msg": "Queried"}
                            self._log_safe(f"[{lbl}] ✓ Query completed!", "ok")
                            msg = update_terminal_log(opts.get("out_dir", tempfile.gettempdir()), lbl, opts)
                            if msg:
                                tag = "warn" if msg.startswith("Could not") or "not found" in msg or "empty" in msg else "info"
                                self._log_safe(f"  [{lbl}] {msg}", tag)
                        else:
                            err_msg = LLT_ERRORS.get(code, f"Code {code}")
                            statuses[lbl] = {"state": "fail", "msg": err_msg}
                            self._log_safe(f"[{lbl}] ✗ FAILED: {err_msg}", "err")
                            if code in LLT_HINTS:
                                self._log_safe(f"  [{lbl}] Hint: {LLT_HINTS[code]}", "warn")
                        if output:
                            for line in output.split("\n")[:8]:
                                line = line.strip()
                                if line:
                                    self._log_safe(f"  [{lbl}] {line}", "info")
                        if self._alive:
                            self.root.after(0, lambda s=dict(statuses): self._update_status_cards(s))
            finally:
                if self._alive:
                    self.root.after(0, lambda: self._finish_loading(statuses))

        threading.Thread(target=_query_all, daemon=True).start()

    def _finish_loading(self, statuses: dict):
        """Called on main thread when all terminals are done."""
        ok = sum(1 for s in statuses.values() if s["state"] == "ok")
        fail = sum(1 for s in statuses.values() if s["state"] == "fail")
        total = len(statuses)  # use full count — some may still be "running" if _run_all crashed
        self._log(f"{'='*50}", "info")
        self._log(f"Done: {ok}/{total} succeeded"
                  + (f", {fail} failed" if fail else ""), "ok" if ok == total else "err")
        self._log(f"{'='*50}", "info")
        self.status.config(text=f"Done: {ok}/{total} OK", fg=Theme.GRL if ok == total else Theme.RED)
        self.run_btn.config(state="normal", text="▶  Generate & Load")
        self.query_btn.config(state="normal", text="⬡  Query Only")
        self.is_loading = False

    # ── Logging ────────────────────────────────────────────────────

    def _log(self, msg: str, tag: str = "info"):
        """Append timestamped message to log (main thread only)."""
        ts = datetime.now().strftime("%H:%M:%S")
        self.log_text.config(state="normal")
        self.log_text.insert(tk.END, f"[{ts}] {msg}\n", tag)
        if int(self.log_text.index("end-1c").split(".")[0]) > 2000:
            self.log_text.delete("1.0", "2.0")
        self.log_text.see(tk.END)
        self.log_text.config(state="disabled")

    def _log_safe(self, msg: str, tag: str = "info"):
        """Thread-safe logging — schedules _log on the main thread via root.after()."""
        if self._alive:
            self.root.after(0, lambda: self._log(msg, tag))


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

if __name__ == "__main__":
    root = tk.Tk()
    app = LLTApp(root)
    root.mainloop()
