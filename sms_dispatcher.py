#!/usr/bin/env python3
"""SMS Bulk Dispatcher - standalone desktop app. No Telegram, no bot.

Talks straight to your Firebase Realtime Database, finds online Android
devices (clients/<id>/status == true) and writes sendSms commands to them.
Numbers are split round-robin across the devices you pick. Each device
waits until the phone flips isSended=true before moving on.

Stdlib only: tkinter, urllib, csv, json. No pip install needed.
Run:  python sms_dispatcher.py
"""

import csv
import io
import json
import math
import os
import queue
import re
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime

import tkinter as tk
from tkinter import ttk, filedialog, messagebox

APP_DIR = os.path.dirname(os.path.abspath(__file__))
SETTINGS_FILE = os.path.join(APP_DIR, "settings.json")
REPORT_DIR = os.path.join(APP_DIR, "reports")
DEFAULT_FIREBASE_URL = "https://berlinxmirrorfinalboss-default-rtdb.firebaseio.com"

MAX_TARGETS = 10000
CONFIRM_TIMEOUT = 12.0      # seconds to wait for the phone to confirm isSended
POLL_INTERVAL = 0.8
SEND_RETRY_WAIT = 1.5
HTTP_TIMEOUT = 10
MIN_DELAY = 0.5
SMS_CHARS_PER_PART = 160

COUNT_KEYS = ("sent", "unconfirmed", "failed", "skipped")
VAR_RE = re.compile(r"\{(\w+)\}")


# ============================================================
# SETTINGS
# ============================================================

def load_settings():
    s = {"firebase_urls": [DEFAULT_FIREBASE_URL], "sim_slot": 0, "delay": 2.0}
    try:
        with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
            loaded = json.load(f)
        if isinstance(loaded, dict):
            s.update(loaded)
    except (OSError, ValueError):
        pass
    if not isinstance(s.get("firebase_urls"), list):
        s["firebase_urls"] = [DEFAULT_FIREBASE_URL]
    return s


def save_settings(s):
    try:
        with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
            json.dump(s, f, indent=2)
    except OSError:
        pass


# ============================================================
# FIREBASE REST (urllib, no requests)
# ============================================================

class FirebaseError(Exception):
    pass


def normalize_url(raw):
    u = (raw or "").strip().rstrip("/")
    if not u:
        return ""
    if not re.match(r"^https?://", u, re.I):
        u = "https://" + u
    return u


def is_online(value):
    return value is True or str(value).lower() in ("true", "1", "online")


class Firebase:
    def __init__(self, base_url, timeout=HTTP_TIMEOUT):
        self.base = normalize_url(base_url)
        self.timeout = timeout

    def _url(self, path, query=""):
        segs = [urllib.parse.quote(s, safe="") for s in path.split("/") if s]
        if segs:
            url = f"{self.base}/{'/'.join(segs)}.json"
        else:
            url = f"{self.base}/.json"
        if query:
            url += "?" + query
        return url

    def _call(self, method, path, body=None, query=""):
        """Returns (http_status, parsed_json_or_None). Raises FirebaseError on network failure."""
        data = None
        headers = {}
        if body is not None:
            data = json.dumps(body).encode("utf-8")
            headers["Content-Type"] = "application/json"
        req = urllib.request.Request(self._url(path, query), data=data,
                                     method=method, headers=headers)
        try:
            with urllib.request.urlopen(req, timeout=self.timeout) as resp:
                raw = resp.read()
                status = resp.status
        except urllib.error.HTTPError as e:
            return e.code, None
        except (urllib.error.URLError, OSError) as e:
            raise FirebaseError(f"network error: {e}")
        try:
            parsed = json.loads(raw.decode("utf-8")) if raw.strip() else None
        except ValueError:
            parsed = None
        return status, parsed

    def get_clients(self):
        status, data = self._call("GET", "clients")
        if status != 200:
            raise FirebaseError(f"HTTP {status} reading /clients (check URL / DB rules)")
        if isinstance(data, list):
            return {str(i): v for i, v in enumerate(data) if v is not None}
        return data if isinstance(data, dict) else {}

    def send_sms(self, dev_id, to_number, message, sim_slot):
        payload = {
            "from": int(sim_slot),
            "isSended": False,
            "message": message,
            "to": to_number.strip(),
        }
        status, _ = self._call("PUT", f"clients/{dev_id}/webhookEvent/sendSms", body=payload)
        return status == 200

    def get_is_sent(self, dev_id):
        status, data = self._call("GET", f"clients/{dev_id}/webhookEvent/sendSms")
        return (status == 200 and isinstance(data, dict)
                and data.get("isSended") in (True, "true", 1, "1"))


# ============================================================
# DEVICES
# ============================================================

def parse_device(dev_id, data, fb_url):
    sims_raw = data.get("sims")
    if isinstance(sims_raw, dict):
        sims_raw = list(sims_raw.values())
    if not isinstance(sims_raw, list):
        sims_raw = []
    sims = []
    for s in sims_raw:
        if isinstance(s, dict):
            sims.append({
                "slot": str(s.get("simSlotIndex", "0")),
                "carrier": str(s.get("carrierName", "Unknown")),
                "phone": str(s.get("phoneNumber", "Unknown")),
            })
    return {
        "key": f"{fb_url}|{dev_id}",
        "id": dev_id,
        "fb_url": fb_url,
        "fb_name": urllib.parse.urlparse(fb_url).netloc or fb_url,
        "model": str(data.get("modelName", "Unknown Phone")),
        "battery": str(data.get("battery", "N/A")),
        "sims": sims,
    }


def scan_all(urls):
    """Scan every saved Firebase. Never raises; per-URL errors go into stats."""
    devices = {}
    stats = []
    for url in urls:
        try:
            clients = Firebase(url).get_clients()
        except FirebaseError as e:
            stats.append({"url": url, "error": str(e), "total": 0, "online": 0})
            continue
        online = 0
        for dev_id, data in clients.items():
            if not isinstance(data, dict) or not is_online(data.get("status")):
                continue
            dev = parse_device(dev_id, data, normalize_url(url))
            devices[dev["key"]] = dev
            online += 1
        stats.append({"url": url, "error": "", "total": len(clients), "online": online})
    return devices, stats


# ============================================================
# FILE PARSING / TEMPLATES / PHONES
# ============================================================

def sanitize_phone(raw):
    cleaned = re.sub(r"[\s\-\(\)\.]", "", (raw or "").strip())
    if not cleaned:
        return None
    if len(cleaned) == 10 and cleaned.isdigit():
        return f"+91{cleaned}"
    if len(cleaned) == 12 and cleaned.startswith("91") and cleaned.isdigit():
        return f"+{cleaned}"
    if cleaned.startswith("+") and cleaned[1:].isdigit() and len(cleaned) >= 11:
        return cleaned
    if cleaned.isdigit() and len(cleaned) >= 10:
        return f"+{cleaned}"
    return None


def read_text(path):
    with open(path, "rb") as f:
        raw = f.read()
    if raw[:2] in (b"\xff\xfe", b"\xfe\xff"):
        try:
            return raw.decode("utf-16")
        except UnicodeDecodeError:
            pass
    if raw.startswith(b"\xef\xbb\xbf"):
        raw = raw[3:]
    for enc in ("utf-8", "cp1252"):
        try:
            return raw.decode(enc)
        except UnicodeDecodeError:
            continue
    return raw.decode("latin-1")


def parse_content(text):
    """Accepts CSV/TSV/semicolon with a MOBILE header, or a plain one-number-per-line list."""
    res = {"columns": [], "rows": [], "total": 0, "valid": 0,
           "invalid": 0, "duplicate": 0, "error": ""}
    sample = text[:4000]
    if not sample.strip():
        res["error"] = "File is empty."
        return res

    counts = {d: sample.count(d) for d in (",", "\t", ";", "|")}
    delim = max(counts, key=counts.get) if max(counts.values()) > 0 else ","

    first_line = sample.strip().splitlines()[0]
    first_cells = [c.strip().upper() for c in next(csv.reader([first_line], delimiter=delim), [])]

    if "MOBILE" in first_cells:
        reader = csv.DictReader(io.StringIO(text), delimiter=delim)
        res["columns"] = [(c or "").strip().upper() for c in (reader.fieldnames or [])]
        raw_rows = list(reader)
    else:
        if any(re.search(r"[A-Z]", c) for c in first_cells):
            res["error"] = "No MOBILE column found. Add a header named MOBILE, or use one number per line."
            return res
        res["columns"] = ["MOBILE"]
        raw_rows = []
        for line in text.splitlines():
            if line.strip():
                cell = next(csv.reader([line], delimiter=delim), [""])[0]
                raw_rows.append({"MOBILE": cell})

    seen = set()
    for raw in raw_rows:
        res["total"] += 1
        row = {}
        for k, v in raw.items():
            if k is None:
                continue
            row[str(k).strip().upper()] = v.strip() if isinstance(v, str) else ""
        phone = sanitize_phone(row.get("MOBILE", ""))
        if not phone:
            res["invalid"] += 1
            continue
        if phone in seen:
            res["duplicate"] += 1
            continue
        seen.add(phone)
        row["MOBILE"] = phone
        res["rows"].append(row)

    res["valid"] = len(res["rows"])
    return res


def template_vars(tpl):
    return sorted(set(m.upper() for m in VAR_RE.findall(tpl)))


def render(tpl, row):
    def rep(m):
        return row.get(m.group(1).upper(), m.group(0))
    return VAR_RE.sub(rep, tpl)


def fmt_time(seconds):
    seconds = max(0, int(seconds))
    m, s = divmod(seconds, 60)
    h, m = divmod(m, 60)
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m}:{s:02d}"


def write_report(results):
    os.makedirs(REPORT_DIR, exist_ok=True)
    path = os.path.join(REPORT_DIR, f"report_{datetime.now():%Y%m%d_%H%M%S}.csv")
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.writer(f)
        w.writerow(["mobile", "device_id", "firebase", "status", "detail", "time", "message"])
        for r in results:
            w.writerow([r["mobile"], r["device_id"], r["firebase"], r["status"],
                        r["detail"], r["time"], r["message"]])
    return path


# ============================================================
# DISPATCHER (runs in background threads, reports via queue)
# ============================================================

class Dispatcher:
    def __init__(self, jobs, devices, sim_slot, delay, ui_q):
        self.devices = devices
        self.sim_slot = sim_slot
        self.delay = delay
        self.ui_q = ui_q
        self.lock = threading.Lock()
        self.counts = {k: 0 for k in COUNT_KEYS}
        self.results = []
        self.stop_flag = threading.Event()
        self.run_flag = threading.Event()
        self.run_flag.set()
        self.queues = {d["key"]: [] for d in devices}
        for i, job in enumerate(jobs):
            dev = devices[i % len(devices)]
            self.queues[dev["key"]].append(job)
        self.threads = []

    def start(self):
        for dev in self.devices:
            if self.queues[dev["key"]]:
                self.threads.append(threading.Thread(target=self._worker, args=(dev,), daemon=True))
        for t in self.threads:
            t.start()
        threading.Thread(target=self._join_all, daemon=True).start()

    def pause(self):
        self.run_flag.clear()

    def resume(self):
        self.run_flag.set()

    def stop(self):
        self.stop_flag.set()
        self.run_flag.set()

    def snapshot(self):
        with self.lock:
            return dict(self.counts)

    def results_copy(self):
        with self.lock:
            return list(self.results)

    def _join_all(self):
        for t in self.threads:
            t.join()
        self.ui_q.put(("done", None))

    def _gate(self):
        """Block while paused. False when stopped."""
        while not self.stop_flag.is_set():
            if self.run_flag.wait(0.3):
                return True
        return False

    def _sleep(self, sec):
        end = time.time() + sec
        while time.time() < end and not self.stop_flag.is_set():
            time.sleep(min(0.2, end - time.time()))

    def _record(self, dev, job, status, detail):
        with self.lock:
            self.counts[status] += 1
            self.results.append({
                "mobile": job["mobile"],
                "device_id": dev["id"],
                "firebase": dev["fb_url"],
                "status": status,
                "detail": detail,
                "time": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                "message": job["message"],
            })
        self.ui_q.put(("progress", None))

    def _dispatch_one(self, fb, dev, job):
        detail = ""
        for attempt in (1, 2):
            try:
                if fb.send_sms(dev["id"], job["mobile"], job["message"], self.sim_slot):
                    break
                detail = "write_rejected"
            except FirebaseError as e:
                detail = str(e)[:200]
            if attempt == 1:
                self._sleep(SEND_RETRY_WAIT)
        else:
            return "failed", detail

        deadline = time.time() + CONFIRM_TIMEOUT
        while True:
            if self.stop_flag.is_set():
                return "unconfirmed", "stopped_while_waiting"
            try:
                if fb.get_is_sent(dev["id"]):
                    return "sent", "confirmed"
            except FirebaseError:
                pass
            if time.time() >= deadline:
                return "unconfirmed", f"no_confirm_in_{int(CONFIRM_TIMEOUT)}s"
            time.sleep(POLL_INTERVAL)

    def _worker(self, dev):
        fb = Firebase(dev["fb_url"])
        jobs = self.queues[dev["key"]]
        for i, job in enumerate(jobs):
            if not self._gate():
                for rest in jobs[i:]:
                    self._record(dev, rest, "skipped", "campaign_stopped")
                break
            t0 = time.time()
            try:
                status, detail = self._dispatch_one(fb, dev, job)
            except Exception as e:
                status, detail = "failed", f"unexpected: {e}"[:200]
            self._record(dev, job, status, detail)
            self._sleep(self.delay - (time.time() - t0))


# ============================================================
# GUI
# ============================================================

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("SMS Bulk Dispatcher")
        self.geometry("1120x820")
        self.minsize(1000, 720)

        self.settings = load_settings()
        self.devices = {}
        self.rows = []
        self.columns = []
        self.file_name = ""
        self.dispatcher = None
        self.running = False
        self.paused = False
        self.last_results = []
        self.ui_q = queue.Queue()

        self._build_ui()
        self._reload_url_list()
        self.after(120, self._pump)
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    # ---------- layout ----------

    def _build_ui(self):
        fb = ttk.LabelFrame(self, text="1. Firebase databases")
        fb.pack(fill="x", padx=10, pady=(10, 4))
        self.url_list = tk.Listbox(fb, height=3, exportselection=False)
        self.url_list.pack(side="left", fill="both", expand=True, padx=8, pady=6)
        fb_right = ttk.Frame(fb)
        fb_right.pack(side="left", fill="y", padx=8, pady=6)
        self.url_entry = ttk.Entry(fb_right, width=55)
        self.url_entry.pack(fill="x")
        ttk.Button(fb_right, text="Add URL", command=self.add_url).pack(fill="x", pady=2)
        ttk.Button(fb_right, text="Remove selected", command=self.remove_url).pack(fill="x", pady=2)
        ttk.Button(fb_right, text="Scan devices", command=self.scan_devices).pack(fill="x", pady=2)

        dv = ttk.LabelFrame(self, text="2. Online devices (selected = used for sending)")
        dv.pack(fill="x", padx=10, pady=4)
        cols = ("id", "model", "battery", "sims", "firebase")
        heads = {"id": "Device ID", "model": "Model", "battery": "Battery",
                 "sims": "SIM / carrier", "firebase": "Firebase"}
        widths = {"id": 170, "model": 150, "battery": 70, "sims": 390, "firebase": 200}
        self.dev_tree = ttk.Treeview(dv, columns=cols, show="headings",
                                     selectmode="extended", height=6)
        for c in cols:
            self.dev_tree.heading(c, text=heads[c])
            self.dev_tree.column(c, width=widths[c], anchor="w")
        self.dev_tree.pack(side="left", fill="both", expand=True, padx=8, pady=6)
        dv_right = ttk.Frame(dv)
        dv_right.pack(side="left", fill="y", padx=8, pady=6)
        ttk.Button(dv_right, text="Select all",
                   command=lambda: self.dev_tree.selection_set(self.dev_tree.get_children())
                   ).pack(fill="x", pady=2)
        ttk.Button(dv_right, text="Clear selection",
                   command=lambda: self.dev_tree.selection_remove(self.dev_tree.get_children())
                   ).pack(fill="x", pady=2)
        self.dev_info = ttk.Label(dv_right, text="Not scanned yet", wraplength=170, justify="left")
        self.dev_info.pack(pady=6, anchor="w")

        mid = ttk.Frame(self)
        mid.pack(fill="both", expand=True, padx=10, pady=4)

        tplf = ttk.LabelFrame(mid, text="3. Message template  (use {COLUMN}, e.g. {NAME})")
        tplf.pack(side="left", fill="both", expand=True, padx=(0, 5))
        self.tpl_text = tk.Text(tplf, height=8, wrap="word", font=("Consolas", 10), undo=True)
        self.tpl_text.pack(fill="both", expand=True, padx=8, pady=6)
        self.tpl_text.bind("<KeyRelease>", lambda e: self._update_tpl_info())
        self.tpl_text.bind("<<Paste>>", lambda e: self.after(10, self._update_tpl_info))
        self.tpl_info = ttk.Label(tplf, text="0 chars | 0 SMS part(s)")
        self.tpl_info.pack(anchor="w", padx=8, pady=(0, 6))

        dataf = ttk.LabelFrame(mid, text="4. Numbers list (CSV / TXT)")
        dataf.pack(side="left", fill="both", expand=True, padx=(5, 0))
        ttk.Button(dataf, text="Load file...", command=self.load_file).pack(anchor="w", padx=8, pady=6)
        self.data_info = ttk.Label(dataf, text="No file loaded", justify="left")
        self.data_info.pack(anchor="w", padx=8)
        self.preview = tk.Text(dataf, height=7, wrap="word", font=("Consolas", 9), state="disabled")
        self.preview.pack(fill="both", expand=True, padx=8, pady=6)

        ctl = ttk.LabelFrame(self, text="5. Campaign")
        ctl.pack(fill="x", padx=10, pady=4)
        row1 = ttk.Frame(ctl)
        row1.pack(fill="x", padx=8, pady=(6, 2))
        ttk.Label(row1, text="SIM slot:").pack(side="left")
        self.sim_var = tk.StringVar(value=str(self.settings.get("sim_slot", 0)))
        ttk.Combobox(row1, textvariable=self.sim_var, values=["0", "1"], width=4,
                     state="readonly").pack(side="left", padx=(4, 14))
        ttk.Label(row1, text="Delay per SMS (s):").pack(side="left")
        self.delay_var = tk.StringVar(value=str(self.settings.get("delay", 2.0)))
        ttk.Spinbox(row1, from_=MIN_DELAY, to=60, increment=0.5,
                    textvariable=self.delay_var, width=6).pack(side="left", padx=(4, 14))
        self.btn_start = ttk.Button(row1, text="Start", command=self.start_campaign)
        self.btn_pause = ttk.Button(row1, text="Pause", command=self.toggle_pause, state="disabled")
        self.btn_stop = ttk.Button(row1, text="Stop", command=self.stop_campaign, state="disabled")
        self.btn_export = ttk.Button(row1, text="Export last report", command=self.export_last)
        for b in (self.btn_start, self.btn_pause, self.btn_stop, self.btn_export):
            b.pack(side="left", padx=4)

        row2 = ttk.Frame(ctl)
        row2.pack(fill="x", padx=8, pady=2)
        self.progress = ttk.Progressbar(row2, maximum=1, value=0)
        self.progress.pack(fill="x")
        self.status_lbl = ttk.Label(ctl, text="Idle")
        self.status_lbl.pack(anchor="w", padx=8, pady=(2, 6))

        logf = ttk.LabelFrame(self, text="Log")
        logf.pack(fill="x", padx=10, pady=(4, 10))
        self.log_text = tk.Text(logf, height=8, wrap="word", font=("Consolas", 9), state="disabled")
        self.log_text.pack(side="left", fill="both", expand=True, padx=(8, 0), pady=6)
        sb = ttk.Scrollbar(logf, command=self.log_text.yview)
        sb.pack(side="right", fill="y", padx=(0, 8), pady=6)
        self.log_text.configure(yscrollcommand=sb.set)

    # ---------- helpers ----------

    def log(self, msg):
        self.log_text.configure(state="normal")
        self.log_text.insert("end", f"{datetime.now():%H:%M:%S}  {msg}\n")
        self.log_text.see("end")
        self.log_text.configure(state="disabled")

    def _set_preview(self, text):
        self.preview.configure(state="normal")
        self.preview.delete("1.0", "end")
        self.preview.insert("1.0", text)
        self.preview.configure(state="disabled")

    def _tpl(self):
        return self.tpl_text.get("1.0", "end").strip()

    def _bg(self, fn, cb):
        def runner():
            try:
                res, err = fn(), None
            except Exception as e:
                res, err = None, e
            self.ui_q.put(("call", cb, (res, err)))
        threading.Thread(target=runner, daemon=True).start()

    def _pump(self):
        try:
            while True:
                item = self.ui_q.get_nowait()
                kind = item[0]
                try:
                    if kind == "call":
                        item[1](*item[2])
                    elif kind == "progress":
                        self._update_progress()
                    elif kind == "done":
                        self._on_done()
                except Exception as e:
                    self.log(f"UI error: {e}")
        except queue.Empty:
            pass
        self.after(120, self._pump)

    def _set_running_buttons(self, running):
        self.btn_start.configure(state="disabled" if running else "normal")
        self.btn_stop.configure(state="normal" if running else "disabled")
        self.btn_pause.configure(state="normal" if running else "disabled", text="Pause")

    # ---------- firebase list ----------

    def _reload_url_list(self):
        self.url_list.delete(0, "end")
        for u in self.settings["firebase_urls"]:
            self.url_list.insert("end", u)

    def add_url(self):
        url = normalize_url(self.url_entry.get())
        if not url:
            messagebox.showwarning("Firebase", "Enter a Firebase Realtime Database URL.")
            return
        if url in self.settings["firebase_urls"]:
            self.log("That URL is already saved.")
            return
        self.settings["firebase_urls"].append(url)
        save_settings(self.settings)
        self.url_entry.delete(0, "end")
        self._reload_url_list()
        self.log(f"Added {url}")

    def remove_url(self):
        idx = self.url_list.curselection()
        if not idx:
            return
        removed = self.settings["firebase_urls"].pop(idx[0])
        save_settings(self.settings)
        self._reload_url_list()
        self.log(f"Removed {removed}")

    # ---------- scan ----------

    def scan_devices(self):
        if self.running:
            messagebox.showinfo("Busy", "Stop the running campaign first.")
            return
        urls = list(self.settings["firebase_urls"])
        if not urls:
            messagebox.showwarning("Firebase", "Add at least one Firebase URL first.")
            return
        self.dev_info.configure(text="Scanning...")
        self.log(f"Scanning {len(urls)} Firebase database(s)...")
        self._bg(lambda: scan_all(urls), self._on_scan_done)

    def _on_scan_done(self, res, err):
        if err is not None:
            self.log(f"Scan failed: {err}")
            messagebox.showerror("Scan failed", str(err))
            return
        devices, stats = res
        prev = set(self.dev_tree.selection())
        self.devices = devices

        self.dev_tree.delete(*self.dev_tree.get_children())
        for key, d in devices.items():
            sims = " | ".join(
                f"Slot {s['slot']}: {s['carrier']}" + (f" ({s['phone']})" if s['phone'] not in ("Unknown", "") else "")
                for s in d["sims"]
            ) or "No SIM"
            self.dev_tree.insert("", "end", iid=key,
                                 values=(d["id"], d["model"], d["battery"], sims, d["fb_name"]))

        keep = [k for k in prev if k in devices]
        self.dev_tree.selection_set(keep if keep else list(devices.keys()))

        total = sum(s["total"] for s in stats)
        lines = [f"Online: {len(devices)} / Registered: {total}"]
        for s in stats:
            if s["error"]:
                lines.append(f"ERROR {urllib.parse.urlparse(s['url']).netloc}: {s['error']}")
        self.dev_info.configure(text="\n".join(lines))
        self.log(f"Scan done. Online {len(devices)} / registered {total}.")
        for s in stats:
            if s["error"]:
                self.log(f"Scan error [{s['url']}]: {s['error']}")

    # ---------- data file ----------

    def load_file(self):
        if self.running:
            messagebox.showinfo("Busy", "Stop the running campaign first.")
            return
        path = filedialog.askopenfilename(
            title="Pick numbers file",
            filetypes=[("CSV / TXT", "*.csv *.txt *.tsv"), ("All files", "*.*")])
        if not path:
            return
        try:
            text = read_text(path)
        except OSError as e:
            messagebox.showerror("Load failed", str(e))
            return
        res = parse_content(text)
        if res["error"]:
            messagebox.showerror("Load failed", res["error"])
            return
        if not res["rows"]:
            messagebox.showerror("Load failed", "No valid numbers found in this file.")
            return

        self.rows = res["rows"][:MAX_TARGETS]
        self.columns = res["columns"]
        self.file_name = os.path.basename(path)
        capped = f"\nCapped to first {MAX_TARGETS}" if len(res["rows"]) > MAX_TARGETS else ""
        self.data_info.configure(
            text=(f"{self.file_name}\n"
                  f"Rows: {res['total']} | Valid: {res['valid']}\n"
                  f"Invalid: {res['invalid']} | Duplicates: {res['duplicate']}{capped}"))
        self.log(f"Loaded {self.file_name}: {res['valid']} valid, {res['invalid']} invalid, "
                 f"{res['duplicate']} duplicate.")
        self._update_tpl_info()

    # ---------- template ----------

    def _update_tpl_info(self):
        tpl = self._tpl()
        parts = math.ceil(len(tpl) / SMS_CHARS_PER_PART) if tpl else 0
        vars_ = template_vars(tpl)
        txt = f"{len(tpl)} chars | {parts} SMS part(s)"
        if vars_:
            txt += " | vars: " + ", ".join("{" + v + "}" for v in vars_)
        if self.rows and vars_:
            missing = [v for v in vars_ if v not in self.columns]
            if missing:
                txt += "  WARNING not in file: " + ", ".join(missing)
        self.tpl_info.configure(text=txt)
        self._update_preview()

    def _update_preview(self):
        if not self.rows:
            self._set_preview("")
            return
        first = self.rows[0]
        tpl = self._tpl()
        body = render(tpl, first) if tpl else "(write a template)"
        self._set_preview(f"To: {first['MOBILE']}\n\n{body}")

    # ---------- campaign ----------

    def start_campaign(self):
        if self.running:
            return
        sel = list(self.dev_tree.selection())
        devs = [self.devices[k] for k in sel if k in self.devices]
        if not devs:
            messagebox.showwarning("Devices", "Select at least one online device.")
            return
        if not self.rows:
            messagebox.showwarning("Numbers", "Load a numbers file first.")
            return
        tpl = self._tpl()
        if not tpl:
            messagebox.showwarning("Template", "Write the message template first.")
            return
        try:
            sim = int(self.sim_var.get())
            delay = max(MIN_DELAY, float(self.delay_var.get()))
        except ValueError:
            messagebox.showwarning("Settings", "Delay must be a number.")
            return

        jobs = [{"mobile": r["MOBILE"], "message": render(tpl, r)} for r in self.rows]
        per_dev = math.ceil(len(jobs) / len(devs))
        warn = ""
        missing = [v for v in template_vars(tpl) if v not in self.columns]
        if missing:
            warn = f"\nWARNING: {', '.join('{' + m + '}' for m in missing)} not in file, will be sent literally.\n"
        msg = (f"Send {len(jobs)} SMS across {len(devs)} device(s) on SIM slot {sim}.\n"
               f"Each device: ~{per_dev} SMS, {delay:g}s apart.\n"
               f"Minimum time: ~{fmt_time(per_dev * delay)}\n{warn}\nStart now?")
        if not messagebox.askyesno("Confirm campaign", msg):
            return

        self.settings["sim_slot"] = sim
        self.settings["delay"] = delay
        save_settings(self.settings)

        self.dispatcher = Dispatcher(jobs, devs, sim, delay, self.ui_q)
        self.running = True
        self.paused = False
        self.progress.configure(maximum=len(jobs), value=0)
        self._set_running_buttons(True)
        self.log(f"Campaign started: {len(jobs)} SMS, {len(devs)} device(s), SIM {sim}, delay {delay:g}s.")
        self.dispatcher.start()

    def _update_progress(self):
        if not self.dispatcher:
            return
        c = self.dispatcher.snapshot()
        total = self.progress.cget("maximum")
        attempted = c["sent"] + c["unconfirmed"] + c["failed"]
        self.progress.configure(value=attempted)
        remaining = max(0, int(total) - attempted - c["skipped"])
        self.status_lbl.configure(
            text=(f"Confirmed: {c['sent']} | Unconfirmed: {c['unconfirmed']} | "
                  f"Failed: {c['failed']} | Skipped: {c['skipped']} | Remaining: {remaining}"))

    def toggle_pause(self):
        if not self.dispatcher or not self.running:
            return
        if self.paused:
            self.dispatcher.resume()
            self.paused = False
            self.btn_pause.configure(text="Pause")
            self.log("Resumed.")
        else:
            self.dispatcher.pause()
            self.paused = True
            self.btn_pause.configure(text="Resume")
            self.log("Paused.")

    def stop_campaign(self):
        if not self.dispatcher or not self.running:
            return
        if messagebox.askyesno("Stop", "Stop the campaign? Numbers not yet sent will be skipped."):
            self.dispatcher.stop()
            self.log("Stop requested. Waiting for in-flight SMS to finish...")

    def _on_done(self):
        d = self.dispatcher
        if d is None:
            return
        self.running = False
        self.paused = False
        self.last_results = d.results_copy()
        c = d.snapshot()
        self._update_progress()
        state = "STOPPED" if d.stop_flag.is_set() else "COMPLETED"
        summary = (f"Campaign {state}: confirmed {c['sent']}, unconfirmed {c['unconfirmed']}, "
                   f"failed {c['failed']}, skipped {c['skipped']}.")
        self.status_lbl.configure(text=summary)
        self.log(summary)
        self._set_running_buttons(False)
        if self.last_results:
            try:
                path = write_report(self.last_results)
                self.log(f"Report saved: {path}")
            except OSError as e:
                self.log(f"Could not save report: {e}")
        self.dispatcher = None

    def export_last(self):
        if not self.last_results:
            messagebox.showinfo("Export", "No finished campaign to export yet.")
            return
        path = filedialog.asksaveasfilename(
            defaultextension=".csv", initialfile=f"report_{datetime.now():%Y%m%d_%H%M%S}.csv",
            filetypes=[("CSV", "*.csv")])
        if not path:
            return
        try:
            with open(path, "w", newline="", encoding="utf-8-sig") as f:
                w = csv.writer(f)
                w.writerow(["mobile", "device_id", "firebase", "status", "detail", "time", "message"])
                for r in self.last_results:
                    w.writerow([r["mobile"], r["device_id"], r["firebase"], r["status"],
                                r["detail"], r["time"], r["message"]])
            self.log(f"Exported: {path}")
        except OSError as e:
            messagebox.showerror("Export failed", str(e))

    def _on_close(self):
        if self.running and not messagebox.askyesno(
                "Quit", "A campaign is still running. Stop it and quit?"):
            return
        if self.dispatcher:
            self.dispatcher.stop()
        self.destroy()


def main():
    App().mainloop()


if __name__ == "__main__":
    main()
