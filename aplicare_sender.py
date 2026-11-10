# ============================================================
# Aplicare Kamar · MJKN Sender — single-file
# RSUD Bayung Lencir — PySide6 · PyMySQL · requests · DPAPI
# ============================================================
# Ikuti prompt.md (aturan keras, siklus, aturan pencocokan, keamanan)
# dan desain UI "Kirim data" + "Setting".
#
# Perbaikan proses kirim ke MJKN (Aplicare):
#  - Baca MJKN: start dimulai dari 1 (sesuai dokumentasi Aplicare), paging benar.
#  - Pencocokan baris tabel ke ruang MJKN: tepat -> koderuang mirip -> nama ruang
#    (nm_bangsal dari tabel bangsal, seperti di modul SIMRS). Update memakai
#    kodekelas/koderuang/namaruang milik MJKN sendiri. Kecocokan ganda tidak dikirim.
#  - Penilaian sukses: kunci "metadata"/"metaData", kode sukses di bpjs.ok_codes
#    (bawaan "1" dan "200"); respons bukan JSON = gagal.
#  - Retry hanya untuk gangguan jaringan / HTTP 5xx / 429.
#  - Cons ID, Secret Key, User Key, dan Kode PPK diperiksa sebelum kirim.
#  - Header autentikasi disejajarkan dengan BPJSApiAplicare.java milik Khanza.
#  - Log "tidak ditemukan" menyebut daftar ruang MJKN untuk kode kelas yang sama.
# ============================================================

from __future__ import annotations

import base64
import copy
import csv
import ctypes
import datetime as _dt
import hashlib
import hmac
import json
import logging
import os
import re
import sys
import threading
import time
from ctypes import wintypes
from logging.handlers import TimedRotatingFileHandler
from pathlib import Path

from PySide6.QtCore import (QObject, QPoint, QRect, QSharedMemory, QSize, Qt,
                            QTimer, Signal, Slot)
from PySide6.QtGui import (QAction, QColor, QFont, QFontDatabase, QGuiApplication,
                           QIcon, QPainter, QPainterPath, QPen, QPixmap, QTextCursor)
from PySide6.QtWidgets import (
    QAbstractItemView, QApplication, QCheckBox, QDialog, QFileDialog, QFrame, QHBoxLayout,
    QHeaderView, QLabel, QLayout, QLineEdit, QMainWindow, QMenu, QMessageBox,
    QPushButton, QScrollArea, QSizePolicy, QSpinBox, QStackedWidget,
    QSystemTrayIcon, QTableWidget, QTableWidgetItem, QTextEdit, QVBoxLayout,
    QWidget, QGridLayout)

import pymysql
import requests

APP_NAME = "AplicareKamarSender"
APP_TITLE = "Aplicare Kamar · MJKN Sender"
APP_SUB = "RSUD Bayung Lencir"
SK_REF = "SK 185/2025"
ALLOWED_WRITE_TABLE = "aplicare_ketersediaan_kamar"

PAL = {
    "text": "#011F1B", "bg": "#F2FFFC", "primary": "#11F7C9",
    "secondary": "#708CFA", "accent": "#5C43FA",
    "card_border": "#BFE8DF", "muted": "#3B5C56", "input_border": "#86B9AE",
    "console_bg": "#011F1B", "console_fg": "#8FFBE5",
    "danger": "#C0392B", "warn": "#B7791F", "ok": "#0F7B5F",
    "lavender": "#E4E4FF", "lavender_fg": "#2E2A8C", "row_line": "#E3F0EC",
}

# ============================================================
# KONFIGURASI, STATE, RAHASIA, LOG
# ============================================================
_DEFAULT_RULES = [
    {"no": 1,  "match": {"field": "kd_kamar", "startswith": ["C-ICU"]},  "action": "map",
     "target": {"kode_kelas_aplicare": "ICU", "kd_bangsal": "ICU"}, "ref_sk": 6},
    {"no": 2,  "match": {"field": "kd_kamar", "startswith": ["C-NICU"]}, "action": "map",
     "target": {"kode_kelas_aplicare": "NIC", "kd_bangsal": "NICU"}, "ref_sk": 2},
    {"no": 3,  "match": {"field": "kd_kamar", "startswith": ["C-PICU"]}, "action": "map",
     "target": {"kode_kelas_aplicare": "PIC", "kd_bangsal": "PICU"}, "ref_sk": 1},
    {"no": 4,  "match": {"field": "kd_kamar", "startswith": ["C-PERIN"]}, "action": "map",
     "target": {"kode_kelas_aplicare": "VIP", "kd_bangsal": "PERI"}, "ref_sk": 4},
    {"no": 5,  "match": {"field": "kd_kamar", "startswith": ["C-LOTUS", "C-BABY", "C-CHAM-ISO"]},
     "action": "pending_row"},
    {"no": 6,  "match": {"field": "kd_kamar", "startswith": ["C-MIUCO"]}, "action": "pending_row"},
    {"no": 7,  "match": {"field": "kd_kamar", "startswith": ["C-IGD-INT", "C-K000213"]}, "action": "ignore"},
    {"no": 8,  "match": {"field": "kelas", "equals": "Kelas VVIP"}, "action": "map",
     "target": {"kode_kelas_aplicare": "VVP", "kd_bangsal": "VVP"}},
    {"no": 9,  "match": {"field": "kelas", "equals": "Kelas VIP"},  "action": "map",
     "target": {"kode_kelas_aplicare": "VIP", "kd_bangsal": "RVIP"}},
    {"no": 10, "match": {"field": "kelas", "equals": "Kelas 1"},    "action": "map",
     "target": {"kode_kelas_aplicare": "KL1", "kd_bangsal": "KEL-1"}},
    {"no": 11, "match": {"field": "kelas", "equals": "Kelas 2"},    "action": "map",
     "target": {"kode_kelas_aplicare": "KL2", "kd_bangsal": "KEL-2"}},
    {"no": 12, "match": {"field": "kelas", "equals": "Kelas 3"},    "action": "map",
     "target": {"kode_kelas_aplicare": "KL3", "kd_bangsal": "Kel 3"}},
]

_DEFAULTS = {
    # Endpoint dari dokumentasi pihak ketiga: verifikasi ke petunjuk teknis resmi BPJS.
    "bpjs": {"base_url": "https://new-api.bpjs-kesehatan.go.id/aplicaresws",
             "path_read": "/rest/bed/read", "path_create": "/rest/bed/create",
             "path_update": "/rest/bed/update", "path_delete": "/rest/bed/delete",
             "path_ref_kelas": "/rest/ref/kelas",
             "cons_id": "", "secret_key_enc": "", "user_key_enc": "", "kode_ppk": "", "timeout_s": 30,
             "ok_codes": ["1", "200"], "read_start": 1},
    "db": {"host": "127.0.0.1", "port": 3306, "database": "", "username": "", "password_enc": ""},
    "auto": {"enabled": True, "interval_min": 30, "exclude_prefixes": [], "retry": 3,
             "only_if_changed": True, "require_approval_on_kapasitas": True,
             "only_active": True, "merge_dupes": True},
    "ui": {"minimize_to_tray": True},
    "rules": _DEFAULT_RULES,
    "rules_meta": {"ref_sk": SK_REF, "ref_total_tt": 100},
}

_cfg_lock = threading.Lock()
_state_lock = threading.Lock()


def _config_dir() -> Path:
    d = Path(os.environ.get("APPDATA", str(Path.home()))) / "AplicareKamarSender"
    d.mkdir(parents=True, exist_ok=True)
    (d / "logs").mkdir(exist_ok=True)
    return d


def _config_path() -> Path: return _config_dir() / "config.json"
def _default_profile_path() -> Path: return _config_dir() / "config.default.json"
def _state_path() -> Path: return _config_dir() / "state.json"


def _deep_merge(dst, src):
    for k, v in src.items():
        if isinstance(v, dict) and isinstance(dst.get(k), dict):
            _deep_merge(dst[k], v)
        else:
            dst[k] = v


def _atomic_write(path: Path, text: str):
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    os.replace(tmp, path)


def load_cfg() -> dict:
    p = _config_path()
    merged = copy.deepcopy(_DEFAULTS)
    if not p.exists():
        save_cfg(merged)
        return merged
    with _cfg_lock:
        try:
            data = json.loads(p.read_text(encoding="utf-8"))
        except Exception:
            data = {}
    _deep_merge(merged, data)
    return merged


def save_cfg(cfg):
    with _cfg_lock:
        _atomic_write(_config_path(), json.dumps(cfg, ensure_ascii=False, indent=2))


def load_state() -> dict:
    with _state_lock:
        p = _state_path()
        if not p.exists():
            return {}
        try:
            return json.loads(p.read_text(encoding="utf-8"))
        except Exception:
            return {}


def save_state(st):
    with _state_lock:
        _atomic_write(_state_path(), json.dumps(st, ensure_ascii=False, indent=2))


def update_state(**kw):
    st = load_state()
    st.update(kw)
    save_state(st)
    return st


class _DATA_BLOB(ctypes.Structure):
    _fields_ = [("cbData", wintypes.DWORD), ("pbData", ctypes.POINTER(ctypes.c_char))]


def _dpapi_call(data: bytes, protect: bool) -> bytes:
    crypt32 = ctypes.windll.crypt32
    kernel32 = ctypes.windll.kernel32
    buf = ctypes.create_string_buffer(data, len(data))
    blob_in = _DATA_BLOB(len(data), ctypes.cast(buf, ctypes.POINTER(ctypes.c_char)))
    blob_out = _DATA_BLOB()
    fn = crypt32.CryptProtectData if protect else crypt32.CryptUnprotectData
    if not fn(ctypes.byref(blob_in), None, None, None, None, 0, ctypes.byref(blob_out)):
        raise OSError("DPAPI gagal")
    try:
        return ctypes.string_at(blob_out.pbData, blob_out.cbData)
    finally:
        kernel32.LocalFree(blob_out.pbData)


def enc_secret(plain: str) -> str:
    """Rahasia selalu dienkripsi DPAPI di Windows. Tidak ada fallback ke teks biasa di Windows."""
    if not plain:
        return ""
    if sys.platform == "win32":
        return "DPAPI:" + base64.b64encode(_dpapi_call(plain.encode("utf-8"), True)).decode("ascii")
    return "PLAIN:" + base64.b64encode(plain.encode("utf-8")).decode("ascii")  # hanya mode pengembangan non-Windows


def dec_secret(blob: str) -> str:
    if not blob:
        return ""
    if blob.startswith("DPAPI:") and sys.platform == "win32":
        try:
            return _dpapi_call(base64.b64decode(blob[6:]), False).decode("utf-8")
        except Exception:
            return ""
    if blob.startswith("PLAIN:") and sys.platform != "win32":
        return base64.b64decode(blob[6:]).decode("utf-8")
    return ""


_LOGGER = None


def setup_logging():
    global _LOGGER
    if _LOGGER:
        return _LOGGER
    lg = logging.getLogger("aplicare")
    lg.setLevel(logging.INFO)
    lg.propagate = False
    fmt = logging.Formatter("%(asctime)s [%(levelname)s] %(message)s", "%Y-%m-%d %H:%M:%S")
    fh = TimedRotatingFileHandler(_config_dir() / "logs" / "app.log", when="midnight",
                                  backupCount=14, encoding="utf-8")
    fh.setFormatter(fmt)
    lg.addHandler(fh)
    if sys.stderr is not None:  # mode --windowed PyInstaller: stderr bisa None
        sh = logging.StreamHandler()
        sh.setFormatter(fmt)
        lg.addHandler(sh)
    _LOGGER = lg
    return lg


def log_file(level: str, msg: str):
    """Log ke berkas. Pemanggil bertanggung jawab agar msg tidak memuat rahasia."""
    lg = _LOGGER or setup_logging()
    lg.log({"PERINGATAN": logging.WARNING, "KESALAHAN": logging.ERROR}.get(level, logging.INFO), msg)


def _now_str() -> str:
    return _dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")


# ============================================================
# CORE: normalisasi, aturan, hitung, rencana (tanpa I/O)
# ============================================================
_WS = re.compile(r"\s+")


def normalize_kd_kamar(s) -> str:
    return _WS.sub("", str(s or "")).upper()


def _is_active(r) -> bool:
    try:
        return int(r.get("statusdata") or 0) == 1
    except (TypeError, ValueError):
        return False


def _is_kosong(r) -> bool:
    return str(r.get("status") or "").strip().upper() == "KOSONG"


def match_rule(kamar, rules):
    key = normalize_kd_kamar(kamar.get("kd_kamar", ""))
    for r in rules:
        m = r.get("match", {})
        if m.get("field") == "kd_kamar":
            for pref in m.get("startswith", []) or []:
                p = normalize_kd_kamar(pref)
                if p and key.startswith(p):
                    return r
        elif m.get("field") == "kelas" and kamar.get("kelas") == m.get("equals"):
            return r
    return None


def rule_target_key(rule):
    t = rule.get("target") or {}
    return (t.get("kode_kelas_aplicare"), t.get("kd_bangsal"))


def rule_label(rule) -> str:
    m = rule.get("match", {})
    if m.get("field") == "kd_kamar":
        return ", ".join(m.get("startswith", []) or [])
    return m.get("equals", "") or ""


def dedupe(rows):
    """Gabungkan kd_kamar ganda (normalisasi). Duplikat berstatus beda dihitung ISI (konservatif)."""
    groups = {}
    for r in rows:
        groups.setdefault(normalize_kd_kamar(r.get("kd_kamar", "")), []).append(r)
    merged, dupes, conflicts = [], [], []
    for key, items in groups.items():
        base = dict(items[0])
        base["_key"] = key
        if len(items) > 1:
            dupes.append(key)
            if len({_is_kosong(i) for i in items}) > 1:
                conflicts.append(key)
        base["status"] = "KOSONG" if all(_is_kosong(i) for i in items) else "ISI"
        merged.append(base)
    return merged, dupes, conflicts


def count_kamar(rows, rules, only_active=True, merge_dupes=True, exclude=()):
    rows = [dict(r) for r in rows]
    if only_active:
        rows = [r for r in rows if _is_active(r)]
    raw_total = len(rows)
    if merge_dupes:
        rows, dupes, conflicts = dedupe(rows)
    else:
        dupes, conflicts = [], []
        for r in rows:
            r["_key"] = normalize_kd_kamar(r.get("kd_kamar", ""))
    excl = [normalize_kd_kamar(x) for x in (exclude or []) if str(x).strip()]
    targets, pending, ignored, unmatched, ignored_labels = {}, {}, [], [], []

    def add(bucket, key, r, extra=None):
        e = bucket.setdefault(key, {"kapasitas": 0, "tersedia": 0, "kamar": [], "kosong": [], **(extra or {})})
        e["kapasitas"] += 1
        e["kamar"].append(r.get("kd_kamar", ""))
        if _is_kosong(r):
            e["tersedia"] += 1
            e["kosong"].append(r.get("kd_kamar", ""))

    for r in rows:
        if excl and any(r["_key"].startswith(x) for x in excl):
            ignored.append(r.get("kd_kamar", ""))
            continue
        rule = match_rule(r, rules)
        if not rule:
            unmatched.append(r.get("kd_kamar", ""))
            continue
        action = rule.get("action")
        if action == "map":
            add(targets, rule_target_key(rule), r)
        elif action == "pending_row":
            add(pending, rule.get("no"), r, {"label": rule_label(rule),
                                              "tokens": list(rule["match"].get("startswith", []) or [rule_label(rule)])})
        else:
            ignored.append(r.get("kd_kamar", ""))
            lab = rule_label(rule)
            if lab and lab not in ignored_labels:
                ignored_labels.append(lab)
    return {
        "targets": targets, "pending": pending, "ignored": ignored, "ignored_labels": ignored_labels,
        "unmatched": unmatched, "duplicates": dupes, "conflicts": conflicts,
        "raw_total": raw_total, "merged_n": raw_total - len(rows), "total": len(rows),
        "total_map": sum(v["kapasitas"] for v in targets.values()),
        "total_map_kosong": sum(v["tersedia"] for v in targets.values()),
        "total_pending": sum(v["kapasitas"] for v in pending.values()),
        "total_pending_kosong": sum(v["tersedia"] for v in pending.values()),
    }


def valid_row(kap, ter) -> bool:
    return 0 <= ter <= kap


class CycleError(Exception):
    pass


def build_plan(apl_rows, counting, valid_codes=None):
    """Rencana per baris tabel aplicare. aksi: update | tetap | tidak_valid | tanpa_baris."""
    plan, seen = [], set()
    targets = counting["targets"]
    for r in apl_rows:
        kode = r.get("kode_kelas_aplicare") or ""
        kb = r.get("kd_bangsal") or ""
        reason = None
        if not kb:
            reason = "nama kamar kosong"
        elif not kode:
            reason = "kode kelas kosong"
        elif valid_codes and kode not in valid_codes:
            reason = "kode kelas tidak dikenal di MJKN"
        new = targets.get((kode, kb))
        lama_k, lama_t = int(r.get("kapasitas") or 0), int(r.get("tersedia") or 0)
        entry = {"kode_kelas_aplicare": kode, "kd_bangsal": kb, "kelas": r.get("kelas") or "",
                 "nm_bangsal": r.get("nm_bangsal") or "",
                 "kapasitas_lama": lama_k, "tersedia_lama": lama_t,
                 "pria_lama": r.get("tersediapria"), "wanita_lama": r.get("tersediawanita"),
                 "campur_lama": r.get("tersediapriawanita"),
                 "kapasitas": int(new["kapasitas"]) if new else lama_k,
                 "tersedia": int(new["tersedia"]) if new else lama_t,
                 "kosong": list(new["kosong"]) if new else [],
                 "aksi": None, "invalid_reason": reason}
        if reason:
            entry["aksi"] = "tidak_valid"
        elif new is None:
            entry["aksi"] = "tetap"
        else:
            seen.add((kode, kb))
            if not valid_row(entry["kapasitas"], entry["tersedia"]):
                entry["aksi"] = "tidak_valid"
                entry["invalid_reason"] = "tersedia melebihi kapasitas"
            elif entry["kapasitas"] == lama_k and entry["tersedia"] == lama_t:
                entry["aksi"] = "tetap"
            else:
                entry["aksi"] = "update"
        plan.append(entry)
    for k, v in targets.items():  # hasil hitung tanpa baris di tabel: hanya info, tidak dibuat otomatis
        if k not in seen:
            plan.append({"kode_kelas_aplicare": k[0], "kd_bangsal": k[1], "kelas": "",
                         "kapasitas_lama": 0, "tersedia_lama": 0, "pria_lama": None,
                         "wanita_lama": None, "campur_lama": None,
                         "kapasitas": int(v["kapasitas"]), "tersedia": int(v["tersedia"]),
                         "kosong": list(v["kosong"]), "aksi": "tanpa_baris", "invalid_reason": None})
    return plan


def dry_run(cfg, kamar_rows, apl_rows, valid_codes=None):
    auto = cfg["auto"]
    cnt = count_kamar(kamar_rows, cfg["rules"], only_active=auto["only_active"],
                      merge_dupes=auto["merge_dupes"], exclude=auto.get("exclude_prefixes"))
    if cnt["total"] == 0:
        raise CycleError("Tidak ada kamar aktif yang dibaca.")
    if len(cnt["unmatched"]) / cnt["total"] > 0.30:
        raise CycleError(f"{len(cnt['unmatched'])}/{cnt['total']} kamar aktif tidak cocok aturan (>30%).")
    if cnt["total_map"] + cnt["total_pending"] == 0:
        raise CycleError("Hasil hitung 0 kamar; siklus dihentikan.")
    return cnt, build_plan(apl_rows, cnt, valid_codes)


def needs_approval(p, cfg) -> bool:
    return bool(cfg["auto"].get("require_approval_on_kapasitas", True)
                and p["aksi"] == "update" and p["kapasitas"] != p["kapasitas_lama"])


def _valid_codes(state):
    """Kode kelas valid = referensi kelas MJKN (bila sudah dibaca). Entri MJKN bukan acuan validitas."""
    codes = {x.get("kodekelas") for x in state.get("ref_kelas", []) if x.get("kodekelas")}
    return codes or None


# ---------- Pencocokan baris tabel -> ruang MJKN ----------
def _nk(s) -> str:
    """Kunci longgar: huruf kecil, hanya huruf/angka ('Kel 3' == 'KEL-3')."""
    return re.sub(r"[^0-9a-z]+", "", str(s or "").casefold())


def match_mjkn(rows, mjkn):
    """Cocokkan tiap baris tabel ke satu ruang MJKN.
    Urutan: (1) kodekelas+koderuang persis, (2) kodekelas sama + koderuang mirip,
    (3) kodekelas sama + namaruang MJKN = nm_bangsal tabel. Tahap 2-3 hanya dipakai
    bila hasilnya tepat satu ruang yang belum terpakai. Satu ruang MJKN hanya untuk satu baris.
    Return {(kode, kd_bangsal): {"entry", "how", "cands", "hits"}}."""
    mjkn = list(mjkn or [])
    res, used, rest = {}, set(), []
    exact = {}
    for i, m in enumerate(mjkn):
        exact.setdefault((m.get("kodekelas"), m.get("koderuang")), i)
    for r in rows:
        key = (r.get("kode_kelas_aplicare"), r.get("kd_bangsal"))
        i = exact.get(key)
        if i is not None and i not in used:
            used.add(i)
            res[key] = {"entry": mjkn[i], "how": "tepat", "cands": [], "hits": []}
        else:
            rest.append(r)
    for r in rest:
        key = (r.get("kode_kelas_aplicare"), r.get("kd_bangsal"))
        kode = _nk(r.get("kode_kelas_aplicare"))
        cands = [m for m in mjkn if kode and _nk(m.get("kodekelas")) == kode]
        free = [(i, m) for i, m in enumerate(mjkn) if i not in used and kode and _nk(m.get("kodekelas")) == kode]
        nm_ruang, nm_tabel = _nk(r.get("kd_bangsal")), _nk(r.get("nm_bangsal"))
        hits, how = [], "tidak ada"
        if nm_ruang:
            hits = [(i, m) for i, m in free if _nk(m.get("koderuang")) == nm_ruang]
            how = "koderuang mirip"
        if not hits and nm_tabel:
            hits = [(i, m) for i, m in free if _nk(m.get("namaruang")) == nm_tabel]
            how = "nama ruang"
        if len(hits) == 1:
            used.add(hits[0][0])
            res[key] = {"entry": hits[0][1], "how": how, "cands": cands, "hits": []}
        else:
            res[key] = {"entry": None, "how": "ambigu" if hits else "tidak ada", "cands": cands,
                        "hits": [m for _, m in hits]}
    return res


def _ruang_txt(m) -> str:
    nm = m.get("namaruang")
    return f"{m.get('koderuang')}" + (f" [{nm}]" if nm and nm != m.get("koderuang") else "")


def _notfound_text(key, mt, mjkn) -> str:
    kode, nama = key
    if mt["how"] == "ambigu":
        return (f"{nama} ({kode}): cocok dengan lebih dari satu ruang di MJKN ("
                + ", ".join(_ruang_txt(m) for m in mt["hits"][:8]) + "); tidak dikirim. Samakan nama di tabel.")
    if mt["cands"]:
        return (f"{nama}: tidak ditemukan di MJKN (kode kelas {kode}). Ruang {kode} di MJKN: "
                + ", ".join(_ruang_txt(m) for m in mt["cands"][:10]) + ". Tidak dibuat otomatis.")
    kodes = sorted({str(m.get("kodekelas")) for m in mjkn if m.get("kodekelas")})
    return (f"{nama}: tidak ditemukan di MJKN; MJKN tidak punya ruang berkode kelas {kode} "
            f"(kode yang ada: {', '.join(kodes) or '-'}). Tidak dibuat otomatis.")


# ---------- Temuan (dinamis, dihitung dari data) ----------
def _join_id(items):
    items = list(items)
    if len(items) <= 1:
        return "".join(items)
    if len(items) == 2:
        return f"{items[0]} dan {items[1]}"
    return ", ".join(items[:-1]) + f", dan {items[-1]}"


def compute_findings(plan, cnt, mjkn, cfg):
    out = []
    valid = [p for p in plan if p["aksi"] in ("update", "tetap")]
    same = [p["kd_bangsal"] for p in valid if p["aksi"] == "tetap" and p["kd_bangsal"] in
            {t[1] for t in cnt["targets"]}]
    groups = {}
    for p in valid:
        if p["aksi"] == "update":
            groups.setdefault((p["kapasitas_lama"], p["tersedia_lama"]), []).append(p["kd_bangsal"])
    if groups:
        parts = [(f"{', '.join(n)} sama-sama {k} / {t}" if len(n) > 1 else f"{n[0]} masih {k} / {t}")
                 for (k, t), n in groups.items()]
        pre = (f"Hanya {_join_id(same)} angkanya sama dengan hasil hitung. " if same else "")
        out.append(("Diisi manual", pre + ", ".join(parts) + "."))
    else:
        out.append(("Diisi manual", "Semua angka di tabel sudah sama dengan hasil hitung."))

    if mjkn is None:
        out.append(("Tidak ikut update", "Belum dibaca dari MJKN. Isi kredensial di Setting lalu jalankan siklus."))
    else:
        rows_all = [p for p in plan if p["aksi"] != "tanpa_baris"]
        mm = match_mjkn(rows_all, mjkn)
        by_entry = {}
        for p in valid:
            mt = mm.get((p["kode_kelas_aplicare"], p["kd_bangsal"]))
            if mt and mt["entry"] is not None:
                by_entry[id(mt["entry"])] = p
        taken = {id(v["entry"]) for v in mm.values() if v["entry"] is not None}
        miss = [m for m in mjkn if id(m) not in taken]
        kap_tot = ter_tot = 0
        for m in mjkn:
            p = by_entry.get(id(m))
            kap_tot += p["kapasitas"] if p else int(m.get("kapasitas") or 0)
            ter_tot += p["tersedia"] if p else int(m.get("tersedia") or 0)
        if miss:
            names = [str(m.get("namaruang") or m.get("koderuang") or "") for m in miss]
            kap = sum(int(m.get("kapasitas") or 0) for m in miss)
            out.append(("Tidak ikut update",
                        f"{', '.join(names)} ada di MJKN tetapi tidak ada di tabel ini ({kap} tempat tidur). "
                        f"Setelah baris di atas diupdate, MJKN masih menampilkan {kap_tot} / {ter_tot}."))
        else:
            out.append(("Tidak ikut update", "Semua entri MJKN ada di tabel."))
        nf = [p["kd_bangsal"] for p in valid
              if (mm.get((p["kode_kelas_aplicare"], p["kd_bangsal"])) or {}).get("entry") is None]
        if nf:
            out.append(("Tidak di MJKN", f"{', '.join(nf)}: baris tabel tidak ditemukan di MJKN. "
                                         "Tidak dikirim dan tidak dibuat otomatis."))

    pend_parts = []
    for v in cnt["pending"].values():
        toks = [t.rstrip("*") for t in v.get("tokens", [])]
        pend_parts.append(f"{_join_id(toks)} ({v['kapasitas']})")
    for p in plan:
        if p["aksi"] == "tanpa_baris":
            pend_parts.append(f"{p['kd_bangsal']} ({p['kapasitas']}, tujuan belum ada di tabel)")
    n_pend = cnt["total_pending"]
    out.append(("Belum ada baris",
                f"{n_pend} kamar belum punya baris di tabel: " + " serta ".join(pend_parts) + "."
                if pend_parts else "Semua kamar yang dihitung sudah punya baris di tabel."))

    inv = [p for p in plan if p["aksi"] == "tidak_valid"]
    if inv:
        txt = " ".join(
            f"Baris kode “{p['kode_kelas_aplicare']}” (nama kamar {p['kd_bangsal'] or 'kosong'}, "
            f"{p['kelas'] or '-'}, {p['kapasitas_lama']} / {p['tersedia_lama']}) tidak valid: "
            f"{p['invalid_reason']}. Tidak dikirim; hapus manual." for p in inv)
        out.append(("Baris tidak valid", txt))
    else:
        out.append(("Baris tidak valid", "Tidak ada."))

    ign = len(cnt["ignored"])
    lab = f" ({', '.join(cnt['ignored_labels'])})" if cnt["ignored_labels"] else ""
    dup = (f" {len(cnt['duplicates'])} kd_kamar ganda digabung ({cnt['raw_total']} baris menjadi {cnt['total']} kamar)."
           if cnt["duplicates"] else "")
    out.append(("Tidak dihitung", f"{ign} kamar{lab} tidak dihitung.{dup}"))

    if cnt["unmatched"]:
        shown = ", ".join(cnt["unmatched"][:8]) + (" …" if len(cnt["unmatched"]) > 8 else "")
        out.append(("Tidak cocok aturan", f"{len(cnt['unmatched'])} kamar tidak cocok aturan mana pun: {shown}."))
    waiting = [p for p in plan if needs_approval(p, cfg)]
    if waiting:
        out.append(("Perlu persetujuan",
                    f"{len(waiting)} perubahan kapasitas menunggu tombol Kirim terpilih: " +
                    ", ".join(f"{p['kd_bangsal']} {p['kapasitas_lama']}→{p['kapasitas']}" for p in waiting) + "."))
    return out


# ============================================================
# DATA: akses database dengan penjaga baca-saja
# ============================================================
_WRITE_PATTERNS = [
    re.compile(r"^\s*INSERT\s+(?:IGNORE\s+)?(?:INTO\s+)?([`\w.]+)", re.I),
    re.compile(r"^\s*REPLACE\s+(?:INTO\s+)?([`\w.]+)", re.I),
    re.compile(r"^\s*UPDATE\s+(?:LOW_PRIORITY\s+|IGNORE\s+)*([`\w.]+)", re.I),
    re.compile(r"^\s*DELETE\s+(?:LOW_PRIORITY\s+|QUICK\s+|IGNORE\s+)*FROM\s+([`\w.]+)", re.I),
]
_DENY_RE = re.compile(r"^\s*(ALTER|CREATE|DROP|TRUNCATE|GRANT|REVOKE|RENAME|LOCK|SET|CALL|LOAD|HANDLER)\b", re.I)
_SELECT_RE = re.compile(r"^\s*(SELECT|SHOW|DESCRIBE|DESC|EXPLAIN)\b", re.I)


class ReadOnlyGuard(Exception):
    pass


def _strip_comments(sql):
    sql = re.sub(r"/\*.*?\*/", " ", sql, flags=re.S)
    return re.sub(r"--[^\n]*|#[^\n]*", " ", sql)


def _bare_table(tok: str) -> str:
    return tok.replace("`", "").split(".")[-1].lower()


def assert_safe(sql, allow_writes=False):
    s = _strip_comments(sql).strip().rstrip(";").strip()
    if not s:
        raise ReadOnlyGuard("SQL kosong")
    if ";" in s:
        raise ReadOnlyGuard("Beberapa pernyataan sekaligus ditolak")
    if _DENY_RE.match(s):
        raise ReadOnlyGuard("Pernyataan ditolak: " + s.split()[0].upper())
    if _SELECT_RE.match(s):
        if re.search(r"\bINTO\s+(OUTFILE|DUMPFILE)\b", s, re.I):
            raise ReadOnlyGuard("SELECT ... INTO OUTFILE ditolak")
        return
    for pat in _WRITE_PATTERNS:
        m = pat.match(s)
        if m:
            if not allow_writes:
                raise ReadOnlyGuard("Penulisan ditolak pada koneksi pembaca.")
            if _bare_table(m.group(1)) != ALLOWED_WRITE_TABLE:
                raise ReadOnlyGuard("Penulisan hanya diizinkan di tabel " + ALLOWED_WRITE_TABLE)
            if re.search(r"\bJOIN\b", s, re.I):
                raise ReadOnlyGuard("Penulisan dengan JOIN ditolak")
            return
    raise ReadOnlyGuard("SQL tidak dikenali: " + s.split()[0])


def db_connect(cfg_db, read_only=True):
    conn = pymysql.connect(host=cfg_db.get("host", "127.0.0.1"), port=int(cfg_db.get("port") or 3306),
                           user=cfg_db.get("username", ""), password=cfg_db.get("password", ""),
                           database=cfg_db.get("database", ""), charset="utf8mb4", autocommit=False,
                           connect_timeout=8, read_timeout=30, write_timeout=30,
                           cursorclass=pymysql.cursors.DictCursor)
    if read_only:
        with conn.cursor() as cur:
            cur.execute("SET SESSION TRANSACTION READ ONLY")
    return conn


def db_fetch(cfg_db, sql, params=None, read_only=True):
    assert_safe(sql, allow_writes=not read_only)
    conn = db_connect(cfg_db, read_only=read_only)
    try:
        with conn.cursor() as cur:
            cur.execute(sql, params or ())
            return cur.fetchall()
    finally:
        try:
            conn.rollback()
        finally:
            conn.close()


_WRITE_PRIVS = re.compile(r"\b(ALL PRIVILEGES|INSERT|UPDATE|DELETE|ALTER|CREATE|DROP)\b", re.I)
_STRUCT_PRIVS = re.compile(r"\b(ALL PRIVILEGES|ALTER|CREATE|DROP)\b", re.I)


def db_check_grants(cfg_db):
    return [list(r.values())[0] for r in db_fetch(cfg_db, "SHOW GRANTS FOR CURRENT_USER()")]


def grant_warnings(grants):
    """Hak tulis di luar tabel yang diizinkan (INSERT/UPDATE/DELETE hanya di aplicare_ketersediaan_kamar)."""
    out = []
    for g in grants:
        m = re.match(r"GRANT\s+(.+?)\s+ON\s+(.+?)\s+TO\s", g, re.I | re.S)
        if not m:
            continue
        privs, obj = m.group(1), m.group(2).replace("`", "")
        if not _WRITE_PRIVS.search(privs):
            continue
        on_allowed = obj.lower().endswith("." + ALLOWED_WRITE_TABLE)
        if on_allowed and not _STRUCT_PRIVS.search(privs):
            continue
        out.append(g)
    return out


def db_describe_aplicare(cfg_db):
    return db_fetch(cfg_db, f"DESCRIBE {ALLOWED_WRITE_TABLE}")


def db_read_kamar(cfg_db):
    return db_fetch(cfg_db, "SELECT kd_kamar, kd_bangsal, trf_kamar, status, kelas, statusdata FROM kamar")


_APL_JOIN_OK = None  # None = belum dicoba, False = tabel bangsal tidak bisa dipakai


def db_read_aplicare(cfg_db):
    """Baca tabel aplicare + nm_bangsal dari tabel bangsal (seperti modul SIMRS).
    Bila tabel bangsal tidak ada/tidak boleh dibaca, jatuh ke pembacaan tanpa nm_bangsal."""
    global _APL_JOIN_OK
    if _APL_JOIN_OK is not False:
        try:
            rows = db_fetch(cfg_db, "SELECT a.kode_kelas_aplicare, a.kd_bangsal, b.nm_bangsal, a.kelas, "
                                    "a.kapasitas, a.tersedia, a.tersediapria, a.tersediawanita, "
                                    "a.tersediapriawanita "
                                    f"FROM {ALLOWED_WRITE_TABLE} a LEFT JOIN bangsal b ON b.kd_bangsal = a.kd_bangsal")
            _APL_JOIN_OK = True
            return rows
        except pymysql.MySQLError as e:
            if not e.args or e.args[0] not in (1146, 1054, 1142, 1143):
                raise
            _APL_JOIN_OK = False
    return db_fetch(cfg_db, "SELECT kode_kelas_aplicare, kd_bangsal, kelas, kapasitas, tersedia, "
                            "tersediapria, tersediawanita, tersediapriawanita "
                            f"FROM {ALLOWED_WRITE_TABLE}")


def db_update_aplicare(cfg_db, updates):
    """Satu transaksi (all-or-nothing). tersediapria/wanita/priawanita = tersedia."""
    if not updates:
        return 0
    sql = (f"UPDATE {ALLOWED_WRITE_TABLE} SET kapasitas=%s, tersedia=%s, tersediapria=%s, "
           "tersediawanita=%s, tersediapriawanita=%s WHERE kode_kelas_aplicare=%s AND kd_bangsal=%s")
    assert_safe(sql, allow_writes=True)
    conn = db_connect(cfg_db, read_only=False)
    try:
        with conn.cursor() as cur:
            for u in updates:
                cur.execute(sql, (u["kapasitas"], u["tersedia"], u["tersedia"], u["tersedia"],
                                  u["tersedia"], u["kode_kelas_aplicare"], u["kd_bangsal"]))
        conn.commit()
        return len(updates)
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def db_insert_aplicare(cfg_db, rows):
    """Tambah baris baru ke aplicare_ketersediaan_kamar (aksi manual berkonfirmasi).
    rows: list of dict {kode_kelas_aplicare, kd_bangsal, kelas, kapasitas, tersedia}."""
    if not rows:
        return 0
    sql = (f"INSERT INTO {ALLOWED_WRITE_TABLE} (kode_kelas_aplicare, kd_bangsal, kelas, kapasitas, "
           "tersedia, tersediapria, tersediawanita, tersediapriawanita) "
           "VALUES (%s, %s, %s, %s, %s, %s, %s, %s)")
    assert_safe(sql, allow_writes=True)
    conn = db_connect(cfg_db, read_only=False)
    try:
        with conn.cursor() as cur:
            for r in rows:
                t = int(r["tersedia"])
                cur.execute(sql, (r["kode_kelas_aplicare"], r["kd_bangsal"], r.get("kelas") or "",
                                  int(r["kapasitas"]), t, t, t, t))
        conn.commit()
        return len(rows)
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def db_delete_aplicare(cfg_db, keys):
    """Hapus baris dari aplicare_ketersediaan_kamar (aksi manual berkonfirmasi).
    keys: list of tuple (kode_kelas_aplicare, kd_bangsal)."""
    if not keys:
        return 0
    sql = (f"DELETE FROM {ALLOWED_WRITE_TABLE} "
           "WHERE kode_kelas_aplicare=%s AND kd_bangsal=%s")
    sql_null = (f"DELETE FROM {ALLOWED_WRITE_TABLE} "
                "WHERE kode_kelas_aplicare=%s AND (kd_bangsal=%s OR kd_bangsal IS NULL)")
    assert_safe(sql, allow_writes=True)
    conn = db_connect(cfg_db, read_only=False)
    try:
        with conn.cursor() as cur:
            for k in keys:
                kode, kb = k[0], k[1] or ""
                if kb == "":
                    cur.execute(sql_null, (kode, kb))
                else:
                    cur.execute(sql, (kode, kb))
        conn.commit()
        return len(keys)
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def _db_cfg(cfg):
    d = dict(cfg["db"])
    d["password"] = dec_secret(cfg["db"].get("password_enc", ""))
    return d


# ============================================================
# BPJS Aplicare (semua endpoint/field = konfigurasi)
# ============================================================
class BpjsClient:
    def __init__(self, bp, mock=False):
        self.base = str(bp.get("base_url", "")).strip().rstrip("/")
        # Buang spasi/newline tidak sengaja saat kredensial disalin dari portal BPJS.
        self.cons_id = str(bp.get("cons_id", "")).strip()
        self.secret = dec_secret(bp.get("secret_key_enc", "")).strip()
        self.user_key = dec_secret(bp.get("user_key_enc", "")).strip()
        self.kode_ppk = str(bp.get("kode_ppk", "")).strip()
        self.paths = bp
        self.timeout = int(bp.get("timeout_s", 30))
        self.ok_codes = {str(x).strip() for x in (bp.get("ok_codes") or ["1", "200"])}
        self.read_start = int(bp.get("read_start", 1))  # Aplicare: baris pertama = 1
        self.last_raw = ""  # ringkasan balasan baca MJKN bila daftar ruang kosong (untuk diagnosis)
        self.mock = mock

    def _headers(self):
        # BPJS: HMAC-SHA256 dari "cons_id&timestamp" dengan Consumer Secret,
        # hasil digest biner di-Base64. Timestamp harus Unix epoch dalam detik (UTC).
        ts = str(int(time.time()))
        message = f"{self.cons_id}&{ts}".encode("utf-8")
        key = self.secret.encode("utf-8")
        digest = hmac.new(key, message, hashlib.sha256).digest()
        sig = base64.b64encode(digest).decode("ascii")
        # Samakan nama header dengan implementasi resmi Khanza BPJSApiAplicare.
        # Nama header HTTP tidak peka huruf besar/kecil, tetapi format ini
        # dibuat identik agar mudah dibandingkan saat diagnosis.
        h = {
            "X-Cons-ID": self.cons_id,
            "X-Timestamp": ts,
            "X-Signature": sig,
            "user_key": self.user_key,  # Khanza selalu mengirim header ini
            "Content-Type": "application/json",
            "Accept": "application/json",
        }
        return h

    def _request(self, method, path, body=None):
        if self.mock:
            return {"metadata": {"code": "200", "message": "MOCK"}, "response": {"list": []}, "_http": 200}
        r = requests.request(method, self.base + path, headers=self._headers(), json=body, timeout=self.timeout)
        try:
            data = r.json()
        except Exception:
            return {"_nonjson": True, "_text": r.text[:300], "_http": r.status_code}
        if not isinstance(data, dict):
            data = {"_raw": data}
        data["_http"] = r.status_code
        return data

    @staticmethod
    def _meta(res) -> dict:
        """Ambil metadata tanpa membedakan kapitalisasi (metadata/metaData)."""
        for k, v in res.items():
            if str(k).casefold() == "metadata" and isinstance(v, dict):
                return v
        return {}

    @staticmethod
    def _meta_value(meta, wanted, default=None):
        """Ambil properti metadata tanpa membedakan Code/code dan Message/message."""
        wanted = {str(x).casefold() for x in wanted}
        for key, value in meta.items():
            if str(key).casefold() in wanted:
                return value
        return default

    def ok(self, res) -> bool:
        if res.get("_nonjson"):
            return False
        meta = self._meta(res)
        http_ok = 200 <= int(res.get("_http", 0)) < 300
        if not http_ok:
            return False
        # Aplicare kerap mengirim "Code" (C besar), bukan "code".
        # Jika metadata berisi kode, kode aplikasi wajib sukses; HTTP 200 saja TIDAK cukup.
        code = self._meta_value(meta, ("code", "responsecode", "statuscode"))
        if code is not None:
            return str(code).strip() in self.ok_codes
        # Metadata tanpa kode juga tidak boleh dianggap sukses secara otomatis.
        if meta:
            return False
        return 200 <= int(res.get("_http", 0)) < 300

    @staticmethod
    def message(res) -> str:
        if res.get("_nonjson"):
            return f"HTTP {res.get('_http', '?')} bukan JSON: {res.get('_text', '')}"[:300]
        meta = BpjsClient._meta(res)
        code = BpjsClient._meta_value(meta, ("code", "responsecode", "statuscode"), "?")
        message = BpjsClient._meta_value(meta, ("message", "msg", "description"), "")
        if meta:
            return f"Code={code} {message}".strip()
        raw = res.get("_raw")
        if raw is not None:
            return f"HTTP {res.get('_http', '?')} {json.dumps(raw, ensure_ascii=False)}"[:300]
        return f"HTTP {res.get('_http', '?')}"

    @staticmethod
    def _items(res):
        resp = res.get("response")
        if isinstance(resp, dict):
            resp = resp.get("list") or []
        return resp if isinstance(resp, list) else []

    def missing(self):
        out = []
        if not self.cons_id:
            out.append("Cons ID")
        if not self.secret:
            out.append("Secret Key (kosong, atau tidak bisa didekripsi: DPAPI hanya terbuka di akun Windows yang menyimpannya)")
        if not self.user_key:
            out.append("User Key Aplicare (kosong, atau tidak bisa didekripsi: DPAPI hanya terbuka di akun Windows yang menyimpannya)")
        if not self.kode_ppk:
            out.append("Kode PPK")
        return out

    def read_page(self, start=None, limit=100):
        # Aplicare: start dimulai dari 1 (baris pertama), limit = jumlah baris.
        start = self.read_start if start is None else start
        return self._request("GET", f"{self.paths['path_read']}/{self.kode_ppk}/{start}/{limit}")

    def _read_retry(self, start, page, retries=0, stop=None, log=None):
        """Baca satu halaman; ulangi hanya bila koneksi terputus / timeout / HTTP 5xx / 429."""
        for attempt in range(retries + 1):
            try:
                res = self.read_page(start, page)
                if self.ok(res) or not _is_transient(res=res) or attempt >= retries:
                    return res
                why = f"HTTP {res.get('_http')}"
            except Exception as e:
                if not _is_transient(exc=e) or attempt >= retries:
                    raise
                why = type(e).__name__
            if log:
                log("PERINGATAN", f"Baca MJKN terputus ({why}); mengulang {attempt + 1}/{retries}…")
            wait = min(2 ** (attempt + 1), 15)
            if stop is not None:
                if stop.wait(wait):
                    break
            else:
                time.sleep(wait)
        raise RuntimeError("Baca MJKN dibatalkan.")

    def read_all(self, page=100, max_pages=50, retries=0, stop=None, log=None):
        out, seen, start = [], set(), self.read_start
        for _ in range(max_pages):
            res = self._read_retry(start, page, retries, stop, log)
            if not self.ok(res):
                raise RuntimeError("Baca MJKN gagal: " + self.message(res))
            items = self._items(res)
            if not items and not out:
                try:
                    raw = json.dumps(res, ensure_ascii=False)
                except Exception:
                    raw = str(res)
                self.last_raw = (f"GET {self.paths['path_read']}/{self.kode_ppk}/{start}/{page} -> " + raw)[:450]
            new = 0
            for it in items:
                k = (it.get("kodekelas"), it.get("koderuang"))
                if k in seen:
                    continue
                seen.add(k)
                out.append(it)
                new += 1
            if len(items) < page or new == 0:
                break
            start += page
        return out

    def ref_kelas(self):
        return self._request("GET", self.paths["path_ref_kelas"])

    def update(self, payload):
        return self._request("POST", f"{self.paths['path_update']}/{self.kode_ppk}", payload)

    # create/delete hanya untuk aksi manual berkonfirmasi (tidak dipanggil siklus otomatis)
    def create(self, payload):
        return self._request("POST", f"{self.paths['path_create']}/{self.kode_ppk}", payload)

    def delete(self, payload):
        return self._request("POST", f"{self.paths['path_delete']}/{self.kode_ppk}", payload)


def _is_transient(res=None, exc=None) -> bool:
    """Hanya gangguan sementara yang layak diulang."""
    if exc is not None:
        return isinstance(exc, (requests.exceptions.ConnectionError, requests.exceptions.Timeout))
    http = int((res or {}).get("_http", 0))
    return http >= 500 or http == 429


def send_rows_to_bpjs(cfg, rows, log, stop=None):
    """Kirim baris (update saja). Return (dikirim, gagal, tidak_ditemukan, mencoba).
    Baris tabel dicocokkan ke ruang MJKN (lihat match_mjkn); update memakai kodekelas,
    koderuang, dan namaruang milik MJKN. Tidak pernah membuat/menghapus entri."""
    bp = cfg["bpjs"]
    if not bp.get("cons_id"):
        log("INFO", "Kredensial BPJS belum diisi; lewati pengiriman.")
        return [], [], [], False
    client = BpjsClient(bp)
    all_keys = [(r["kode_kelas_aplicare"], r["kd_bangsal"]) for r in rows]
    lacking = client.missing()
    if lacking:
        log("PERINGATAN", "Pengiriman ke MJKN dibatalkan, belum lengkap: " + "; ".join(lacking) + ".")
        return [], all_keys, [], True
    retries = max(0, int(cfg["auto"].get("retry", 3)))
    try:
        mjkn = client.read_all(retries=retries, stop=stop, log=log)
    except Exception as e:
        log("PERINGATAN", f"Gagal membaca MJKN: {e}")
        return [], all_keys, [], True
    st = load_state()
    st["mjkn_terakhir"] = mjkn
    st["waktu_baca_mjkn"] = _now_str()
    save_state(st)
    if not mjkn:
        log("PERINGATAN", "MJKN tidak mengembalikan ruang apa pun untuk Kode PPK ini; periksa Kode PPK dan User Key.")
        if client.last_raw:
            log("PERINGATAN", "Balasan MJKN: " + client.last_raw)
    matches = match_mjkn(rows, mjkn)
    sent, failed, notfound = [], [], []
    for r in rows:
        key = (r["kode_kelas_aplicare"], r["kd_bangsal"])
        mt = matches.get(key) or {"entry": None, "how": "tidak ada", "cands": [], "hits": []}
        m = mt["entry"]
        if m is None:
            notfound.append(key)
            log("PERINGATAN", _notfound_text(key, mt, mjkn))
            continue
        if mt["how"] != "tepat":
            log("PERINGATAN", f"{key[1]} ({key[0]}) dicocokkan ke MJKN {m.get('koderuang')} ({mt['how']}). "
                              "Samakan kd_bangsal di tabel dengan koderuang MJKN agar cocok persis.")
        t = r["tersedia"]
        payload = {"kodekelas": str(m.get("kodekelas") or key[0]),
                   "koderuang": str(m.get("koderuang") or key[1]),
                   "namaruang": str(m.get("namaruang") or r.get("nm_bangsal") or key[1]),
                   "kapasitas": str(r["kapasitas"]), "tersedia": str(t), "tersediapria": str(t),
                   "tersediawanita": str(t), "tersediapriawanita": str(t)}
        ok = False
        for attempt in range(retries + 1):
            transient = False
            try:
                res = client.update(payload)
                if client.ok(res):
                    ok = True
                    break
                log("PERINGATAN", f"{payload['koderuang']}: {client.message(res)}")
                transient = _is_transient(res=res)
            except Exception as e:
                log("PERINGATAN", f"Kirim {payload['koderuang']} gagal: {e}")
                transient = _is_transient(exc=e)
            if not transient:
                break
            if attempt < retries:
                if stop is not None:
                    if stop.wait(min(2 ** attempt, 10)):
                        break
                else:
                    time.sleep(min(2 ** attempt, 10))
        if ok:
            sent.append(key)
            log("INFO", f"MJKN {payload['koderuang']}: {r['kapasitas']} / {t} terkirim.")
        else:
            failed.append(key)
            log("PERINGATAN", f"Baris {key[1]} tertunda.")
    return sent, failed, notfound, True


def refresh_ref_kelas(cfg, log):
    bp = cfg["bpjs"]
    if not bp.get("cons_id"):
        return
    try:
        cl = BpjsClient(bp)
        res = cl.ref_kelas()
        if cl.ok(res):
            update_state(ref_kelas=BpjsClient._items(res))
    except Exception as e:
        log("PERINGATAN", f"Referensi kelas gagal dibaca: {e}")


# ============================================================
# Penjadwal / siklus penuh
# ============================================================
class Scheduler:
    def __init__(self, log_fn=None, step_fn=None, done_fn=None):
        self._lock = threading.Lock()
        self._stop = threading.Event()
        self._thread = None
        self._first = True
        self.running = False
        self.log_fn = log_fn or (lambda l, m: None)
        self.step_fn = step_fn or (lambda i: None)
        self.done_fn = done_fn or (lambda *a: None)

    def start(self):
        if self.running:
            return
        self._stop.clear()
        self._thread = threading.Thread(target=self._loop, daemon=True)
        self.running = True
        self._thread.start()

    def stop(self):
        self._stop.set()
        self.running = False

    def run_now(self, by="manual"):
        threading.Thread(target=self._run_cycle, args=(by,), daemon=True).start()

    def _loop(self):
        last = None
        while not self._stop.is_set():
            try:
                cfg = load_cfg()
                if cfg["auto"].get("enabled"):
                    iv = max(60, int(cfg["auto"].get("interval_min", 30)) * 60)
                    if last is None or time.monotonic() - last >= iv:
                        self._run_cycle("auto")
                        last = time.monotonic()
            except Exception as e:
                self.log_fn("KESALAHAN", f"Siklus auto gagal: {e}")
            self._stop.wait(5)

    def _run_cycle(self, by):
        if not self._lock.acquire(blocking=False):
            self.log_fn("INFO", "Siklus sebelumnya belum selesai; dilewati.")
            return
        cnt = plan = None
        try:
            cfg = load_cfg()
            if not cfg["db"].get("database"):
                self.log_fn("INFO", "Database SIMRS belum diisi (Setting); siklus dilewati.")
                return
            db = _db_cfg(cfg)
            self.step_fn(1)
            kamar = db_read_kamar(db)
            apl = db_read_aplicare(db)
            self.log_fn("INFO", f"Membaca tabel kamar → {len(kamar)} baris; aplicare {len(apl)} baris.")
            if self._first:
                refresh_ref_kelas(cfg, self.log_fn)
            st = load_state()
            self.step_fn(2)
            cnt, plan = dry_run(cfg, kamar, apl, _valid_codes(st))
            for k in cnt["conflicts"]:
                self.log_fn("PERINGATAN", f"{k}: duplikat berstatus berbeda, dihitung ISI.")
            for p in plan:
                if p["aksi"] == "tidak_valid":
                    self.log_fn("PERINGATAN", f"Baris {p['kode_kelas_aplicare']} · {p['kd_bangsal'] or '(kosong)'} "
                                              f"tidak valid ({p['invalid_reason']}); tidak dikirim.")
            changed = [p for p in plan if p["aksi"] == "update"]
            waiting = [p for p in changed if needs_approval(p, cfg)]
            auto_ok = [p for p in changed if p not in waiting]
            if waiting:
                self.log_fn("PERINGATAN", f"{len(waiting)} perubahan kapasitas menunggu persetujuan (Kirim terpilih).")
            full = self._first or bool(st.get("tertunda"))
            send_all = full or not cfg["auto"].get("only_if_changed", True)
            if not auto_ok and not send_all:
                self.log_fn("INFO", "Tidak ada perubahan yang boleh dikirim otomatis; lewati pengiriman."
                                    if waiting else "Tidak ada perubahan; lewati pengiriman.")
                update_state(waktu_siklus_terakhir=_now_str(), baris_ditulis_terakhir=0,
                             menunggu_persetujuan=[_key_of(p) for p in waiting])
                return
            written = 0
            if auto_ok:
                self.step_fn(3)
                written = db_update_aplicare(db, [{k: p[k] for k in ("kode_kelas_aplicare", "kd_bangsal",
                                                                      "kapasitas", "tersedia")} for p in auto_ok])
                self.log_fn("INFO", f"Update tabel aplicare: {written} baris.")
            self.step_fn(4)
            if send_all:
                to_send = []
                for p in plan:
                    if p["aksi"] not in ("update", "tetap"):
                        continue
                    row = dict(p)
                    if p in waiting:  # belum disetujui: kirim angka lama yang ada di tabel
                        row["kapasitas"], row["tersedia"] = p["kapasitas_lama"], p["tersedia_lama"]
                    to_send.append(row)
            else:
                to_send = auto_ok
            sent, failed, notfound, tried = send_rows_to_bpjs(cfg, to_send, self.log_fn, self._stop)
            if tried:
                self._first = False
                self.log_fn("INFO", f"Kirim MJKN selesai: {len(sent)} sukses, {len(failed)} tertunda, "
                                    f"{len(notfound)} tidak ditemukan di MJKN.")
            self.step_fn(5)
            update_state(waktu_siklus_terakhir=_now_str(), baris_ditulis_terakhir=written,
                         tertunda=[{"kode_kelas_aplicare": k[0], "kd_bangsal": k[1]} for k in failed]
                         if tried else load_state().get("tertunda", []),
                         menunggu_persetujuan=[_key_of(p) for p in waiting],
                         tidak_ditemukan=([{"kode_kelas_aplicare": k[0], "kd_bangsal": k[1]} for k in notfound]
                                          if tried else load_state().get("tidak_ditemukan", [])),
                         hasil_hitung_terakhir={"total_map": cnt["total_map"], "kosong": cnt["total_map_kosong"],
                                                "belum_ada_baris": cnt["total_pending"],
                                                "tidak_dihitung": len(cnt["ignored"])})
        except CycleError as e:
            self.log_fn("PERINGATAN", f"Siklus dihentikan: {e}")
        except Exception as e:
            self.log_fn("KESALAHAN", f"Siklus gagal: {e}")
        finally:
            self.step_fn(1)
            self._lock.release()
            self.done_fn(cnt, plan, by)


def _key_of(p):
    return {"kode_kelas_aplicare": p["kode_kelas_aplicare"], "kd_bangsal": p["kd_bangsal"],
            "kapasitas": p["kapasitas"], "tersedia": p["tersedia"]}


# ============================================================
# UI — util, ikon, QSS
# ============================================================
class Bus(QObject):
    """Jembatan thread → UI."""
    log = Signal(str, str)
    step = Signal(int)
    cycle_done = Signal(object, object, str)
    task_done = Signal(object, object, object)

    def __init__(self):
        super().__init__()
        self.task_done.connect(self._on_task)

    @Slot(object, object, object)
    def _on_task(self, cb, res, err):
        cb(res, err)

    def run(self, fn, cb):
        def w():
            try:
                res, err = fn(), None
            except Exception as e:  # noqa: BLE001
                res, err = None, e
            self.task_done.emit(cb, res, err)
        threading.Thread(target=w, daemon=True).start()

    def emit_log(self, level, msg):
        log_file(level, msg)
        self.log.emit(level, msg)


BUS: Bus | None = None


def _paint_icon(size, painter_fn):
    pm = QPixmap(size, size)
    pm.fill(Qt.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.Antialiasing)
    painter_fn(p)
    p.end()
    return pm


def logo_pixmap(size=40):
    def draw(p):
        p.setBrush(QColor(PAL["primary"]))
        p.setPen(Qt.NoPen)
        p.drawRoundedRect(0, 0, size, size, size * 0.26, size * 0.26)
        p.translate(size * 0.2, size * 0.2)
        p.scale(size * 0.6 / 24, size * 0.6 / 24)
        pen = QPen(QColor(PAL["text"]), 2.2)
        pen.setCapStyle(Qt.RoundCap)
        pen.setJoinStyle(Qt.RoundJoin)
        p.setPen(pen)
        p.setBrush(Qt.NoBrush)
        p.drawLine(2, 4, 2, 20)
        path = QPainterPath()
        path.moveTo(2, 8)
        path.lineTo(18, 8)
        path.quadTo(22, 8, 22, 12)
        path.lineTo(22, 20)
        p.drawPath(path)
        p.drawLine(2, 17, 22, 17)
        p.drawLine(6, 8, 6, 17)
    return _paint_icon(size, draw)


def eye_icon(slashed=False, size=22):
    def draw(p):
        p.scale(size / 24, size / 24)
        pen = QPen(QColor(PAL["text"]), 2)
        pen.setCapStyle(Qt.RoundCap)
        p.setPen(pen)
        path = QPainterPath()
        path.moveTo(2, 12)
        path.cubicTo(5, 6.5, 8.5, 5, 12, 5)
        path.cubicTo(15.5, 5, 19, 6.5, 22, 12)
        path.cubicTo(19, 17.5, 15.5, 19, 12, 19)
        path.cubicTo(8.5, 19, 5, 17.5, 2, 12)
        p.drawPath(path)
        p.drawEllipse(QPoint(12, 12), 3, 3)
        if slashed:
            p.drawLine(4, 4, 20, 20)
    return QIcon(_paint_icon(size, draw))


def _ensure_check_icon() -> str:
    path = _config_dir() / "check.png"
    if not path.exists():
        def draw(p):
            pen = QPen(QColor("#FFFFFF"), 2.4)
            pen.setCapStyle(Qt.RoundCap)
            pen.setJoinStyle(Qt.RoundJoin)
            p.setPen(pen)
            p.drawPolyline([QPoint(4, 9), QPoint(8, 13), QPoint(14, 5)])
        _paint_icon(18, draw).save(str(path), "PNG")
    return str(path).replace("\\", "/")


def build_qss() -> str:
    chk = _ensure_check_icon()
    return f"""
QWidget {{ background: transparent; color: {PAL['text']};
    font-family: 'Noto Sans Devanagari', 'Segoe UI', sans-serif; font-size: 13px; }}
QMainWindow, QDialog, QMessageBox, QWidget#Root {{ background: {PAL['bg']}; }}
QFrame#Header {{ background: #FFFFFF; border: none; border-bottom: 1px solid {PAL['card_border']}; }}
QFrame#Card {{ background: #FFFFFF; border: 1px solid {PAL['card_border']}; border-radius: 14px; }}
QLabel#Kicker {{ color: {PAL['muted']}; font-size: 11px; font-weight: 600; letter-spacing: 1px; }}
QLabel#Title {{ font-size: 15px; font-weight: 700; }}
QLabel#Heading {{ font-size: 19px; font-weight: 700; }}
QLabel#Sub {{ color: {PAL['muted']}; font-size: 12px; }}
QLabel#Muted {{ color: {PAL['muted']}; }}
QLabel#FieldLabel {{ color: {PAL['muted']}; font-size: 12px; font-weight: 700; }}
QLabel#ConsoleLabel {{ color: {PAL['muted']}; font-size: 12px; font-weight: 700; }}
QLabel#Pill {{ background: {PAL['lavender']}; color: {PAL['lavender_fg']}; border-radius: 14px;
    padding: 6px 14px; font-weight: 700; font-size: 12px; }}
QLabel#ClassChip {{ background: #FFFFFF; border: 1.5px solid {PAL['secondary']}; color: {PAL['text']};
    border-radius: 11px; padding: 3px 12px; font-size: 12px; font-weight: 600; }}
QLabel#FindTag {{ background: #DDE1FF; color: {PAL['lavender_fg']}; border-radius: 10px;
    padding: 4px 10px; font-size: 12px; font-weight: 700; }}
QFrame#Step {{ background: #FFFFFF; border: 1.5px solid #C5CCFF; border-radius: 16px; }}
QFrame#Step[active="true"] {{ background: {PAL['primary']}; border-color: {PAL['primary']}; }}
QLabel#StepNum {{ background: {PAL['lavender']}; color: {PAL['accent']}; border-radius: 11px;
    font-size: 11px; font-weight: 700; }}
QFrame#Step[active="true"] QLabel#StepNum {{ background: {PAL['text']}; color: #FFFFFF; }}
QLabel#StepText {{ font-weight: 600; font-size: 12px; }}
QFrame#PreviewBox {{ background: #E6FBF6; border: none; border-radius: 14px; }}
QFrame#PreviewInner {{ background: #FFFFFF; border: 1px solid {PAL['card_border']}; border-radius: 10px; }}
QLabel#PreviewText {{ font-family: 'Cascadia Mono', 'Consolas', monospace; font-size: 12px; }}
QLineEdit, QSpinBox, QTextEdit {{ background: #FFFFFF; border: 1.5px solid {PAL['input_border']};
    border-radius: 10px; padding: 9px 12px; selection-background-color: {PAL['accent']}; selection-color: #FFFFFF; }}
QLineEdit:focus, QSpinBox:focus, QTextEdit:focus {{ border-color: {PAL['accent']}; }}
QSpinBox {{ padding-left: 12px; padding-right: 12px; }}
QSpinBox::up-button {{ subcontrol-origin: border; width: 0; }}
QSpinBox::down-button {{ subcontrol-origin: border; width: 0; }}
QSpinBox QLineEdit {{ border: none; background: transparent; padding: 0px; }}
QLineEdit#RuleInput {{ border-radius: 12px; padding: 9px 12px; }}
QLineEdit#RuleInput[bad="true"] {{ border-color: {PAL['danger']}; }}
QTextEdit#Console {{ background: {PAL['console_bg']}; color: {PAL['console_fg']};
    font-family: 'Cascadia Mono', 'Consolas', monospace; border-radius: 14px; border: none;
    padding: 14px; font-size: 12px; }}
QPushButton {{ background: #FFFFFF; color: {PAL['text']}; border: 1.5px solid {PAL['text']};
    border-radius: 10px; padding: 9px 16px; font-weight: 600; }}
QPushButton:hover {{ background: #F2FFFC; }}
QPushButton:disabled {{ color: #8AA19B; border-color: #BFD3CE; }}
QPushButton#Primary {{ background: {PAL['accent']}; color: #FFFFFF; border: 1.5px solid {PAL['accent']}; }}
QPushButton#Primary:hover {{ background: #4a36d6; border-color: #4a36d6; }}
QPushButton#Secondary {{ background: {PAL['primary']}; color: {PAL['text']}; border: 1.5px solid {PAL['primary']}; }}
QPushButton#Secondary:hover {{ background: #0fe0b6; }}
QPushButton#Icon {{ padding: 0px; min-width: 44px; max-width: 44px; min-height: 44px; max-height: 44px; }}
QPushButton#Tiny {{ border: none; background: transparent; color: {PAL['muted']}; padding: 0px 5px;
    font-size: 13px; font-weight: 700; }}
QPushButton#Tiny:hover {{ color: {PAL['accent']}; }}
QPushButton#Page {{ padding: 5px 0px; min-width: 32px; max-width: 32px; font-size: 14px; }}
QPushButton#PageOn {{ background: {PAL['accent']}; color: #FFFFFF; border: 1.5px solid {PAL['accent']};
    padding: 5px 0px; min-width: 32px; max-width: 32px; font-size: 13px; }}
QCheckBox {{ spacing: 10px; }}
QCheckBox::indicator, QTableView::indicator {{ width: 18px; height: 18px; border: 1.5px solid {PAL['accent']};
    border-radius: 5px; background: #FFFFFF; }}
QCheckBox::indicator:checked, QTableView::indicator:checked {{ background: {PAL['accent']};
    border-color: {PAL['accent']}; image: url({chk}); }}
QTableWidget {{ background: #FFFFFF; border: none; }}
QTableWidget::item {{ border-bottom: 1px solid {PAL['row_line']}; padding-left: 8px; }}
QHeaderView {{ background: #FFFFFF; }}
QHeaderView::section {{ background: #FFFFFF; border: none; border-bottom: 2px solid {PAL['text']};
    padding: 10px 8px; font-weight: 700; color: {PAL['muted']}; font-size: 12px; }}
QScrollArea {{ border: none; background: transparent; }}
QScrollArea > QWidget > QWidget {{ background: transparent; }}
QScrollBar:vertical {{ background: transparent; width: 10px; margin: 2px; }}
QScrollBar::handle:vertical {{ background: #7A8E89; border-radius: 4px; min-height: 30px; }}
QScrollBar::add-line, QScrollBar::sub-line {{ height: 0; width: 0; }}
QScrollBar:horizontal {{ height: 0; }}
QToolTip {{ background: #FFFFFF; color: {PAL['text']}; border: 1px solid {PAL['card_border']}; padding: 4px; }}
"""


def pill_style(mode: str) -> str:
    base = "border-radius:11px;padding:4px 14px;font-weight:700;font-size:12px;"
    return {
        "idle": f"background:{PAL['lavender']};color:{PAL['lavender_fg']};{base}",
        "ok": f"background:{PAL['primary']};color:{PAL['text']};{base}",
        "bad": f"background:#FFE0E0;color:#8E2020;{base}",
        "outline": f"background:#FFFFFF;border:1.5px solid {PAL['secondary']};color:{PAL['lavender_fg']};{base}",
    }[mode]


def confirm(parent, title, text, yes="Ya, lanjutkan") -> bool:
    mb = QMessageBox(parent)
    mb.setWindowTitle(title)
    mb.setText(text)
    mb.setIcon(QMessageBox.Question)
    b_yes = mb.addButton(yes, QMessageBox.AcceptRole)
    mb.addButton("Batal", QMessageBox.RejectRole)
    mb.exec()
    return mb.clickedButton() is b_yes


class FlowLayout(QLayout):
    def __init__(self, parent=None, h=8, v=8):
        super().__init__(parent)
        self._items, self._h, self._v = [], h, v

    def addItem(self, item): self._items.append(item)
    def count(self): return len(self._items)
    def itemAt(self, i): return self._items[i] if 0 <= i < len(self._items) else None
    def takeAt(self, i): return self._items.pop(i) if 0 <= i < len(self._items) else None
    def hasHeightForWidth(self): return True
    def heightForWidth(self, w): return self._do(QRect(0, 0, w, 0), True)

    def setGeometry(self, r):
        super().setGeometry(r)
        self._do(r, False)

    def sizeHint(self): return self.minimumSize()

    def minimumSize(self):
        s = QSize()
        for it in self._items:
            s = s.expandedTo(it.minimumSize())
        return s

    def _do(self, rect, test):
        x, y, lh = rect.x(), rect.y(), 0
        for it in self._items:
            w = it.sizeHint()
            nx = x + w.width()
            if nx > rect.right() and lh > 0:
                x, y, lh = rect.x(), y + lh + self._v, 0
                nx = x + w.width()
            if not test:
                it.setGeometry(QRect(QPoint(x, y), w))
            x, lh = nx + self._h, max(lh, w.height())
        return y + lh - rect.y()


class Card(QFrame):
    def __init__(self, parent=None, margins=20, spacing=10):
        super().__init__(parent)
        self.setObjectName("Card")
        self._lay = QVBoxLayout(self)
        self._lay.setContentsMargins(margins, margins, margins, margins)
        self._lay.setSpacing(spacing)

    def body(self): return self._lay


class Console(QTextEdit):
    COLORS = {"INFO": PAL["console_fg"], "PERINGATAN": "#FFE08A", "KESALAHAN": "#FF8A8A"}

    def __init__(self, parent=None, min_h=150):
        super().__init__(parent)
        self.setObjectName("Console")
        self.setReadOnly(True)
        self.setMinimumHeight(min_h)

    def add(self, level, msg):
        ts = _dt.datetime.now().strftime("%H:%M:%S")
        color = self.COLORS.get(level, PAL["console_fg"])
        esc = msg.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
        self.append(f'<span style="color:#7A9E96">[{ts}]</span> <span style="color:{color}">{esc}</span>')
        self.moveCursor(QTextCursor.End)


    def add_block(self, level, title, lines):
        """Satu judul bercap waktu, lalu baris-baris rinci menjorok di bawahnya."""
        self.add(level, title)
        color = self.COLORS.get(level, PAL["console_fg"])
        for ln in lines:
            body = ln.lstrip(" ")
            lead = "&nbsp;" * (11 + len(ln) - len(body))
            esc = body.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
            self.append(f'<span style="color:{color}">{lead}{esc}</span>')
        self.moveCursor(QTextCursor.End)


class StepChip(QFrame):
    def __init__(self, idx, text, parent=None):
        super().__init__(parent)
        self.setObjectName("Step")
        self.setProperty("active", False)
        lay = QHBoxLayout(self)
        lay.setContentsMargins(6, 4, 14, 4)
        lay.setSpacing(8)
        num = QLabel(str(idx))
        num.setObjectName("StepNum")
        num.setFixedSize(22, 22)
        num.setAlignment(Qt.AlignCenter)
        t = QLabel(text)
        t.setObjectName("StepText")
        lay.addWidget(num)
        lay.addWidget(t)
        self.setSizePolicy(QSizePolicy.Maximum, QSizePolicy.Fixed)

    def set_active(self, on):
        self.setProperty("active", bool(on))
        self.style().unpolish(self)
        self.style().polish(self)
        for w in self.findChildren(QLabel):
            w.style().unpolish(w)
            w.style().polish(w)


class SecretField(QWidget):
    """Label di atas, input + tombol mata di kanan (sesuai desain Setting)."""
    def __init__(self, label, placeholder="", hidden=True, default="", parent=None):
        super().__init__(parent)
        v = QVBoxLayout(self)
        v.setContentsMargins(0, 0, 0, 0)
        v.setSpacing(6)
        lab = QLabel(label)
        lab.setObjectName("FieldLabel")
        v.addWidget(lab)
        row = QHBoxLayout()
        row.setSpacing(10)
        self.edit = QLineEdit(default)
        self.edit.setPlaceholderText(placeholder)
        self.edit.setMinimumHeight(44)
        self.btn = QPushButton()
        self.btn.setObjectName("Icon")
        self._hidden = hidden
        self.edit.setEchoMode(QLineEdit.Password if hidden else QLineEdit.Normal)
        self.btn.setIcon(eye_icon(not hidden))
        self.btn.setIconSize(QSize(22, 22))
        self.btn.setToolTip("Tampilkan / sembunyikan")
        self.btn.clicked.connect(self._toggle)
        row.addWidget(self.edit, 1)
        row.addWidget(self.btn)
        v.addLayout(row)

    def _toggle(self):
        self._hidden = not self._hidden
        self.edit.setEchoMode(QLineEdit.Password if self._hidden else QLineEdit.Normal)
        self.btn.setIcon(eye_icon(not self._hidden))

    def text(self): return self.edit.text()
    def clear(self): self.edit.clear()


def labeled_input(label, placeholder="", default=""):
    w = QWidget()
    v = QVBoxLayout(w)
    v.setContentsMargins(0, 0, 0, 0)
    v.setSpacing(6)
    lab = QLabel(label)
    lab.setObjectName("FieldLabel")
    e = QLineEdit(default)
    e.setPlaceholderText(placeholder)
    e.setMinimumHeight(44)
    v.addWidget(lab)
    v.addWidget(e)
    return w, e


def wrap_scroll(widget):
    sa = QScrollArea()
    sa.setWidgetResizable(True)
    sa.setFrameShape(QFrame.NoFrame)
    sa.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
    sa.setWidget(widget)
    return sa


# ---------- parsing aturan dari input UI ----------
def parse_from_text(text: str):
    t = text.strip()
    if not t:
        raise ValueError("nama kamar / kelas kosong")
    if re.match(r"^kelas\s", t, re.I) or t == "-":
        return {"field": "kelas", "equals": t}
    parts = [p.strip().rstrip("*").strip() for p in re.split(r"[,;]", t) if p.strip()]
    if not parts:
        raise ValueError("awalan kosong")
    return {"field": "kd_kamar", "startswith": parts}


def parse_to_text(text: str):
    """Kolom kanan: 'KODE * NAMA' (mis. 'KL1 * KEL-1') = hubungkan ke satu baris tabel
    aplicare_ketersediaan_kamar (kode_kelas_aplicare * nama kamar di tabel)."""
    t = text.strip()
    low = t.lower()
    if not t or "belum ada baris" in low:
        return "pending_row", None
    if "tidak dihitung" in low:
        return "ignore", None
    for sep in ("*", "·", "|"):  # '·' dan '|' hanya agar config lama tetap terbaca
        if sep in t:
            a, b = (x.strip() for x in t.split(sep, 1))
            if a and b:
                return "map", {"kode_kelas_aplicare": a, "kd_bangsal": b}
            break
    raise ValueError("format tujuan: KODE * NAMA (mis. KL1 * KEL-1), kosong, atau 'tidak dihitung'")


def resolve_aplicare_target(target, apl_rows):
    """Samakan KODE * NAMA dengan baris yang ada di tabel aplicare (abaikan huruf besar/kecil
    dan spasi ganda), lalu pakai tulisan persis seperti di tabel. Bila tidak ada baris yang
    cocok, nilai dikembalikan apa adanya (caption akan menandai 'Belum ada baris')."""
    if not target or not apl_rows:
        return target

    def norm(s):
        return _WS.sub(" ", str(s or "")).strip().casefold()

    k, n = norm(target.get("kode_kelas_aplicare")), norm(target.get("kd_bangsal"))
    hits = {(r.get("kode_kelas_aplicare") or "", r.get("kd_bangsal") or "")
            for r in apl_rows
            if norm(r.get("kode_kelas_aplicare")) == k and norm(r.get("kd_bangsal")) == n}
    if len(hits) == 1:
        kode, nama = next(iter(hits))
        return {"kode_kelas_aplicare": kode, "kd_bangsal": nama}
    return target


class RuleRow(QWidget):
    """Dua input (asal → tujuan) + caption hasil hitung; tombol ↑ ↓ × kecil di baris caption."""
    def __init__(self, rule, owner, parent=None):
        super().__init__(parent)
        self.rule = rule
        self.owner = owner
        v = QVBoxLayout(self)
        v.setContentsMargins(0, 0, 6, 0)
        v.setSpacing(2)
        row = QHBoxLayout()
        row.setSpacing(8)
        self.e_from = QLineEdit(self._from_text(rule))
        self.e_from.setObjectName("RuleInput")
        self.e_from.setPlaceholderText("C-AWALAN* atau Kelas 1")
        self.e_from.setMinimumHeight(40)
        arrow = QLabel("→")
        arrow.setObjectName("Muted")
        self.e_to = QLineEdit(self._to_text(rule))
        self.e_to.setObjectName("RuleInput")
        self.e_to.setPlaceholderText("mis. KL1 * KEL-1")
        self.e_to.setToolTip("Isi dengan: KODE * NAMA, sesuai baris di tabel aplicare_ketersediaan_kamar.\n"
                             "Contoh: KL1 * KEL-1\n"
                             "Kosong = belum ada baris · 'tidak dihitung' = diabaikan")
        self.e_to.setMinimumHeight(40)
        row.addWidget(self.e_from, 1)
        row.addWidget(arrow)
        row.addWidget(self.e_to, 1)
        v.addLayout(row)
        cap = QHBoxLayout()
        cap.setContentsMargins(2, 0, 0, 6)
        self.caption = QLabel("— kamar · — kosong")
        self.caption.setObjectName("Sub")
        self.caption.setWordWrap(True)
        cap.addWidget(self.caption, 1)
        for txt, tip, fn in (("↑", "Naikkan", lambda: owner.move_rule(self, -1)),
                             ("↓", "Turunkan", lambda: owner.move_rule(self, 1)),
                             ("×", "Hapus aturan", lambda: owner.delete_rule(self))):
            b = QPushButton(txt)
            b.setObjectName("Tiny")
            b.setToolTip(tip)
            b.setCursor(Qt.PointingHandCursor)
            b.clicked.connect(fn)
            cap.addWidget(b)
        v.addLayout(cap)
        self.e_from.textChanged.connect(owner.rules_edited)
        self.e_to.textChanged.connect(owner.rules_edited)

    @staticmethod
    def _from_text(r):
        m = r.get("match", {})
        if m.get("field") == "kd_kamar":
            return ", ".join(f"{p}*" for p in m.get("startswith", []))
        return m.get("equals", "") or ""

    @staticmethod
    def _to_text(r):
        a = r.get("action")
        if a == "map":
            t = r.get("target") or {}
            return f"{t.get('kode_kelas_aplicare', '')} * {t.get('kd_bangsal', '')}"
        return "tidak dihitung" if a == "ignore" else ""

    def to_rule(self):
        """Parse input → aturan. Raise ValueError bila format salah."""
        ok = True
        out = {"no": self.rule.get("no", 0)}
        try:
            out["match"] = parse_from_text(self.e_from.text())
        except ValueError:
            ok = False
        try:
            action, target = parse_to_text(self.e_to.text())
            target = resolve_aplicare_target(target, getattr(self.owner, "_apl", None))
            out["action"] = action
            if target:
                out["target"] = target
        except ValueError:
            ok = False
        for e, bad in ((self.e_from, "match" not in out), (self.e_to, "action" not in out)):
            e.setProperty("bad", bad)
            e.style().unpolish(e)
            e.style().polish(e)
        if not ok:
            raise ValueError(f"Aturan {out['no']}: format tidak valid")
        if "ref_sk" in self.rule and out.get("target") == self.rule.get("target"):
            out["ref_sk"] = self.rule["ref_sk"]
        return out


# ============================================================
# Layar "Kirim data"
# ============================================================
class ScreenKirim(QWidget):
    PAGE_SIZE = 10
    DEFAULT_CLASSES = ["VVIP", "VIP", "KELAS I", "KELAS II", "KELAS III", "ICU", "NICU", "PICU", "RUANG ISOLASI"]

    def __init__(self, main):
        super().__init__()
        self.main = main
        self.cfg = load_cfg()
        self.rules = copy.deepcopy(self.cfg["rules"])
        self._kamar = None
        self._apl = []
        self._plan_list = []
        self._plan = {}
        self._cnt = None
        self._page = 0
        self._checked = set()
        self._selected_key = None
        self._sim_time = None
        self._build()
        self._recount_timer = QTimer(self)
        self._recount_timer.setSingleShot(True)
        self._recount_timer.timeout.connect(self._recount)
        self.refresh_status()
        QTimer.singleShot(400, lambda: self.reload(silent=True))

    # ---------- build ----------
    def _build(self):
        root = QVBoxLayout(self)
        root.setContentsMargins(20, 16, 20, 20)
        root.setSpacing(12)
        self.status_lbl = QLabel("")
        self.status_lbl.setObjectName("Muted")
        root.addWidget(self.status_lbl)

        steps = QHBoxLayout()
        steps.setSpacing(8)
        self.steps = []
        names = ["Tabel kamar: ada perubahan?", "Konversi dan hitung kamar kosong",
                 "Update aplicare_ketersediaan_kamar", "Kirim ke BPJS MJKN", "Ulangi siklus"]
        for i, n in enumerate(names, 1):
            c = StepChip(i, n)
            self.steps.append(c)
            steps.addWidget(c)
            if i < len(names):
                ar = QLabel("→")
                ar.setObjectName("Muted")
                steps.addWidget(ar)
        steps.addStretch()
        root.addLayout(steps)
        self.set_step(1)

        body = QHBoxLayout()
        body.setSpacing(16)
        body.setAlignment(Qt.AlignTop)
        left = self._build_rule_panel()
        left.setFixedWidth(430)
        body.addWidget(left, 0, Qt.AlignTop)
        right = QVBoxLayout()
        right.setSpacing(14)
        right.addWidget(self._build_table_card())
        right.addWidget(self._build_findings_card())
        right.addLayout(self._build_console())
        right.addStretch(1)
        body.addLayout(right, 1)
        root.addLayout(body, 1)

    def _build_rule_panel(self):
        card = Card()
        lay = card.body()
        k = QLabel("ATURAN PENCOCOKAN")
        k.setObjectName("Kicker")
        h = QLabel("Nama kamar → baris aplicare")
        h.setObjectName("Heading")
        lay.addWidget(k)
        lay.addWidget(h)
        help_l = QLabel("Kiri: nama kamar atau kelas persis seperti di tabel kamar. Kanan: KODE * NAMA baris "
                        "di tabel aplicare_ketersediaan_kamar, mis. KL1 * KEL-1. Hanya baris yang sudah ada di "
                        "tabel yang dipakai. Dibaca dari atas, aturan pertama yang cocok dipakai. "
                        f"{SK_REF} hanya referensi.")
        help_l.setWordWrap(True)
        help_l.setObjectName("Muted")
        lay.addWidget(help_l)

        self.rules_container = QWidget()
        self.rules_v = QVBoxLayout(self.rules_container)
        self.rules_v.setContentsMargins(0, 0, 0, 0)
        self.rules_v.setSpacing(6)
        self.rules_scroll = QScrollArea()
        self.rules_scroll.setWidgetResizable(True)
        self.rules_scroll.setFrameShape(QFrame.NoFrame)
        self.rules_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.rules_scroll.setFixedHeight(290)
        self.rules_scroll.setWidget(self.rules_container)
        lay.addWidget(self.rules_scroll)
        self.rule_widgets = []
        self._fill_rules()

        self.summary = QLabel("")
        self.summary.setWordWrap(True)
        self.summary.setObjectName("Muted")
        lay.addWidget(self.summary)

        add = QPushButton("Add +")
        add.setObjectName("Secondary")
        add.setMinimumHeight(44)
        add.clicked.connect(self._add_rule)
        lay.addWidget(add)

        box = QFrame()
        box.setObjectName("PreviewBox")
        bl = QVBoxLayout(box)
        bl.setContentsMargins(14, 12, 14, 14)
        bl.setSpacing(8)
        top = QHBoxLayout()
        top.addStretch()
        salin = QPushButton("Salin")
        salin.clicked.connect(self._copy_preview)
        top.addWidget(salin)
        bl.addLayout(top)
        inner = QFrame()
        inner.setObjectName("PreviewInner")
        il = QVBoxLayout(inner)
        il.setContentsMargins(14, 12, 14, 12)
        self.preview = QLabel("Pilih satu baris di tabel untuk melihat pratinjau.")
        self.preview.setObjectName("PreviewText")
        self.preview.setTextInteractionFlags(Qt.TextSelectableByMouse)
        il.addWidget(self.preview)
        bl.addWidget(inner)
        lay.addWidget(box)

        self.cb_active = QCheckBox("Hanya kamar aktif (statusdata = 1)")
        self.cb_active.setChecked(self.cfg["auto"]["only_active"])
        self.cb_dupes = QCheckBox("Gabungkan kd_kamar ganda (spasi, huruf besar/kecil)")
        self.cb_dupes.setChecked(self.cfg["auto"]["merge_dupes"])
        self.cb_active.toggled.connect(self.rules_edited)
        self.cb_dupes.toggled.connect(self.rules_edited)
        lay.addWidget(self.cb_active)
        lay.addWidget(self.cb_dupes)

        r2 = QHBoxLayout()
        r2.setSpacing(10)
        rst = QPushButton("Reset")
        rst.setMinimumHeight(44)
        rst.clicked.connect(self._reset_rules)
        sv = QPushButton("Simpan aturan")
        sv.setObjectName("Primary")
        sv.setMinimumHeight(44)
        sv.clicked.connect(self._save_rules)
        r2.addWidget(rst, 1)
        r2.addWidget(sv, 1)
        lay.addLayout(r2)

        kl = QLabel("Kelas di MJKN")
        kl.setObjectName("FieldLabel")
        lay.addWidget(kl)
        self.chips_wrap = QWidget()
        self.chips_flow = FlowLayout(self.chips_wrap, 8, 8)
        lay.addWidget(self.chips_wrap)
        self._fill_class_chips()
        return card

    def _fill_class_chips(self):
        while self.chips_flow.count():
            it = self.chips_flow.takeAt(0)
            if it and it.widget():
                it.widget().deleteLater()
        names = [x.get("namakelas") for x in load_state().get("ref_kelas", []) if x.get("namakelas")]
        for n in (names or self.DEFAULT_CLASSES):
            c = QLabel(str(n).upper() if names else n)
            c.setObjectName("ClassChip")
            self.chips_flow.addWidget(c)

    def _fill_rules(self):
        while self.rules_v.count():
            it = self.rules_v.takeAt(0)
            if it.widget():
                it.widget().deleteLater()
        self.rule_widgets = []
        for r in self.rules:
            w = RuleRow(r, self)
            self.rules_v.addWidget(w)
            self.rule_widgets.append(w)
        self.rules_v.addStretch(1)

    def _build_table_card(self):
        card = Card()
        lay = card.body()
        head = QHBoxLayout()
        head.setSpacing(8)
        t = QLabel("Tabel aplicare_ketersediaan_kamar")
        t.setObjectName("Heading")
        head.addWidget(t)
        head.addStretch()
        for txt, slot, style in (("Muat dari SIMRS", lambda: self.reload(), "Secondary"),
                                 ("Simulasi", self.simulate, ""),
                                 ("Pilih semua", self.select_all, ""),
                                 ("Hapus pilihan", self.clear_selection, "")):
            b = QPushButton(txt)
            if style:
                b.setObjectName(style)
            b.clicked.connect(slot)
            head.addWidget(b)
        lay.addLayout(head)
        r = QHBoxLayout()
        self.b_send = QPushButton("Kirim terpilih")
        self.b_send.setObjectName("Primary")
        self.b_send.clicked.connect(self.send_selected)
        r.addWidget(self.b_send)
        self.b_add = QPushButton("Tambah baris")
        self.b_add.setMinimumHeight(42)
        self.b_add.clicked.connect(self.add_row)
        r.addWidget(self.b_add)
        self.b_del = QPushButton("Hapus baris")
        self.b_del.setMinimumHeight(42)
        self.b_del.clicked.connect(self.delete_rows)
        r.addWidget(self.b_del)
        r.addStretch()
        lay.addLayout(r)

        self.table = QTableWidget(0, 7)
        self.table.setHorizontalHeaderLabels(["", "Kode Aplicare", "Nama kamar", "Kelas SIMRS",
                                              "Kapasitas", "Tersedia", "Pria · Wanita · Campur"])
        h = self.table.horizontalHeader()
        h.setDefaultAlignment(Qt.AlignLeft | Qt.AlignVCenter)
        h.setStretchLastSection(True)
        h.setSectionResizeMode(0, QHeaderView.Fixed)
        for i, w in ((0, 46), (1, 120), (2, 170), (3, 120), (4, 120), (5, 120)):
            if i:
                h.setSectionResizeMode(i, QHeaderView.Interactive)
            self.table.setColumnWidth(i, w)
        self.table.verticalHeader().setVisible(False)
        self.table.verticalHeader().setDefaultSectionSize(52)
        self.table.setSelectionMode(QAbstractItemView.NoSelection)
        self.table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.table.setShowGrid(False)
        self.table.setFrameShape(QFrame.NoFrame)
        self.table.setFocusPolicy(Qt.NoFocus)
        self.table.setMinimumHeight(44 + 52 * self.PAGE_SIZE + 4)
        self.table.itemChanged.connect(self._on_item_changed)
        self.table.cellClicked.connect(self._on_cell_clicked)
        lay.addWidget(self.table)

        foot = QHBoxLayout()
        self.footer = QLabel("— baris")
        self.footer.setObjectName("Sub")
        foot.addWidget(self.footer)
        foot.addStretch()
        self.pager = QHBoxLayout()
        self.pager.setSpacing(6)
        foot.addLayout(self.pager)
        lay.addLayout(foot)
        return card

    def _build_findings_card(self):
        card = Card()
        lay = card.body()
        t = QLabel("Temuan tabel kirim")
        t.setObjectName("Heading")
        lay.addWidget(t)
        self.find_box = QVBoxLayout()
        self.find_box.setSpacing(8)
        lay.addLayout(self.find_box)
        self._fill_findings([("Temuan", "Belum ada data. Tekan Muat dari SIMRS atau Simulasi.")])
        return card

    def _fill_findings(self, items):
        while self.find_box.count():
            it = self.find_box.takeAt(0)
            lay = it.layout()
            if lay:
                while lay.count():
                    w = lay.takeAt(0).widget()
                    if w:
                        w.deleteLater()
        for lbl, txt in items:
            row = QHBoxLayout()
            row.setSpacing(10)
            row.setAlignment(Qt.AlignTop)
            tag = QLabel(lbl)
            tag.setObjectName("FindTag")
            tag.setWordWrap(True)
            tag.setFixedWidth(104)
            tl = QLabel(txt)
            tl.setWordWrap(True)
            tl.setObjectName("Muted")
            row.addWidget(tag, 0, Qt.AlignTop)
            row.addWidget(tl, 1)
            self.find_box.addLayout(row)

    def _build_console(self):
        v = QVBoxLayout()
        v.setSpacing(6)
        head = QHBoxLayout()
        l = QLabel("Console")
        l.setObjectName("ConsoleLabel")
        head.addWidget(l)
        head.addStretch()
        for txt, fn in (("Ekspor CSV", self.export_csv), ("Salin", self._copy_console),
                        ("Bersihkan", lambda: self.console.clear())):
            b = QPushButton(txt)
            b.setObjectName("Tiny")
            b.setCursor(Qt.PointingHandCursor)
            b.clicked.connect(fn)
            head.addWidget(b)
        v.addLayout(head)
        self.console = Console(min_h=170)
        self.console.add("INFO", "Menunggu perubahan data kamar…")
        v.addWidget(self.console)
        return v

    # ---------- util ----------
    def log(self, level, msg): self.console.add(level, msg)
    def _copy_console(self): QGuiApplication.clipboard().setText(self.console.toPlainText())
    def _copy_preview(self): QGuiApplication.clipboard().setText(self.preview.text())

    def set_step(self, i):
        for n, c in enumerate(self.steps, 1):
            c.set_active(n == i)

    def effective_cfg(self):
        cfg = load_cfg()
        cfg["rules"] = copy.deepcopy(self.rules)
        cfg["auto"]["only_active"] = self.cb_active.isChecked()
        cfg["auto"]["merge_dupes"] = self.cb_dupes.isChecked()
        return cfg

    def refresh_status(self):
        cfg = load_cfg()
        st = load_state()
        hm = lambda s: s[11:16] if s else "—"
        if cfg["auto"]["enabled"]:
            head = f"Siklus otomatis setiap {cfg['auto']['interval_min']} menit"
        else:
            head = "Kirim otomatis nonaktif"
        w = st.get("baris_ditulis_terakhir")
        wr = "belum ada yang ditulis" if not w else f"{w} baris ditulis pada siklus terakhir"
        sim = self._sim_time or "—"
        self.status_lbl.setText(f"{head} · simulasi terakhir {sim} · siklus terakhir {hm(st.get('waktu_siklus_terakhir'))}"
                                f" · {wr}")

    # ---------- aturan ----------
    def rules_edited(self, *_):
        self._recount_timer.start(350)

    def _collect_rules(self, strict=False):
        out, errs = [], []
        for i, w in enumerate(self.rule_widgets, 1):
            try:
                r = w.to_rule()
                r["no"] = i
                out.append(r)
            except ValueError as e:
                errs.append(str(e))
        if strict and errs:
            raise ValueError("; ".join(errs))
        return out

    def _sync_rules_from_widgets(self):
        rules = self._collect_rules()
        if len(rules) == len(self.rule_widgets):
            self.rules = rules
            return True
        return False

    def _add_rule(self):
        self._sync_rules_from_widgets()
        self.rules.append({"no": len(self.rules) + 1, "match": {"field": "kd_kamar", "startswith": ["C-BARU"]},
                           "action": "pending_row"})
        self._fill_rules()
        self._recount()
        self.rules_scroll.verticalScrollBar().setValue(self.rules_scroll.verticalScrollBar().maximum())

    def delete_rule(self, widget):
        if not confirm(self, "Hapus aturan", "Hapus aturan ini dari daftar? (Belum tersimpan sampai Simpan aturan.)",
                       "Hapus"):
            return
        self._sync_rules_from_widgets()
        i = self.rule_widgets.index(widget)
        if i < len(self.rules):
            self.rules.pop(i)
        for n, r in enumerate(self.rules, 1):
            r["no"] = n
        self._fill_rules()
        self._recount()

    def move_rule(self, widget, d):
        if not self._sync_rules_from_widgets():
            self.log("PERINGATAN", "Perbaiki format aturan sebelum mengubah urutan.")
            return
        i = self.rule_widgets.index(widget)
        j = i + d
        if 0 <= j < len(self.rules):
            self.rules[i], self.rules[j] = self.rules[j], self.rules[i]
            for n, r in enumerate(self.rules, 1):
                r["no"] = n
            self._fill_rules()
            self._recount()

    def _save_rules(self):
        try:
            rules = self._collect_rules(strict=True)
        except ValueError as e:
            QMessageBox.warning(self, "Aturan", str(e))
            return
        if not confirm(self, "Simpan aturan", f"Simpan {len(rules)} aturan dan opsi ke konfigurasi lokal?", "Simpan"):
            return
        cfg = load_cfg()
        cfg["rules"] = rules
        cfg["auto"]["only_active"] = self.cb_active.isChecked()
        cfg["auto"]["merge_dupes"] = self.cb_dupes.isChecked()
        save_cfg(cfg)
        self.rules = copy.deepcopy(rules)
        self.cfg = cfg
        self.log("INFO", f"{len(rules)} aturan dan opsi disimpan.")

    def _reset_rules(self):
        if not confirm(self, "Reset aturan", "Kembalikan aturan ke bawaan? Perubahan yang belum disimpan hilang.",
                       "Reset"):
            return
        self.rules = copy.deepcopy(_DEFAULT_RULES)
        self._fill_rules()
        self._recount()
        self.log("INFO", "Aturan direset ke bawaan (belum disimpan).")

    def _recount(self):
        """Pratinjau hitungan langsung dari cache tabel kamar (tanpa I/O)."""
        self._sync_rules_from_widgets()
        if self._kamar is None:
            for w in self.rule_widgets:
                w.caption.setText("— kamar · — kosong")
            return
        cfg = self.effective_cfg()
        cnt = count_kamar(self._kamar, cfg["rules"], cfg["auto"]["only_active"], cfg["auto"]["merge_dupes"],
                          cfg["auto"].get("exclude_prefixes"))
        self._cnt = cnt
        self._apply_captions(cnt)
        self._apply_summary(cnt)

    def _apply_captions(self, cnt):
        row_keys = {(r.get("kode_kelas_aplicare"), r.get("kd_bangsal")) for r in self._apl}
        now = self.rules if len(self.rules) == len(self.rule_widgets) else [w.rule for w in self.rule_widgets]
        for w, r in zip(self.rule_widgets, now):
            a = r.get("action")
            ref = f" · ref. SK {r['ref_sk']}" if r.get("ref_sk") is not None else ""
            if a == "map":
                k = rule_target_key(r)
                t = cnt["targets"].get(k, {"kapasitas": 0, "tersedia": 0})
                extra = "" if (not self._apl or k in row_keys) else " · Belum ada baris di tabel aplicare"
                w.caption.setText(f"{t['kapasitas']} kamar · {t['tersedia']} kosong{ref}{extra}")
            elif a == "pending_row":
                p = cnt["pending"].get(r.get("no"), {"kapasitas": 0, "tersedia": 0})
                w.caption.setText(f"{p['kapasitas']} kamar · {p['tersedia']} kosong · "
                                  "Belum ada baris di tabel aplicare")
            else:
                w.caption.setText("Tidak dihitung")

    def _apply_summary(self, cnt):
        meta = load_cfg().get("rules_meta", {})
        tt = f": {meta['ref_total_tt']} TT" if meta.get("ref_total_tt") else ""
        self.summary.setText(
            f"Masuk baris tabel: {cnt['total_map']} kamar, {cnt['total_map_kosong']} kosong · "
            f"belum ada baris: {cnt['total_pending']} kamar, {cnt['total_pending_kosong']} kosong · "
            f"tidak dihitung: {len(cnt['ignored'])} kamar\n"
            f"Referensi {SK_REF}{tt}. Hanya referensi, tidak memengaruhi angka yang dikirim.")

    # ---------- muat / simulasi ----------
    def _show_empty(self, msg):
        self.table.blockSignals(True)
        self.table.clearSpans()
        self.table.setRowCount(1)
        self.table.setCellWidget(0, 0, None)
        it = QTableWidgetItem(msg)
        it.setForeground(QColor(PAL["muted"]))
        it.setTextAlignment(Qt.AlignCenter)
        it.setFlags(Qt.ItemIsEnabled)
        self.table.setItem(0, 0, it)
        self.table.setSpan(0, 0, 1, 7)
        self.table.blockSignals(False)
        self.footer.setText("0 baris")
        self._build_pager(0)

    def reload(self, silent=False, simulate=False):
        cfg = self.effective_cfg()
        if not cfg["db"].get("database"):
            self._show_empty("Belum terhubung ke SIMRS. Buka Setting → Database Connection → Test Koneksi.")
            if not silent:
                self.log("PERINGATAN", "Database SIMRS belum diisi di Setting.")
            return
        if not silent:
            self.log("INFO", "Membaca tabel kamar (hanya baca)…")
        self.set_step(1)

        def job():
            db = _db_cfg(cfg)
            return db_read_kamar(db), db_read_aplicare(db)

        BUS.run(job, lambda res, err: self._on_loaded(res, err, cfg, silent, simulate))

    def _on_loaded(self, res, err, cfg, silent, simulate):
        self.set_step(1)
        if err is not None:
            self._show_empty("Belum terhubung ke SIMRS. Buka Setting → Database Connection → Test Koneksi.")
            self.main.set_status("Gagal", "bad")
            if not silent:
                self.log("KESALAHAN", f"Gagal membaca database: {err}")
            return
        kamar, apl = res
        self._kamar, self._apl = kamar, apl
        self.main.set_status("Terhubung", "ok")
        self._plan_list, self._plan, cnt, perr = [], {}, None, None
        try:
            cnt, plan = dry_run(cfg, kamar, apl, _valid_codes(load_state()))
            self._plan_list = plan
            self._plan = {(p["kode_kelas_aplicare"], p["kd_bangsal"]): p for p in plan}
        except CycleError as e:
            perr = str(e)
            cnt = count_kamar(kamar, cfg["rules"], cfg["auto"]["only_active"], cfg["auto"]["merge_dupes"],
                              cfg["auto"].get("exclude_prefixes"))
        self._cnt = cnt
        self._checked = {k for k, p in self._plan.items() if p["aksi"] == "update"}
        self._page = 0
        self._selected_key = None
        self._render_page()
        self._apply_captions(cnt)
        self._apply_summary(cnt)
        mj = load_state().get("mjkn_terakhir")
        if self._plan_list:
            self._fill_findings(compute_findings(self._plan_list, cnt, mj, cfg))
        if not silent or simulate:
            self.log("INFO", f"{len(kamar)} baris dibaca, {len(cnt['duplicates'])} kd_kamar ganda digabung "
                             f"→ {cnt['total']} kamar unik")
            self.log("INFO", f"{len(cfg['rules'])} aturan dijalankan: {cnt['total_map']} kamar ke baris tabel, "
                             f"{cnt['total_pending']} belum punya baris, {len(cnt['ignored'])} tidak dihitung")
            for k in cnt["conflicts"]:
                self.log("PERINGATAN", f"{k}: duplikat berstatus berbeda, dihitung ISI.")
            if cnt["unmatched"]:
                self.log("PERINGATAN", f"{len(cnt['unmatched'])} kamar tidak cocok aturan: "
                                       + ", ".join(cnt["unmatched"][:15]))
            if perr:
                self.log("PERINGATAN", f"Hitung dihentikan: {perr}")
        if simulate and self._plan_list:
            self._log_simulation(cnt)

    def _log_simulation(self, cnt):
        pl = self._plan_list
        n_upd = sum(1 for p in pl if p["aksi"] == "update")
        n_same = sum(1 for p in pl if p["aksi"] == "tetap")
        inv = [p for p in pl if p["aksi"] == "tidak_valid"]
        for p in pl:
            if p["aksi"] in ("update", "tidak_valid", "tanpa_baris"):
                self.log("INFO" if p["aksi"] != "tidak_valid" else "PERINGATAN",
                         f"{p['kode_kelas_aplicare']} · {p['kd_bangsal'] or '(kosong)'}: "
                         f"{p['kapasitas_lama']}/{p['tersedia_lama']} → {p['kapasitas']}/{p['tersedia']} [{p['aksi']}]")
        for k, v in cnt["targets"].items():
            if v["kosong"]:
                self.log("INFO", f"Kosong {k[0]} · {k[1]}: " + ", ".join(v["kosong"]))
        self._sim_time = _dt.datetime.now().strftime("%H:%M")
        update_state(waktu_simulasi_terakhir=self._sim_time)
        self.refresh_status()
        names = ", ".join(p["kode_kelas_aplicare"] for p in inv)
        self.log("INFO", f"Simulasi: {n_upd} baris berubah, {n_same} tetap, {len(inv)} tidak valid"
                         f"{' (' + names + ')' if inv else ''}. Tidak ada yang ditulis.")

    def simulate(self):
        self.log("INFO", "Simulasi: membaca tabel kamar dan aplicare (tanpa menulis)…")
        self.reload(simulate=True)

    # ---------- tabel ----------
    def _rich(self, old, new, changed):
        if changed:
            return (f'<span style="color:#8A9E99"><s>{old}</s></span> '
                    f'→ <b>{new}</b>')
        return f"<b>{new}</b>"

    def _cell(self, html, tip=""):
        lab = QLabel(html)
        lab.setTextFormat(Qt.RichText)
        lab.setStyleSheet(f"background:transparent;padding-left:8px;border-bottom:1px solid {PAL['row_line']};")
        lab.setAttribute(Qt.WA_TransparentForMouseEvents)
        if tip:
            lab.setToolTip(tip)
        return lab

    def _render_page(self):
        rows = self._apl
        total = len(rows)
        self.table.blockSignals(True)
        self.table.clearSpans()
        self.table.setRowCount(0)
        if not rows:
            self.table.blockSignals(False)
            self._show_empty("Tabel kosong. Isi koneksi Database di Setting → Test Koneksi → Muat dari SIMRS.")
            return
        start = self._page * self.PAGE_SIZE
        for r in rows[start:start + self.PAGE_SIZE]:
            self.table.insertRow(self.table.rowCount())
            self._fill_row(self.table.rowCount() - 1, r)
        self.table.blockSignals(False)
        self._build_pager(total)
        self._update_footer()
        if self._selected_key is None and rows:
            self._selected_key = (rows[start].get("kode_kelas_aplicare", ""), rows[start].get("kd_bangsal", ""))
        self._show_preview(self._selected_key)

    def _fill_row(self, i, r):
        kode, kb = r.get("kode_kelas_aplicare", ""), r.get("kd_bangsal", "")
        key = (kode, kb)
        p = self._plan.get(key)
        cb = QTableWidgetItem()
        cb.setFlags(Qt.ItemIsUserCheckable | Qt.ItemIsEnabled)
        cb.setCheckState(Qt.Checked if key in self._checked else Qt.Unchecked)
        cb.setData(Qt.UserRole, key)
        self.table.setItem(i, 0, cb)
        aksi = p["aksi"] if p else None
        status_tip = {"update": "Update", "tetap": "Tetap", "tidak_valid": f"Tidak valid: {p['invalid_reason']}" if p else "",
                      "tanpa_baris": "Belum ada baris di tabel", None: "Belum dihitung"}.get(aksi, "")
        self.table.setCellWidget(i, 1, self._cell(kode, status_tip))
        if aksi == "tidak_valid":
            w = QWidget()
            w.setAttribute(Qt.WA_TransparentForMouseEvents)
            w.setObjectName("RowW")
            w.setStyleSheet(f"QWidget#RowW{{border-bottom:1px solid {PAL['row_line']};}}")
            hl = QHBoxLayout(w)
            hl.setContentsMargins(8, 0, 0, 0)
            hl.setSpacing(8)
            nm = QLabel(kb or "—")
            nm.setStyleSheet("background:transparent;border:none;")
            hl.addWidget(nm)
            badge = QLabel("Tidak valid")
            badge.setStyleSheet(f"border:1.5px solid {PAL['secondary']};border-radius:9px;padding:1px 8px;"
                                f"color:{PAL['lavender_fg']};font-size:11px;font-weight:600;background:#FFFFFF;")
            badge.setFixedHeight(22)
            badge.setToolTip(p["invalid_reason"] or "")
            hl.addWidget(badge, 0, Qt.AlignVCenter)
            hl.addStretch()
            self.table.setCellWidget(i, 2, w)
        else:
            self.table.setCellWidget(i, 2, self._cell(kb or "—", status_tip))
        self.table.setCellWidget(i, 3, self._cell(r.get("kelas", "") or "", status_tip))
        lama_k, lama_t = int(r.get("kapasitas") or 0), int(r.get("tersedia") or 0)
        if aksi == "tidak_valid":
            self.table.setCellWidget(i, 4, self._cell(f'<span style="color:#8A9E99"><s>{lama_k}</s></span>'))
            self.table.setCellWidget(i, 5, self._cell(f'<span style="color:#8A9E99"><s>{lama_t}</s></span>'))
            self.table.setCellWidget(i, 6, self._cell("—"))
        elif aksi in ("update", "tetap"):
            self.table.setCellWidget(i, 4, self._cell(self._rich(lama_k, p["kapasitas"], p["kapasitas"] != lama_k)))
            self.table.setCellWidget(i, 5, self._cell(self._rich(lama_t, p["tersedia"], p["tersedia"] != lama_t)))
            t = p["tersedia"]
            self.table.setCellWidget(i, 6, self._cell(f"{t} · {t} · {t}"))
        else:
            self.table.setCellWidget(i, 4, self._cell(f"<b>{lama_k}</b>"))
            self.table.setCellWidget(i, 5, self._cell(f"<b>{lama_t}</b>"))
            pr, wn, cp = (r.get("tersediapria"), r.get("tersediawanita"), r.get("tersediapriawanita"))
            self.table.setCellWidget(i, 6, self._cell(f"{pr} · {wn} · {cp}"))

    def _build_pager(self, total):
        while self.pager.count():
            w = self.pager.takeAt(0).widget()
            if w:
                w.deleteLater()
        pages = max(1, (total + self.PAGE_SIZE - 1) // self.PAGE_SIZE)
        prev = QPushButton("‹")
        prev.setObjectName("Page")
        prev.clicked.connect(lambda: self._go(self._page - 1))
        self.pager.addWidget(prev)
        for n in range(pages):
            b = QPushButton(str(n + 1))
            b.setObjectName("PageOn" if n == self._page else "Page")
            b.clicked.connect(lambda _=False, n=n: self._go(n))
            self.pager.addWidget(b)
        nxt = QPushButton("›")
        nxt.setObjectName("Page")
        nxt.clicked.connect(lambda: self._go(self._page + 1))
        self.pager.addWidget(nxt)

    def _go(self, n):
        pages = max(1, (len(self._apl) + self.PAGE_SIZE - 1) // self.PAGE_SIZE)
        if 0 <= n < pages and n != self._page:
            self._page = n
            self._selected_key = None
            self._render_page()

    def _update_footer(self):
        valid = [p for p in self._plan_list if p["aksi"] in ("update", "tetap")]
        kap, ter = sum(p["kapasitas"] for p in valid), sum(p["tersedia"] for p in valid)
        after = f" · setelah update: {kap} kamar, {ter} kosong terkirim dari tabel" if self._plan_list else ""
        self.footer.setText(f"{len(self._checked)} dipilih · {len(self._apl)} baris{after}")

    def _on_item_changed(self, item):
        if item.column() != 0:
            return
        key = item.data(Qt.UserRole)
        if item.checkState() == Qt.Checked:
            self._checked.add(key)
        else:
            self._checked.discard(key)
        self._update_footer()

    def _on_cell_clicked(self, row, col):
        it = self.table.item(row, 0)
        if it and it.data(Qt.UserRole):
            self._selected_key = it.data(Qt.UserRole)
            self._show_preview(self._selected_key)

    def _show_preview(self, key):
        p = self._plan.get(key) if key else None
        if not p:
            row = next((r for r in self._apl if (r.get("kode_kelas_aplicare"), r.get("kd_bangsal")) == key), None)
            if not row:
                return
            t = int(row.get("tersedia") or 0)
            self.preview.setText(f"{row.get('kode_kelas_aplicare')} · {row.get('kd_bangsal') or '—'}\n"
                                 f"kapasitas {row.get('kapasitas')} · tersedia {t}\n"
                                 f"pria {row.get('tersediapria')} · wanita {row.get('tersediawanita')} · "
                                 f"campur {row.get('tersediapriawanita')}")
            return
        t = p["tersedia"]
        self.preview.setText(f"{p['kode_kelas_aplicare']} · {p['kd_bangsal'] or '—'}\n"
                             f"kapasitas {p['kapasitas']} · tersedia {t}\n"
                             f"pria {t} · wanita {t} · campur {t}")

    def select_all(self):
        self._checked = {k for k, p in self._plan.items() if p["aksi"] in ("update", "tetap")} \
            or {(r.get("kode_kelas_aplicare"), r.get("kd_bangsal")) for r in self._apl}
        self._render_page()

    def clear_selection(self):  # hanya menghapus centang, bukan data
        self._checked = set()
        self._render_page()

    # ---------- tambah baris ----------
    def add_row(self):
        cfg = self.effective_cfg()
        if not cfg["db"].get("database"):
            QMessageBox.information(self, "Tambah baris", "Hubungkan database di Setting terlebih dahulu.")
            return
        d = QDialog(self)
        d.setWindowTitle("Tambah baris aplicare_ketersediaan_kamar")
        v = QVBoxLayout(d)
        v.setContentsMargins(22, 20, 22, 20)
        v.setSpacing(10)
        t = QLabel("Tambah baris baru")
        t.setObjectName("Heading")
        v.addWidget(t)
        s = QLabel("Baris baru akan ditulis ke tabel aplicare_ketersediaan_kamar. "
                   "Baris ini TIDAK dibuat otomatis di MJKN; entri MJKN tetap aksi manual terpisah.")
        s.setObjectName("Sub")
        s.setWordWrap(True)
        v.addWidget(s)
        w, self.e_add_kode = labeled_input("Kode Aplicare", "mis. NIC")
        v.addWidget(w)
        w, self.e_add_kb = labeled_input("Nama kamar", "mis. NICU")
        v.addWidget(w)
        w, self.e_add_kelas = labeled_input("Kelas SIMRS", "mis. Kelas VIP")
        v.addWidget(w)
        rk = QHBoxLayout()
        w, self.e_add_kap = labeled_input("Kapasitas", "0")
        rk.addWidget(w, 1)
        w, self.e_add_ter = labeled_input("Tersedia", "0")
        rk.addWidget(w, 1)
        v.addLayout(rk)
        row = QHBoxLayout()
        ok = QPushButton("Simpan baris")
        ok.setObjectName("Primary")
        ok.setMinimumHeight(42)
        ok.clicked.connect(lambda: self._do_add_row(d))
        batal = QPushButton("Batal")
        batal.setMinimumHeight(42)
        batal.clicked.connect(d.reject)
        row.addWidget(ok)
        row.addWidget(batal)
        v.addLayout(row)
        d.exec()

    def _do_add_row(self, dlg):
        kode = self.e_add_kode.text().strip()
        kb = self.e_add_kb.text().strip()
        kelas = self.e_add_kelas.text().strip()
        kap = self.e_add_kap.text().strip()
        ter = self.e_add_ter.text().strip()
        if not kode or not kb:
            QMessageBox.warning(self, "Tambah baris", "Kode Aplicare dan Nama kamar wajib diisi.")
            return
        if not kap.isdigit() or not ter.isdigit():
            QMessageBox.warning(self, "Tambah baris", "Kapasitas dan Tersedia harus angka.")
            return
        kap, ter = int(kap), int(ter)
        if ter < 0 or kap < 0 or ter > kap:
            QMessageBox.warning(self, "Tambah baris", "Harus memenuhi 0 ≤ tersedia ≤ kapasitas.")
            return
        # cegah duplikat dengan baris yang sudah ada
        exists = any((r.get("kode_kelas_aplicare") == kode and r.get("kd_bangsal") == kb)
                     for r in self._apl)
        if exists:
            QMessageBox.warning(self, "Tambah baris", "Baris dengan pasangan kode + nama kamar itu sudah ada.")
            return
        if not confirm(self, "Tambah baris",
                       f"Tulis baris “{kode}” · “{kb}” ({kelas or '-'}, {kap}/{ter}) ke tabel?\n\n"
                       "Ini adalah operasi tulis ke database.", "Simpan"):
            return
        cfg = self.effective_cfg()

        def job():
            db = _db_cfg(cfg)
            return db_insert_aplicare(db, [{"kode_kelas_aplicare": kode, "kd_bangsal": kb,
                                            "kelas": kelas, "kapasitas": kap, "tersedia": ter}])

        def done(res, err):
            if err is not None:
                self.log("KESALAHAN", f"Tambah baris gagal: {err}")
                return
            self.log("INFO", f"{res} baris ditambahkan ke tabel aplicare_ketersediaan_kamar.")
            self.reload(silent=True)

        BUS.run(job, done)
        dlg.accept()

    # ---------- hapus baris ----------
    def delete_rows(self):
        cfg = self.effective_cfg()
        if not cfg["db"].get("database"):
            QMessageBox.information(self, "Hapus baris", "Hubungkan database di Setting terlebih dahulu.")
            return
        # hanya baris tidak valid yang boleh dihapus lewat tombol ini
        keys = [k for k in self._checked if self._plan.get(k, {}).get("aksi") == "tidak_valid"]
        if not keys:
            QMessageBox.information(self, "Hapus baris",
                                    "Tidak ada baris tidak valid yang dicentang.\n\n"
                                    "Centang baris bertanda “Tidak valid” lalu klik Hapus baris.")
            return
        names = " · ".join(f"{k[0]} / {k[1] or 'kosong'}" for k in keys)
        if not confirm(self, "Hapus baris",
                       f"Hapus {len(keys)} baris tidak valid dari tabel?\n\n{names}", "Lanjut"):
            return
        if not confirm(self, "Konfirmasi hapus",
                       "Baris akan DIHAPUS permanen dari tabel aplicare_ketersediaan_kamar. "
                       "Lanjutkan?", "Hapus permanen"):
            return

        def job():
            db = _db_cfg(cfg)
            return db_delete_aplicare(db, keys)

        def done(res, err):
            if err is not None:
                self.log("KESALAHAN", f"Hapus baris gagal: {err}")
                return
            self.log("INFO", f"{res} baris tidak valid dihapus dari tabel.")
            self.reload(silent=True)

        BUS.run(job, done)

    # ---------- kirim terpilih ----------
    def send_selected(self):
        keys = [k for k in self._checked if self._plan.get(k, {}).get("aksi") in ("update", "tetap")]
        skipped = len(self._checked) - len(keys)
        if not keys:
            QMessageBox.information(self, "Kirim terpilih",
                                    "Tidak ada baris valid yang dipilih. Jalankan Simulasi atau Muat dari SIMRS dahulu.")
            return
        rows = [self._plan[k] for k in keys]
        n_write = sum(1 for p in rows if p["aksi"] == "update")
        msg = (f"Kirim {len(rows)} baris terpilih ke BPJS MJKN?\n\n"
               f"• {n_write} baris akan ditulis ke tabel aplicare_ketersediaan_kamar\n"
               f"• {len(rows)} baris akan dikirim ke MJKN")
        if skipped:
            msg += f"\n• {skipped} baris tidak valid dilewati"
        if not confirm(self, "Konfirmasi kirim", msg, "Kirim"):
            return
        cfg = self.effective_cfg()
        self.b_send.setEnabled(False)
        self.set_step(3)
        rows = [dict(p) for p in rows]

        def job():
            db = _db_cfg(cfg)
            written = db_update_aplicare(db, [{k: p[k] for k in ("kode_kelas_aplicare", "kd_bangsal", "kapasitas",
                                                                 "tersedia")} for p in rows if p["aksi"] == "update"])
            BUS.emit_log("INFO", f"Update tabel aplicare: {written} baris.")
            BUS.step.emit(4)
            sent, failed, notfound, tried = send_rows_to_bpjs(cfg, rows, BUS.emit_log)
            st = load_state()
            pend = [x for x in st.get("tertunda", []) if (x["kode_kelas_aplicare"], x["kd_bangsal"]) not in keys]
            pend += [{"kode_kelas_aplicare": k[0], "kd_bangsal": k[1]} for k in failed]
            ap = [x for x in st.get("menunggu_persetujuan", [])
                  if (x["kode_kelas_aplicare"], x["kd_bangsal"]) not in keys]
            update_state(tertunda=pend, menunggu_persetujuan=ap, waktu_siklus_terakhir=_now_str(),
                         baris_ditulis_terakhir=written)
            return written, len(sent), len(failed), tried

        def done(res, err):
            self.b_send.setEnabled(True)
            self.set_step(1)
            if err is not None:
                self.log("KESALAHAN", f"Kirim terpilih gagal: {err}")
                return
            w, s, f, tried = res
            self.log("INFO", f"Kirim terpilih selesai: {w} baris ditulis, {s} terkirim ke MJKN, {f} tertunda.")
            self.refresh_status()
            self.reload(silent=True)

        BUS.run(job, done)

    # ---------- ekspor simulasi ----------
    def export_csv(self):
        if not self._plan_list:
            QMessageBox.information(self, "Ekspor", "Belum ada hasil. Jalankan Simulasi dahulu.")
            return
        fn, _ = QFileDialog.getSaveFileName(self, "Ekspor simulasi",
                                            f"simulasi_kamar_{_dt.datetime.now():%Y%m%d_%H%M}.csv", "CSV (*.csv)")
        if not fn:
            return
        try:
            with open(fn, "w", newline="", encoding="utf-8-sig") as f:
                w = csv.writer(f)
                w.writerow(["kode_kelas_aplicare", "nama_kamar", "kelas", "kapasitas_lama", "tersedia_lama",
                            "kapasitas_baru", "tersedia_baru", "pria", "wanita", "campur", "aksi", "alasan",
                            "kamar_kosong"])
                for p in self._plan_list:
                    t = p["tersedia"]
                    w.writerow([p["kode_kelas_aplicare"], p["kd_bangsal"], p["kelas"], p["kapasitas_lama"],
                                p["tersedia_lama"], p["kapasitas"], t, t, t, t, p["aksi"],
                                p.get("invalid_reason") or "", " ".join(p.get("kosong", []))])
            self.log("INFO", f"Simulasi diekspor: {fn}")
        except Exception as e:
            self.log("KESALAHAN", f"Ekspor gagal: {e}")

    # ---------- dari penjadwal ----------
    def on_cycle_done(self, cnt, plan, by):
        self.refresh_status()
        self.reload(silent=True)


# ============================================================
# Layar "Setting"
# ============================================================
APLICARE_UPDATE_FIELDS = [
    "kodekelas · kode kelas Aplicare (harus ada di daftar kelas di atas)",
    "koderuang · nama kamar, sama dengan di tabel aplicare_ketersediaan_kamar",
    "namaruang · diambil dari data MJKN, tidak diubah",
    "kapasitas · jumlah seluruh kamar aktif",
    "tersedia · jumlah kamar berstatus KOSONG",
    "tersediapria, tersediawanita, tersediapriawanita · diisi sama dengan tersedia",
]
MAX_RUANG_TAMPIL = 60


class ScreenSetting(QWidget):
    def __init__(self, main):
        super().__init__()
        self.main = main
        self.cfg = load_cfg()
        self._build()
        self.load_values()

    def _pill(self, text, mode):
        l = QLabel(text)
        l.setStyleSheet(pill_style(mode))
        return l

    def _build(self):
        root = QVBoxLayout(self)
        root.setContentsMargins(20, 16, 20, 20)
        root.setSpacing(14)
        pills = QHBoxLayout()
        pills.setSpacing(8)
        self.pill_bpjs = self._pill("BPJS Connection: belum diuji", "outline")
        self.pill_dbtop = self._pill("Database Connection: Waiting", "outline")
        self.pill_auto = self._pill("Auto Sender: —", "ok")
        for p in (self.pill_bpjs, self.pill_dbtop, self.pill_auto):
            pills.addWidget(p)
        pills.addStretch()
        root.addLayout(pills)

        cols = QHBoxLayout()
        cols.setSpacing(16)
        cols.setAlignment(Qt.AlignTop)

        # ---- kolom kiri: BPJS + simpan
        left = QVBoxLayout()
        left.setSpacing(16)
        lc = Card(margins=22, spacing=12)
        ll = lc.body()
        k = QLabel("BPJS CONNECTION")
        k.setObjectName("Kicker")
        t = QLabel("Koneksi Aplicare")
        t.setObjectName("Heading")
        s = QLabel("Kredensial dari BPJS Kesehatan, disimpan terenkripsi di komputer ini.")
        s.setObjectName("Sub")
        for w in (k, t, s):
            ll.addWidget(w)
        w, self.e_url = labeled_input("URL API", "https://new-api.bpjs-kesehatan.go.id/aplicaresws")
        ll.addWidget(w)
        self.e_cons = SecretField("Cons ID", "Cons ID")
        self.e_secret = SecretField("Secret Key", "Secret Key")
        self.e_userkey = SecretField("User Key", "User Key")
        self.e_ppk = SecretField("Kode PPK", "Kode faskes")
        for f in (self.e_cons, self.e_secret, self.e_userkey, self.e_ppk):
            ll.addWidget(f)
        row = QHBoxLayout()
        row.setSpacing(10)
        tb = QPushButton("Test Koneksi")
        tb.setObjectName("Secondary")
        tb.setMinimumHeight(42)
        tb.clicked.connect(self.test_bpjs)
        rb = QPushButton("Reset")
        rb.setMinimumHeight(42)
        rb.clicked.connect(self.reset_bpjs)
        row.addWidget(tb)
        row.addWidget(rb)
        row.addStretch()
        ll.addLayout(row)
        cl = QLabel("Console")
        cl.setObjectName("ConsoleLabel")
        ll.addWidget(cl)
        self.c_bpjs = Console(min_h=240)
        self.c_bpjs.add("INFO", "Belum ada percobaan koneksi.")
        ll.addWidget(self.c_bpjs)
        left.addWidget(lc)

        sv = QHBoxLayout()
        sv.setSpacing(10)
        self.cb_default = QCheckBox()
        self.b_default = QPushButton("Simpan Sebagai Default")
        self.b_default.setMinimumHeight(42)
        self.b_default.clicked.connect(self.save_default)
        sv.addWidget(self.cb_default)
        sv.addWidget(self.b_default)
        sv.addStretch()
        left.addLayout(sv)
        simpan = QPushButton("Simpan")
        simpan.setObjectName("Primary")
        simpan.setMinimumHeight(42)
        simpan.setMinimumWidth(110)
        simpan.clicked.connect(self.save)
        sr = QHBoxLayout()
        sr.addWidget(simpan)
        sr.addStretch()
        left.addLayout(sr)
        left.addStretch(1)
        cols.addLayout(left, 1)

        # ---- kolom kanan: DB + Auto
        right = QVBoxLayout()
        right.setSpacing(16)
        dc = Card(margins=22, spacing=12)
        dl = dc.body()
        k2 = QLabel("DATABASE CONNECTION")
        k2.setObjectName("Kicker")
        dl.addWidget(k2)
        head = QHBoxLayout()
        t2 = QLabel("Database SIMRS")
        t2.setObjectName("Heading")
        head.addWidget(t2)
        head.addStretch()
        badge = QLabel("Hanya baca")
        badge.setStyleSheet(pill_style("idle"))
        head.addWidget(badge)
        dl.addLayout(head)
        s2 = QLabel("Aplikasi hanya boleh menulis ke tabel aplicare_ketersediaan_kamar.")
        s2.setObjectName("Sub")
        dl.addWidget(s2)
        w, self.e_host = labeled_input("Host", "127.0.0.1:3306", "127.0.0.1:3306")
        dl.addWidget(w)
        w, self.e_dbname = labeled_input("Database", "Nama database")
        dl.addWidget(w)
        w, self.e_dbuser = labeled_input("Username", "Username")
        dl.addWidget(w)
        self.e_dbpass = SecretField("Password", "Password")
        dl.addWidget(self.e_dbpass)
        r2 = QHBoxLayout()
        r2.setSpacing(10)
        tdb = QPushButton("Test Koneksi")
        tdb.setObjectName("Secondary")
        tdb.setMinimumHeight(42)
        tdb.clicked.connect(self.test_db)
        self.pill_db = QLabel("Waiting")
        self.pill_db.setStyleSheet(pill_style("idle"))
        r2.addWidget(tdb)
        r2.addWidget(self.pill_db)
        r2.addStretch()
        dl.addLayout(r2)
        cl2 = QLabel("Console")
        cl2.setObjectName("ConsoleLabel")
        dl.addWidget(cl2)
        self.c_db = Console(min_h=110)
        self.c_db.add("INFO", "Menunggu — tekan Test Koneksi.")
        dl.addWidget(self.c_db)
        right.addWidget(dc)

        ac = Card(margins=22, spacing=12)
        al = ac.body()
        k3 = QLabel("AUTO SENDER SETTINGS")
        k3.setObjectName("Kicker")
        t3 = QLabel("Kirim otomatis")
        t3.setObjectName("Heading")
        s3 = QLabel("Jadwal siklus: baca tabel kamar, hitung, update tabel, kirim ke MJKN.")
        s3.setObjectName("Sub")
        for w in (k3, t3, s3):
            al.addWidget(w)
        r3 = QHBoxLayout()
        r3.setSpacing(14)
        self.cb_auto = QCheckBox("Kirim otomatis")
        self.sp_interval = QSpinBox()
        self.sp_interval.setRange(1, 1440)
        self.sp_interval.setPrefix("Setiap ")
        self.sp_interval.setSuffix(" menit")
        self.sp_interval.setButtonSymbols(QSpinBox.NoButtons)
        self.sp_interval.setMinimumHeight(44)
        r3.addWidget(self.cb_auto, 1)
        r3.addWidget(self.sp_interval, 1)
        al.addLayout(r3)
        el = QLabel("Kecualikan nama kamar (satu per baris)")
        el.setObjectName("FieldLabel")
        al.addWidget(el)
        self.t_exc = QTextEdit()
        self.t_exc.setMinimumHeight(110)
        self.t_exc.setMaximumHeight(120)
        self.t_exc.setPlaceholderText("Contoh: C-IGD-INT")
        al.addWidget(self.t_exc)
        r4 = QHBoxLayout()
        r4.setSpacing(14)
        self.cb_retry = QCheckBox("Ulangi jika gagal")
        self.sp_retry = QSpinBox()
        self.sp_retry.setRange(1, 10)
        self.sp_retry.setSuffix(" kali")
        self.sp_retry.setButtonSymbols(QSpinBox.NoButtons)
        self.sp_retry.setMinimumHeight(44)
        r4.addWidget(self.cb_retry, 1)
        r4.addWidget(self.sp_retry, 1)
        al.addLayout(r4)
        self.cb_only = QCheckBox("Hanya kirim jika ada perubahan")
        self.cb_approve = QCheckBox("Perubahan kapasitas perlu persetujuan sebelum dikirim")
        self.cb_tray = QCheckBox("Minimalkan ke ikon tray saat jendela ditutup")
        for c in (self.cb_only, self.cb_approve, self.cb_tray):
            al.addWidget(c)
        right.addWidget(ac)
        right.addStretch(1)
        cols.addLayout(right, 1)
        root.addLayout(cols, 1)

    # ---------- data ----------
    def load_values(self):
        cfg = load_cfg()
        self.cfg = cfg
        bp, db, au = cfg["bpjs"], cfg["db"], cfg["auto"]
        self.e_url.setText(bp.get("base_url", ""))
        self.e_cons.edit.setText(bp.get("cons_id", ""))
        self.e_ppk.edit.setText(bp.get("kode_ppk", ""))
        self.e_secret.edit.clear()
        self.e_userkey.edit.clear()
        self.e_dbpass.edit.clear()
        saved = "Tersimpan (kosongkan untuk tidak mengubah)"
        self.e_secret.edit.setPlaceholderText(saved if bp.get("secret_key_enc") else "Secret Key")
        self.e_userkey.edit.setPlaceholderText(saved if bp.get("user_key_enc") else "User Key")
        self.e_dbpass.edit.setPlaceholderText(saved if db.get("password_enc") else "Password")
        self.e_host.setText(f"{db.get('host', '127.0.0.1')}:{db.get('port', 3306)}")
        self.e_dbname.setText(db.get("database", ""))
        self.e_dbuser.setText(db.get("username", ""))
        self.cb_auto.setChecked(au["enabled"])
        self.sp_interval.setValue(max(1, int(au["interval_min"])))
        self.t_exc.setPlainText("\n".join(au.get("exclude_prefixes") or []))
        self.cb_retry.setChecked(au["retry"] > 0)
        self.sp_retry.setValue(max(1, int(au["retry"] or 3)))
        self.cb_only.setChecked(au["only_if_changed"])
        self.cb_approve.setChecked(au["require_approval_on_kapasitas"])
        self.cb_tray.setChecked(cfg.get("ui", {}).get("minimize_to_tray", True))
        self.update_auto_pill()

    def update_auto_pill(self):
        if self.cb_auto.isChecked():
            self.pill_auto.setText(f"Auto Sender: aktif, setiap {self.sp_interval.value()} menit")
            self.pill_auto.setStyleSheet(pill_style("ok"))
        else:
            self.pill_auto.setText("Auto Sender: nonaktif")
            self.pill_auto.setStyleSheet(pill_style("idle"))

    def _db_from_form(self):
        host, _, port = self.e_host.text().strip().partition(":")
        pw = self.e_dbpass.text() or dec_secret(load_cfg()["db"].get("password_enc", ""))
        return {"host": host or "127.0.0.1", "port": int(port) if port.isdigit() else 3306,
                "database": self.e_dbname.text().strip(), "username": self.e_dbuser.text().strip(),
                "password": pw}

    def reset_bpjs(self):
        self.load_values()
        self.c_bpjs.add("INFO", "Isian dikembalikan ke nilai tersimpan.")

    # ---------- uji koneksi ----------
    def test_bpjs(self):
        bp = load_cfg()["bpjs"]
        secret = self.e_secret.text() or dec_secret(bp.get("secret_key_enc", ""))
        ukey = self.e_userkey.text() or dec_secret(bp.get("user_key_enc", ""))
        cons = self.e_cons.text().strip()
        if not cons or not secret or not ukey:
            missing = []
            if not cons:
                missing.append("Cons ID Aplicare")
            if not secret:
                missing.append("Secret Key Aplicare")
            if not ukey:
                missing.append("User Key Aplicare")
            self.c_bpjs.add("PERINGATAN", "Kredensial Aplicare belum lengkap: " + ", ".join(missing) + ".")
            return
        try:
            tmp = {**bp, "base_url": self.e_url.text().strip() or bp.get("base_url", ""),
                   "cons_id": cons, "secret_key_enc": enc_secret(secret), "user_key_enc": enc_secret(ukey),
                   "kode_ppk": self.e_ppk.text().strip()}
        except OSError as e:
            self.c_bpjs.add("KESALAHAN", f"Enkripsi gagal: {e}")
            return
        self.c_bpjs.add("INFO", "Menguji koneksi BPJS (baca referensi kelas)…")

        def job():  # hanya membaca (GET); tidak ada yang dikirim atau diubah
            c = BpjsClient(tmp)
            res = c.ref_kelas()
            out = {"ok": c.ok(res), "msg": c.message(res), "kelas": [], "ruang": None,
                   "ruang_err": "", "ppk": bool(tmp.get("kode_ppk"))}
            if not out["ok"]:
                return out
            out["kelas"] = c._items(res)
            if not out["ppk"]:
                return out
            try:
                out["ruang"] = c.read_all()
            except RuntimeError as e:
                out["ruang_err"] = str(e)
            except Exception as e:
                out["ruang_err"] = type(e).__name__
            return out

        def done(res, err):
            if err is not None:
                self.c_bpjs.add("KESALAHAN", f"Gagal: {type(err).__name__}")
                self.pill_bpjs.setText("BPJS Connection: gagal")
                self.pill_bpjs.setStyleSheet(pill_style("bad"))
                return
            ok = res["ok"]
            self.c_bpjs.add("INFO" if ok else "PERINGATAN",
                            f"{res['msg']}" + (f" · {len(res['kelas'])} kelas" if ok else ""))
            self.pill_bpjs.setText("BPJS Connection: terhubung" if ok else "BPJS Connection: gagal")
            self.pill_bpjs.setStyleSheet(pill_style("ok" if ok else "bad"))
            if ok:
                self._show_aplicare_data(res)

        BUS.run(job, done)

    def _show_aplicare_data(self, res):
        """Tampilkan data yang dikenal/diminta Aplicare: kelas, ruang terdaftar, dan field update."""
        c = self.c_bpjs
        kelas = [f"{k.get('kodekelas') or '?'} · {k.get('namakelas') or k.get('nama') or ''}".rstrip(" ·")
                 for k in res["kelas"]]
        c.add_block("INFO", f"Kelas yang dikenal Aplicare ({len(kelas)}):", kelas or ["(kosong)"])
        if not res["ppk"]:
            c.add("INFO", "Isi Kode PPK untuk melihat ruang yang terdaftar di MJKN.")
        elif res["ruang"] is None:
            c.add("PERINGATAN", f"Ruang terdaftar di MJKN tidak terbaca: {res['ruang_err']}")
        else:
            ruang = res["ruang"]
            lines = [f"{r.get('kodekelas') or '?'} · {r.get('koderuang') or '?'} · {r.get('namaruang') or ''}"
                     f" · kapasitas {r.get('kapasitas', '?')} / tersedia {r.get('tersedia', '?')}"
                     for r in ruang[:MAX_RUANG_TAMPIL]]
            if len(ruang) > MAX_RUANG_TAMPIL:
                lines.append(f"… dan {len(ruang) - MAX_RUANG_TAMPIL} ruang lainnya")
            c.add_block("INFO", f"Ruang terdaftar di MJKN untuk Kode PPK ini ({len(ruang)}):",
                        lines or ["(belum ada ruang terdaftar)"])
        c.add_block("INFO", "Data yang diminta Aplicare saat update (per ruang):", APLICARE_UPDATE_FIELDS)
        c.add("INFO", "Hanya ruang yang sudah terdaftar di MJKN yang bisa di-update; aplikasi tidak membuat atau menghapus ruang.")

    def test_db(self):
        db = self._db_from_form()
        self.c_db.add("INFO", "Menguji koneksi database…")
        self.pill_db.setText("Waiting")
        self.pill_db.setStyleSheet(pill_style("idle"))

        def job():
            db_fetch(db, "SELECT 1")
            warns = grant_warnings(db_check_grants(db))
            try:
                cols = [r.get("Field") for r in db_describe_aplicare(db)]
            except Exception as e:  # noqa: BLE001
                cols = f"DESCRIBE gagal: {e}"
            return warns, cols

        def done(res, err):
            if err is not None:
                self.pill_db.setText("Gagal")
                self.pill_db.setStyleSheet(pill_style("bad"))
                self.pill_dbtop.setText("Database Connection: gagal")
                self.pill_dbtop.setStyleSheet(pill_style("bad"))
                self.c_db.add("KESALAHAN", f"Gagal: {err}")
                self.main.set_status("Gagal", "bad")
                return
            warns, cols = res
            self.pill_db.setText("Terhubung")
            self.pill_db.setStyleSheet(pill_style("ok"))
            self.pill_dbtop.setText("Database Connection: terhubung")
            self.pill_dbtop.setStyleSheet(pill_style("ok"))
            self.main.set_status("Terhubung", "ok")
            self.c_db.add("INFO", "Terhubung ke SIMRS (transaksi hanya baca).")
            if isinstance(cols, list):
                self.c_db.add("INFO", f"Kolom {ALLOWED_WRITE_TABLE}: {', '.join(map(str, cols))}")
            else:
                self.c_db.add("PERINGATAN", cols)
            for g in warns:
                self.c_db.add("PERINGATAN", f"Hak tulis di luar kebijakan: {g}")

        BUS.run(job, done)

    # ---------- simpan ----------
    def _write_form(self, cfg):
        if self.e_secret.text():
            cfg["bpjs"]["secret_key_enc"] = enc_secret(self.e_secret.text())
        if self.e_userkey.text():
            cfg["bpjs"]["user_key_enc"] = enc_secret(self.e_userkey.text())
        cfg["bpjs"]["base_url"] = self.e_url.text().strip()
        cfg["bpjs"]["cons_id"] = self.e_cons.text().strip()
        cfg["bpjs"]["kode_ppk"] = self.e_ppk.text().strip()
        host, _, port = self.e_host.text().strip().partition(":")
        cfg["db"].update({"host": host or "127.0.0.1", "port": int(port) if port.isdigit() else 3306,
                          "database": self.e_dbname.text().strip(), "username": self.e_dbuser.text().strip()})
        if self.e_dbpass.text():
            cfg["db"]["password_enc"] = enc_secret(self.e_dbpass.text())
        cfg["auto"].update({
            "enabled": self.cb_auto.isChecked(), "interval_min": self.sp_interval.value(),
            "exclude_prefixes": [s.strip() for s in self.t_exc.toPlainText().splitlines() if s.strip()],
            "retry": self.sp_retry.value() if self.cb_retry.isChecked() else 0,
            "only_if_changed": self.cb_only.isChecked(),
            "require_approval_on_kapasitas": self.cb_approve.isChecked()})
        cfg.setdefault("ui", {})["minimize_to_tray"] = self.cb_tray.isChecked()
        return cfg

    def save(self):
        if not confirm(self, "Simpan pengaturan", "Simpan pengaturan koneksi dan pengiriman otomatis? "
                       "Rahasia disimpan terenkripsi.", "Simpan"):
            return
        try:
            cfg = self._write_form(load_cfg())
        except OSError as e:
            QMessageBox.critical(self, "Setting", f"Enkripsi rahasia gagal: {e}")
            return
        save_cfg(cfg)
        if self.cb_default.isChecked():
            _atomic_write(_default_profile_path(), json.dumps(cfg, ensure_ascii=False, indent=2))
        self.load_values()
        self.main.screen_kirim.refresh_status()
        QMessageBox.information(self, "Setting", "Pengaturan tersimpan.")

    def save_default(self):
        if not confirm(self, "Simpan sebagai default",
                       "Simpan isian saat ini sebagai profil default (config.default.json)?", "Simpan"):
            return
        try:
            cfg = self._write_form(load_cfg())
            _atomic_write(_default_profile_path(), json.dumps(cfg, ensure_ascii=False, indent=2))
            self.c_bpjs.add("INFO", "Profil default disimpan.")
        except Exception as e:  # noqa: BLE001
            QMessageBox.critical(self, "Setting", f"Gagal: {e}")


# ============================================================
# Jendela utama
# ============================================================
class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle(APP_TITLE)
        self.setWindowIcon(QIcon(logo_pixmap(64)))
        self.resize(1500, 980)
        self.setMinimumSize(1180, 700)
        self._quitting = False
        self._build()
        self._build_tray()
        BUS.log.connect(self.screen_kirim.log)
        BUS.step.connect(self.screen_kirim.set_step)
        BUS.cycle_done.connect(self.screen_kirim.on_cycle_done)
        self.scheduler = Scheduler(log_fn=BUS.emit_log, step_fn=BUS.step.emit,
                                   done_fn=lambda c, p, b: BUS.cycle_done.emit(c, p, b))
        QTimer.singleShot(1200, self.scheduler.start)
        QTimer.singleShot(900, self._check_grants)

    def _build(self):
        root = QWidget()
        root.setObjectName("Root")
        self.setCentralWidget(root)
        lay = QVBoxLayout(root)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(0)
        header = QFrame()
        header.setObjectName("Header")
        hl = QHBoxLayout(header)
        hl.setContentsMargins(20, 12, 20, 12)
        hl.setSpacing(12)
        logo = QLabel()
        logo.setPixmap(logo_pixmap(44))
        logo.setFixedSize(44, 44)
        hl.addWidget(logo)
        vt = QVBoxLayout()
        vt.setSpacing(0)
        tt = QLabel(APP_TITLE)
        tt.setObjectName("Title")
        st = QLabel(APP_SUB)
        st.setObjectName("Sub")
        vt.addWidget(tt)
        vt.addWidget(st)
        hl.addLayout(vt)
        hl.addStretch()
        self.b_kirim = QPushButton("Kirim data")
        self.b_kirim.setToolTip("Klik lagi saat di layar ini untuk menjalankan satu siklus sekarang")
        self.b_set = QPushButton("Setting")
        for b in (self.b_kirim, self.b_set):
            b.setMinimumHeight(42)
            b.setMinimumWidth(104)
        self.pill = QLabel("Belum diuji")
        self.pill.setObjectName("Pill")
        hl.addWidget(self.b_kirim)
        hl.addWidget(self.b_set)
        hl.addWidget(self.pill)
        lay.addWidget(header)

        self.stack = QStackedWidget()
        self.screen_kirim = ScreenKirim(self)
        self.screen_setting = ScreenSetting(self)
        self.stack.addWidget(wrap_scroll(self.screen_kirim))
        self.stack.addWidget(wrap_scroll(self.screen_setting))
        lay.addWidget(self.stack, 1)
        self.b_kirim.clicked.connect(self._on_kirim)
        self.b_set.clicked.connect(lambda: self._nav(1))
        self._nav(0)

    def _nav(self, idx):
        self.stack.setCurrentIndex(idx)
        for b, on in ((self.b_kirim, idx == 0), (self.b_set, idx == 1)):
            b.setObjectName("Primary" if on else "")
            b.style().unpolish(b)
            b.style().polish(b)
        if idx == 0:
            self.screen_kirim.refresh_status()

    def _on_kirim(self):
        if self.stack.currentIndex() != 0:
            self._nav(0)
            return
        n = sum(1 for p in self.screen_kirim._plan_list if p["aksi"] == "update"
                and not needs_approval(p, load_cfg()))
        if confirm(self, "Jalankan siklus sekarang",
                   f"Jalankan satu siklus sekarang?\n\nBaris yang berubah (±{n} baris pada hasil terakhir) ditulis "
                   "ke tabel aplicare_ketersediaan_kamar lalu dikirim ke BPJS MJKN.", "Jalankan"):
            self.scheduler.run_now("manual")

    def set_status(self, text, mode):
        self.pill.setText(text)
        self.pill.setStyleSheet(pill_style(mode))

    def _check_grants(self):
        cfg = load_cfg()
        if not cfg["db"].get("database"):
            return

        def job():
            return grant_warnings(db_check_grants(_db_cfg(cfg)))

        def done(res, err):
            if err is not None or not res:
                return
            for g in res:
                msg = f"Hak tulis di luar kebijakan: {g}"
                BUS.emit_log("PERINGATAN", msg)
                self.screen_setting.c_db.add("PERINGATAN", msg)

        BUS.run(job, done)

    # ---------- tray ----------
    def _build_tray(self):
        self.tray = None
        if not QSystemTrayIcon.isSystemTrayAvailable():
            return
        self.tray = QSystemTrayIcon(QIcon(logo_pixmap(64)), self)
        self.tray.setToolTip(APP_TITLE)
        menu = QMenu()
        a_open = QAction("Buka", self)
        a_open.triggered.connect(self._restore)
        a_quit = QAction("Keluar", self)
        a_quit.triggered.connect(self._quit)
        menu.addAction(a_open)
        menu.addAction(a_quit)
        self.tray.setContextMenu(menu)
        self.tray.activated.connect(lambda r: self._restore() if r == QSystemTrayIcon.Trigger else None)
        self.tray.show()

    def _restore(self):
        self.showNormal()
        self.raise_()
        self.activateWindow()

    def _quit(self):
        self._quitting = True
        self.close()
        QApplication.quit()

    def closeEvent(self, e):
        if (not self._quitting and self.tray is not None
                and load_cfg().get("ui", {}).get("minimize_to_tray", True)):
            e.ignore()
            self.hide()
            self.tray.showMessage(APP_TITLE, "Aplikasi tetap berjalan di tray. Klik kanan ikon → Keluar untuk menutup.",
                                  QSystemTrayIcon.Information, 3000)
            return
        self.scheduler.stop()
        e.accept()


# ============================================================
# Entry point
# ============================================================
def _single_instance():
    shm = QSharedMemory(APP_NAME)
    if shm.attach():
        shm.detach()
        return None
    return shm if shm.create(1) else None


def _load_font() -> str:
    cands = [Path(__file__).parent / "assets" / "NotoSansDevanagari-Regular.ttf"]
    if hasattr(sys, "_MEIPASS"):
        cands.append(Path(sys._MEIPASS) / "assets" / "NotoSansDevanagari-Regular.ttf")
    for p in cands:
        if p.exists():
            QFontDatabase.addApplicationFont(str(p))
            break
    fams = QFontDatabase.families()
    return "Noto Sans Devanagari" if "Noto Sans Devanagari" in fams else "Segoe UI"


def main():
    global BUS
    setup_logging()
    app = QApplication(sys.argv)
    app.setApplicationName(APP_NAME)
    app.setQuitOnLastWindowClosed(False)
    shm = _single_instance()  # simpan referensi selama aplikasi hidup
    if shm is None:
        QMessageBox.warning(None, APP_TITLE, "Aplikasi sudah berjalan.")
        return 1
    fam = _load_font()
    app.setStyleSheet(build_qss())
    app.setFont(QFont(fam, 10))
    BUS = Bus()
    win = MainWindow()
    win.show()
    rc = app.exec()
    try:
        win.scheduler.stop()
    except Exception:
        pass
    return rc


if __name__ == "__main__":
    sys.exit(main())