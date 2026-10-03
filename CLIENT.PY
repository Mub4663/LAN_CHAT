# ─────────────────────────────────────────────────────────────────────────────
# LAN Chat Client 
# ─────────────────────────────────────────────────────────────────────────────
import socket, threading, tkinter as tk
from tkinter import filedialog, messagebox
from datetime import datetime, date
import uuid, os, hashlib, time, subprocess, json
from PIL import Image, ImageTk, ImageDraw

try:    import simpleaudio as sa;  USE_SA = True
except: USE_SA = False

try:    from playsound import playsound
except: playsound = None

try:
    import sounddevice as sd, soundfile as sf, numpy as np
    HAS_AUDIO = True
except: HAS_AUDIO = False

# ── PATHS ─────────────────────────────────────────────────────────────────────
BASE       = os.path.abspath(".")
RECV_DIR   = os.path.join(BASE, "files", "received")
VOICE_DIR  = os.path.join(BASE, "files", "voice")
AVATAR_DIR = os.path.join(BASE, "files", "avatars")
for _d in [RECV_DIR, VOICE_DIR, AVATAR_DIR]:
    os.makedirs(_d, exist_ok=True)

READSTATE_DIR = os.path.join(BASE, "files", "readstate")
os.makedirs(READSTATE_DIR, exist_ok=True)

PORT      = 5000
DISC_PORT = 5001
MIN_PW    = 6
SR = 16000; CH = 1; MAX_SEC = 60

def gid():   return str(uuid.uuid4())
def shpw(p): return hashlib.sha256(p.encode()).hexdigest()

COLORS = ["#E74C3C","#3498DB","#2ECC71","#9B59B6","#F39C12",
          "#1ABC9C","#E67E22","#E91E63","#00BCD4","#FF5722"]

THEMES = {
    "light": {
        "bg":     "#f0f2f5",  "chat_bg": "#e5ddd5",
        "mine":   "#dcf8c6",  "other":   "#ffffff",
        "priv":   "#fff3cd",  "text":    "#111111",
        "time":   "#667781",  "acc":     "#075e54",
        "acc2":   "#25d366",  "panel":   "#ffffff",
        "ptxt":   "#111111",  "ibg":     "#ffffff",
        "sepbg":  "#d9d9d9",  "sepfg":   "#555555",
        "sel":    "#f0f2f5",  "hdr":     "#075e54",
    },
    "dark": {
        "bg":     "#0b1417",  "chat_bg": "#1f2c34",
        "mine":   "#056162",  "other":   "#243036",
        "priv":   "#3a3000",  "text":    "#eaeaea",
        "time":   "#c2c2c2",  "acc":     "#00a884",
        "acc2":   "#00a884",  "panel":   "#1f2c34",
        "ptxt":   "#eaeaea",  "ibg":     "#2a3942",
        "sepbg":  "#33444d",  "sepfg":   "#aaaaaa",
        "sel":    "#2a3942",  "hdr":     "#1f2c34",
    },
}
theme = "light"
def T(): return THEMES[theme]

# ── GLOBALS ───────────────────────────────────────────────────────────────────
tcp          = None
server_ip    = ""
username     = None
current_chat = "Group"

# message store
msg_store    = {}          # mid -> msg dict
chat_lists   = {"Group": []}  # chat_key -> [mid, ...]
unread       = {}          # chat_key -> count
online_users = []

# ── PERSISTED READ-STATE ──────────────────────────────────────────────────────
# Tracks the last time THIS user actually opened each chat, saved to a small
# local JSON file per-username so unread counts don't reset to "unread" again
# after logout/login for messages the user has already seen in a past session.
_read_state = {}   # chat_key -> last-read ISO timestamp

def _read_state_path():
    if not username: return None
    safe = "".join(c for c in username if c.isalnum() or c in "_-")
    return os.path.join(READSTATE_DIR, f"{safe}.json")

def _load_read_state():
    global _read_state
    p = _read_state_path()
    if not p or not os.path.exists(p):
        _read_state = {}
        return
    try:
        with open(p, "r", encoding="utf-8") as f:
            _read_state = json.load(f)
    except Exception:
        _read_state = {}

def _save_read_state():
    p = _read_state_path()
    if not p: return
    try:
        with open(p, "w", encoding="utf-8") as f:
            json.dump(_read_state, f)
    except Exception:
        pass
avatar_cache = {}
typing_jobs  = {}
date_shown   = {}
reply_mid    = None
recording    = False
rec_frames   = []
rec_stream   = None
rec_start    = 0

# ── ROOT WINDOW ───────────────────────────────────────────────────────────────
root = tk.Tk()
root.title("LAN Chat")
root.geometry("1200x740")
root.minsize(900, 540)

# ══════════════════════════════════════════════════════════════════════════════
# AUTH SCREEN  — sits on top until login succeeds
# ══════════════════════════════════════════════════════════════════════════════
auth_frame = tk.Frame(root)
auth_frame.place(relx=0, rely=0, relwidth=1, relheight=1)

# ── Login card ────────────────────────────────────────────────────────────────
login_card = tk.Frame(auth_frame, bd=2, relief=tk.GROOVE)
login_card.place(relx=0.5, rely=0.5, anchor="center", width=440, height=330)

tk.Label(login_card, text="💬 LAN Chat",
         font=("Segoe UI", 16, "bold"), fg="#075e54").pack(pady=(20, 4))
tk.Label(login_card, text="Connect to your local network",
         font=("Segoe UI", 9), fg="#888").pack()
tk.Frame(login_card, height=10).pack()

_lf = tk.Frame(login_card, padx=40); _lf.pack(fill=tk.X)

def _entry(parent, label, show=None):
    tk.Label(parent, text=label,
             font=("Segoe UI", 9), anchor="w").pack(fill=tk.X, pady=(5, 0))
    e = tk.Entry(parent, font=("Segoe UI", 10), relief=tk.SOLID, bd=1)
    if show: e.config(show=show)
    e.pack(fill=tk.X, ipady=5)
    return e

l_ip = _entry(_lf, "Server IP  (blank = auto-discover)")
l_u  = _entry(_lf, "Username")
l_p  = _entry(_lf, "Password", show="*")

l_status = tk.Label(login_card, text="", font=("Segoe UI", 9))
l_status.pack(pady=(6, 2))

_lb = tk.Frame(login_card, padx=40); _lb.pack(fill=tk.X, pady=6)

# ── Register card (shown when Register clicked) ───────────────────────────────
reg_card = tk.Frame(auth_frame, bd=2, relief=tk.GROOVE)

tk.Label(reg_card, text="📝 Create Account",
         font=("Segoe UI", 14, "bold"), fg="#075e54").pack(pady=(18, 4))

_rf = tk.Frame(reg_card, padx=36); _rf.pack(fill=tk.X)

r_u  = _entry(_rf, "Username  (min 3 chars, letters / numbers / _ / -)")
r_fn = _entry(_rf, "First Name")
r_ln = _entry(_rf, "Last Name")
r_p  = _entry(_rf, "Password  (min 6 characters)", show="*")
r_p2 = _entry(_rf, "Confirm Password", show="*")

_rav = [None]
_rav_lbl = tk.Label(_rf, text="📷 No profile picture selected",
                    font=("Segoe UI", 8), fg="#888")
_rav_lbl.pack(anchor="w", pady=(4, 0))
_rav_preview = [None]  # holds PhotoImage reference
_rav_img_lbl = tk.Label(_rf, bg="white")
_rav_img_lbl.pack(anchor="w", pady=(2, 0))

def _pick_avatar():
    f = filedialog.askopenfilename(
        filetypes=[("Images", "*.png *.jpg *.jpeg")])
    if f:
        _rav[0] = f
        _rav_lbl.config(
            text="✅  " + os.path.basename(f), fg="#075e54",
            font=("Segoe UI", 8, "bold"))
        try:
            img = Image.open(f); img.thumbnail((48, 48))
            ph  = ImageTk.PhotoImage(img)
            _rav_preview[0] = ph
            _rav_img_lbl.config(image=ph)
        except: pass

tk.Button(_rf, text="📷  Upload Profile Picture (optional)",
          command=_pick_avatar, relief=tk.FLAT,
          bg="#1a73e8", fg="white",
          font=("Segoe UI", 9, "bold"), cursor="hand2",
          padx=8, pady=4).pack(anchor="w", pady=(4, 0))

r_status = tk.Label(reg_card, text="", font=("Segoe UI", 9))
r_status.pack(pady=(4, 0))

_rb = tk.Frame(reg_card, padx=36); _rb.pack(fill=tk.X, pady=6)

def show_reg():
    reg_card.place(relx=0.5, rely=0.5, anchor="center", width=480, height=540)
    login_card.place_forget()

def hide_reg():
    reg_card.place_forget()
    login_card.place(relx=0.5, rely=0.5, anchor="center", width=440, height=330)

tk.Button(_rb, text="← Back to Login", command=hide_reg,
          relief=tk.FLAT, bg="#e0e0e0",
          font=("Segoe UI", 9), padx=10, cursor="hand2").pack(side=tk.LEFT)

# ══════════════════════════════════════════════════════════════════════════════
# MAIN CHAT UI
# ══════════════════════════════════════════════════════════════════════════════
paned = tk.PanedWindow(root, orient=tk.HORIZONTAL,
                       sashwidth=5, sashrelief=tk.RAISED)
# packed AFTER login

sidebar   = tk.Frame(paned, width=270); paned.add(sidebar,   minsize=180)
main_area = tk.Frame(paned);            paned.add(main_area, minsize=500)

# ── Sidebar ───────────────────────────────────────────────────────────────────
sb_top = tk.Frame(sidebar); sb_top.pack(fill=tk.X, padx=8, pady=8)
av_lbl = tk.Label(sb_top);  av_lbl.pack(side=tk.LEFT)
nick_lbl = tk.Label(sb_top, font=("Segoe UI", 10, "bold"))
nick_lbl.pack(side=tk.LEFT, padx=6)
theme_btn = tk.Button(sb_top, text="🌗", relief=tk.FLAT,
                      cursor="hand2", width=3)
theme_btn.pack(side=tk.RIGHT)
netstat_btn = tk.Button(sb_top, text="📶", relief=tk.FLAT,
                        cursor="hand2", width=3)
netstat_btn.pack(side=tk.RIGHT)
logout_btn = tk.Button(sb_top, text="⏏ Logout", relief=tk.FLAT,
                       font=("Segoe UI", 8), bg="#e74c3c",
                       fg="white", padx=6, cursor="hand2")
logout_btn.pack(side=tk.RIGHT, padx=(0, 4))

conv_canvas = tk.Canvas(sidebar, highlightthickness=0)
conv_scroll = tk.Scrollbar(sidebar, orient=tk.VERTICAL,
                            command=conv_canvas.yview)
conv_canvas.configure(yscrollcommand=conv_scroll.set)
conv_inner  = tk.Frame(conv_canvas)
conv_win    = conv_canvas.create_window((0, 0), window=conv_inner, anchor="nw")
conv_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
conv_scroll.pack(side=tk.RIGHT, fill=tk.Y)
conv_canvas.bind("<Configure>",
    lambda e: conv_canvas.itemconfig(conv_win, width=e.width))
conv_inner.bind("<Configure>",
    lambda e: conv_canvas.configure(
        scrollregion=conv_canvas.bbox("all")))

# ── Header ────────────────────────────────────────────────────────────────────
hdr = tk.Frame(main_area, height=56)
hdr.pack(fill=tk.X); hdr.pack_propagate(False)
hdr_av_wrap = tk.Frame(hdr, width=38, height=38)
hdr_av_wrap.pack_propagate(False)
hdr_av_wrap.pack(side=tk.LEFT, padx=(12, 6), pady=8)
hdr_av   = tk.Label(hdr_av_wrap); hdr_av.place(x=0, y=0)
hdr_av_badge = tk.Canvas(hdr_av_wrap, width=12, height=12, highlightthickness=0)
hdr_av_badge.place(relx=1.0, rely=1.0, anchor="se")
hdr_info = tk.Frame(hdr);  hdr_info.pack(side=tk.LEFT, pady=8)
hdr_name = tk.Label(hdr_info, text="Group Chat",
                    font=("Segoe UI", 11, "bold"))
hdr_name.pack(anchor="w")
hdr_sub  = tk.Label(hdr_info, text="", font=("Segoe UI", 8))
hdr_sub.pack(anchor="w")
srch_btn = tk.Button(hdr, text="🔍", relief=tk.FLAT,
                     cursor="hand2", width=3)
srch_btn.pack(side=tk.RIGHT, padx=8)

# ── Search bar (hidden by default) ───────────────────────────────────────────
srch_bar = tk.Frame(main_area)
srch_e   = tk.Entry(srch_bar, font=("Segoe UI", 10),
                    relief=tk.SOLID, bd=1)
srch_e.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=6, ipady=4)
tk.Button(srch_bar, text="✕", relief=tk.FLAT,
          command=lambda: srch_bar.pack_forget()).pack(side=tk.RIGHT, padx=4)

# ── Chat canvas ───────────────────────────────────────────────────────────────
chat_fr = tk.Frame(main_area); chat_fr.pack(fill=tk.BOTH, expand=True)
canvas  = tk.Canvas(chat_fr, highlightthickness=0)
vscroll = tk.Scrollbar(chat_fr, orient=tk.VERTICAL, command=canvas.yview)
canvas.configure(yscrollcommand=vscroll.set)
msgs_frame = tk.Frame(canvas)
msgs_win   = canvas.create_window((0, 0), window=msgs_frame, anchor="nw")
canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
vscroll.pack(side=tk.RIGHT, fill=tk.Y)
canvas.bind("<Configure>",
    lambda e: canvas.itemconfig(msgs_win, width=e.width))
msgs_frame.bind("<Configure>",
    lambda e: canvas.configure(scrollregion=canvas.bbox("all")))

# ── Typing indicator ──────────────────────────────────────────────────────────
typing_lbl = tk.Label(main_area, text="",
                      font=("Segoe UI", 8, "italic"), anchor="w")
typing_lbl.pack(fill=tk.X, padx=14)

# ── Reply bar (hidden by default) ────────────────────────────────────────────
reply_var = tk.StringVar()
reply_bar = tk.Frame(main_area)
tk.Label(reply_bar, text="↩", font=("Segoe UI", 11)).pack(side=tk.LEFT, padx=6)
reply_lbl = tk.Label(reply_bar, textvariable=reply_var,
                     font=("Segoe UI", 9), anchor="w")
reply_lbl.pack(side=tk.LEFT, fill=tk.X, expand=True)
tk.Button(reply_bar, text="✕", relief=tk.FLAT,
          command=lambda: _clear_reply()).pack(side=tk.RIGHT, padx=6)

# ── Input bar ─────────────────────────────────────────────────────────────────
inp_bar  = tk.Frame(main_area)
inp_bar.pack(fill=tk.X, padx=8, pady=6)
file_btn = tk.Button(inp_bar, text="📎", width=3,
                     relief=tk.FLAT, cursor="hand2")
file_btn.pack(side=tk.LEFT, padx=(0, 4))
entry_box = tk.Text(inp_bar, height=2, font=("Segoe UI", 11),
                    relief=tk.FLAT, wrap=tk.WORD)
entry_box.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=4)
rec_btn  = tk.Button(inp_bar, text="🎙", width=3,
                     relief=tk.FLAT, cursor="hand2")
rec_btn.pack(side=tk.LEFT, padx=(4, 4))
send_btn = tk.Button(inp_bar, text=" ➤ ",
                     font=("Segoe UI", 11, "bold"),
                     relief=tk.FLAT, cursor="hand2")
send_btn.pack(side=tk.RIGHT)

clip_btn = tk.Button(inp_bar, text="📋 Sync OFF",
                     font=("Segoe UI", 8), relief=tk.FLAT,
                     cursor="hand2", padx=6)
clip_btn.pack(side=tk.RIGHT, padx=(0, 6))

# Widget registry: mid -> { row, bubble, is_me, tick, rrow }
widget_map = {}

# ══════════════════════════════════════════════════════════════════════════════
# AVATAR
# ══════════════════════════════════════════════════════════════════════════════
def _make_initials(name, sz):
    col = COLORS[hash(name) % len(COLORS)]
    img = Image.new("RGBA", (sz, sz), (0, 0, 0, 0))
    d   = ImageDraw.Draw(img)
    d.ellipse([0, 0, sz-1, sz-1], fill=col)
    letter = name[0].upper() if name else "?"
    try:
        from PIL import ImageFont
        fn = ImageFont.truetype("arial.ttf", sz // 2)
        bb = d.textbbox((0, 0), letter, font=fn)
        d.text(((sz - (bb[2]-bb[0])) // 2,
                (sz - (bb[3]-bb[1])) // 2 - 1),
               letter, fill="white", font=fn)
    except:
        d.text((sz // 3, sz // 5), letter, fill="white")
    return img

def get_avatar(name, sz=36):
    key = f"{name}_{sz}"
    if key in avatar_cache: return avatar_cache[key]
    path = os.path.join(AVATAR_DIR, f"{name}.png")
    img  = Image.open(path) if os.path.exists(path) else _make_initials(name, sz)
    mask = Image.new("L", (sz, sz), 0)
    ImageDraw.Draw(mask).ellipse([0, 0, sz-1, sz-1], fill=255)
    out  = img.resize((sz, sz)).convert("RGBA")
    out.putalpha(mask)
    ph   = ImageTk.PhotoImage(out)
    avatar_cache[key] = ph
    return ph

# ══════════════════════════════════════════════════════════════════════════════
# THEME
# ══════════════════════════════════════════════════════════════════════════════
def apply_theme():
    t = T()
    root.config(bg=t["bg"])
    auth_frame.config(bg=t["bg"])
    for card in [login_card, reg_card]:
        card.config(bg=t["bg"])
        for w in card.winfo_children():
            try: w.config(bg=t["bg"], fg=t["text"])
            except: pass
    for fr in [_lf, _rb]:
        fr.config(bg=t["bg"])
        for w in fr.winfo_children():
            try: w.config(bg=t["bg"], fg=t["text"])
            except: pass
    _lf.config(bg=t["bg"])
    for w in _lf.winfo_children():
        try: w.config(bg=t["bg"], fg=t["text"])
        except: pass
    _lb.config(bg=t["bg"])
    # Preserve button colours in login bar
    for w in _lb.winfo_children():
        try:
            txt = w.cget("text").strip()
            if "Login" in txt:
                w.config(bg="#075e54", fg="white")
            elif "Register" in txt:
                w.config(bg="#1a73e8", fg="white")
            elif "Forgot" in txt or "Reset" in txt:
                w.config(bg="#888888", fg="white")
            else:
                w.config(bg=t["bg"], fg=t["text"])
        except: pass
    _rf.config(bg=t["bg"])
    for w in _rf.winfo_children():
        try: w.config(bg=t["bg"], fg=t["text"])
        except: pass
    paned.config(bg=t["bg"])
    sidebar.config(bg=t["panel"]); sb_top.config(bg=t["panel"])
    av_lbl.config(bg=t["panel"])
    nick_lbl.config(bg=t["panel"], fg=t["ptxt"])
    theme_btn.config(bg=t["panel"], fg=t["ptxt"])
    netstat_btn.config(bg=t["panel"], fg=t["ptxt"])
    logout_btn.config(bg="#e74c3c", fg="white")
    conv_canvas.config(bg=t["panel"]); conv_inner.config(bg=t["panel"])
    main_area.config(bg=t["bg"])
    hdr.config(bg=t["hdr"]); hdr_av.config(bg=t["hdr"])
    hdr_av_wrap.config(bg=t["hdr"]); hdr_av_badge.config(bg=t["hdr"])
    hdr_info.config(bg=t["hdr"])
    hdr_name.config(bg=t["hdr"], fg="white")
    hdr_sub.config(bg=t["hdr"],  fg="#ccffcc")
    srch_btn.config(bg=t["hdr"], fg="white")
    chat_fr.config(bg=t["chat_bg"])
    canvas.config(bg=t["chat_bg"]); msgs_frame.config(bg=t["chat_bg"])
    typing_lbl.config(bg=t["bg"], fg=t["acc2"])
    reply_bar.config(bg=t["ibg"]); reply_lbl.config(bg=t["ibg"], fg=t["text"])
    inp_bar.config(bg=t["ibg"])
    entry_box.config(bg=t["ibg"], fg=t["text"],
                     insertbackground=t["text"])
    file_btn.config(bg=t["ibg"], fg=t["text"])
    rec_btn.config(bg=t["ibg"],  fg=t["text"])
    send_btn.config(bg=t["acc2"], fg="white")
    srch_bar.config(bg=t["ibg"]); srch_e.config(bg=t["ibg"], fg=t["text"])
    try: _rebuild_sidebar()
    except: pass

def _toggle_theme():
    global theme
    theme = "dark" if theme == "light" else "light"
    apply_theme()
    _switch_chat(current_chat)

theme_btn.config(command=_toggle_theme)

# ══════════════════════════════════════════════════════════════════════════════
# SIDEBAR
# ══════════════════════════════════════════════════════════════════════════════
def _rebuild_sidebar():
    t = T()
    for w in conv_inner.winfo_children(): w.destroy()

    def make_row(key, label, sub="", show_badge=False, is_online=False):
        bg  = t["sel"] if key == current_chat else t["panel"]
        row = tk.Frame(conv_inner, bg=bg, cursor="hand2")
        row.pack(fill=tk.X, pady=1)
        ph  = get_avatar("Group" if key == "Group" else key, 44)
        av_wrap = tk.Frame(row, bg=bg, width=44, height=44)
        av_wrap.pack_propagate(False)
        av_wrap.pack(side=tk.LEFT, padx=8, pady=6)
        al  = tk.Label(av_wrap, bg=bg, image=ph); al.image = ph
        al.place(x=0, y=0)
        if show_badge:
            badge_bg = "#2ecc71" if is_online else "#8a8a8a"
            badge = tk.Canvas(av_wrap, width=13, height=13, bg=bg,
                              highlightthickness=0)
            badge.create_oval(1, 1, 12, 12, fill=badge_bg, outline=bg, width=2)
            badge.place(relx=1.0, rely=1.0, anchor="se")
        nfo = tk.Frame(row, bg=bg); nfo.pack(side=tk.LEFT, fill=tk.X, expand=True)
        tr  = tk.Frame(nfo, bg=bg); tr.pack(fill=tk.X)
        tk.Label(tr, text=label, bg=bg, fg=t["ptxt"],
                 font=("Segoe UI", 10, "bold")).pack(side=tk.LEFT)
        uc = unread.get(key, 0)
        if uc > 0 and key != current_chat:
            tk.Label(tr, text=str(uc), bg=t["acc2"], fg="white",
                     font=("Segoe UI", 8, "bold"),
                     padx=5, pady=1).pack(side=tk.RIGHT, padx=6)
        if sub:
            tk.Label(nfo, text=sub[:40], bg=bg, fg=t["time"],
                     font=("Segoe UI", 8)).pack(anchor="w")
        for w2 in [row, al, nfo, tr]:
            w2.bind("<Button-1>", lambda e, k=key: _switch_chat(k))

    # Group last message preview
    _glast = ""
    for _gmid in reversed(chat_lists.get("Group", [])):
        _gm = msg_store.get(_gmid, {})
        _gft = _gm.get("ftype", "text")
        if _gft == "text":   _glast = (_gm.get("sender","")+": "+_gm.get("content",""))[:38]; break
        elif _gft == "image":  _glast = "📷 Image";  break
        elif _gft == "voice":  _glast = "🎙 Voice note"; break
        elif _gft == "video":  _glast = "🎞 Video"; break
        elif _gft == "file":   _glast = "📄 File";  break
    if not _glast: _glast = f"{len(online_users)} members online"
    make_row("Group", "👥 Group Chat", _glast)
    tk.Frame(conv_inner, height=1, bg=t["sepbg"]).pack(
        fill=tk.X, padx=8, pady=2)
    # Show online users + anyone we have real chat history with (offline too)
    # Filter out file paths that got stored as chat_keys by mistake
    def _is_real_user(k):
        return (k != "Group" and
                "\\" not in k and "/" not in k and
                "." not in k and len(k) <= 50)
    _chat_users = set(k for k in chat_lists
                      if _is_real_user(k) and chat_lists[k])
    _all_users  = sorted(set(online_users) | _chat_users)
    _online_norm = set(o.strip().lower() for o in online_users)
    for u in _all_users:
        if u == username: continue
        _is_on = u.strip().lower() in _online_norm
        last = ""
        for mid in reversed(chat_lists.get(u, [])):
            m = msg_store.get(mid, {})
            ft = m.get("ftype", "text")
            if ft == "text":
                last = m.get("content", "")[:38]; break
            elif ft == "image":  last = "📷 Image";  break
            elif ft == "voice":  last = "🎙 Voice note"; break
            elif ft == "video":  last = "🎞 Video"; break
            elif ft == "file":   last = "📄 File";  break
        make_row(u, u, last, show_badge=True, is_online=_is_on)

def _update_header():
    t = T()
    hdr_av_badge.config(bg=t["hdr"])
    hdr_av_badge.delete("all")
    if current_chat == "Group":
        hdr_name.config(text="👥 Group Chat")
        hdr_sub.config(text=f"{len(online_users)} online")
        ph = get_avatar("Group", 38)
        # No individual online/offline badge for the group entry
    else:
        hdr_name.config(text=current_chat)
        _is_on = current_chat.strip().lower() in [o.strip().lower() for o in online_users]
        hdr_sub.config(text="Online" if _is_on else "Offline")
        ph = get_avatar(current_chat, 38)
        badge_bg = "#2ecc71" if _is_on else "#8a8a8a"
        hdr_av_badge.create_oval(1, 1, 11, 11, fill=badge_bg,
                                 outline=t["hdr"], width=2)
    hdr_av.config(image=ph); hdr_av.image = ph

# ══════════════════════════════════════════════════════════════════════════════
# SWITCH CHAT
# ══════════════════════════════════════════════════════════════════════════════
def _switch_chat(key):
    global current_chat
    current_chat = key
    unread[key]  = 0
    _read_state[key] = datetime.now().isoformat()
    _save_read_state()
    # Clear display
    for w in msgs_frame.winfo_children(): w.destroy()
    widget_map.clear(); date_shown.clear()
    # Render all stored messages for this chat
    chat_lists.setdefault(key, [])
    for mid in chat_lists[key]:
        m = msg_store.get(mid)
        if m: _render_msg(m, scroll=False)
    # Force immediate canvas repaint so messages appear right away
    # (without this, some Tkinter builds delay the visual redraw until
    # another widget-geometry event happens to fire, e.g. opening search)
    canvas.update_idletasks()
    canvas.configure(scrollregion=canvas.bbox("all"))
    _update_header()
    _rebuild_sidebar()
    root.after(120, _scroll_bottom)

# ══════════════════════════════════════════════════════════════════════════════
# RENDER MESSAGE
# ══════════════════════════════════════════════════════════════════════════════
def _scroll_bottom():
    root.update_idletasks()
    canvas.yview_moveto(1.0)
    root.after(80, lambda: canvas.yview_moveto(1.0))

def _date_sep(ts_iso):
    try:
        dt = datetime.fromisoformat(ts_iso.split("::")[0]
                                    if "::" in ts_iso else ts_iso)
        d  = dt.date(); today = date.today()
        if d == today:           return "Today"
        if (today - d).days == 1: return "Yesterday"
        return dt.strftime("%d %b %Y")
    except: return "Today"

def _maybe_date_sep(ts_iso):
    label = _date_sep(ts_iso)
    if date_shown.get(current_chat) == label: return
    date_shown[current_chat] = label
    t = T()
    outer = tk.Frame(msgs_frame, bg=t["chat_bg"]); outer.pack(pady=8)
    pill  = tk.Frame(outer, bg=t["sepbg"], padx=12, pady=3); pill.pack()
    tk.Label(pill, text=label, bg=t["sepbg"], fg=t["sepfg"],
             font=("Segoe UI", 8, "bold")).pack()

def _render_msg(msg, scroll=True):
    t    = T()
    mid  = msg.get("mid", gid()); msg["mid"] = mid
    sender   = msg.get("sender", "")
    # ── KEY FIX: Compare sender to logged-in username ─────────────────────────
    is_me    = (sender.strip().lower() == username.strip().lower())
    ftype    = msg.get("ftype", "text") or "text"
    content  = msg.get("content", "")
    ts_iso   = msg.get("ts", "")
    chat_key = msg.get("chat_key", "Group")
    rep_to   = msg.get("reply_to", None)

    if chat_key != current_chat: return
    _maybe_date_sep(ts_iso)

    # Bubble colour
    if is_me:
        bbg = t["mine"]
    elif chat_key != "Group":
        bbg = t["priv"]
    else:
        bbg = t["other"]

    row = tk.Frame(msgs_frame, bg=t["chat_bg"])
    row.pack(fill=tk.X, pady=3, padx=6)

    # ── ALIGNMENT FIX ────────────────────────────────────────────────────────
    # For MY messages:  spacer LEFT → bubble+avatar pushed to RIGHT
    # For OTHER messages: avatar+bubble LEFT → spacer RIGHT
    if is_me:
        tk.Frame(row, bg=t["chat_bg"]).pack(side=tk.LEFT, fill=tk.X, expand=True)

    av = tk.Label(row, bg=t["chat_bg"])
    ph = get_avatar(sender, 34); av.config(image=ph); av.image = ph

    bubble = tk.Frame(row, bg=bbg, padx=10, pady=6)

    if is_me:
        bubble.pack(side=tk.LEFT, anchor="s", pady=(0, 4))
        av.pack(side=tk.LEFT,     anchor="s", padx=(4, 2), pady=(0, 4))
    else:
        av.pack(side=tk.LEFT,     anchor="s", padx=(2, 4), pady=(0, 4))
        bubble.pack(side=tk.LEFT, anchor="s", pady=(0, 4))
        tk.Frame(row, bg=t["chat_bg"]).pack(side=tk.LEFT, fill=tk.X, expand=True)

    # Reply quote
    if rep_to:
        orig   = msg_store.get(rep_to, {})
        rb_bg  = t["ibg"]
        rb     = tk.Frame(bubble, bg=rb_bg); rb.pack(fill=tk.X, pady=(0, 4))
        tk.Frame(rb, bg=t["acc2"], width=3).pack(side=tk.LEFT, fill=tk.Y)
        rt = tk.Frame(rb, bg=rb_bg, padx=6, pady=3); rt.pack(side=tk.LEFT)
        tk.Label(rt, text=orig.get("sender", ""),
                 bg=rb_bg, fg=t["acc2"],
                 font=("Segoe UI", 8, "bold")).pack(anchor="w")
        tk.Label(rt, text=(orig.get("content", "") or "[media]")[:55],
                 bg=rb_bg, fg=t["time"],
                 font=("Segoe UI", 8), wraplength=240).pack(anchor="w")

    # Sender name in group (others only)
    if chat_key == "Group" and not is_me:
        nc = COLORS[hash(sender) % len(COLORS)]
        tk.Label(bubble, text=sender, bg=bbg, fg=nc,
                 font=("Segoe UI", 9, "bold")).pack(anchor="w")

    # Content
    if ftype == "text":
        tk.Label(bubble, text=content, bg=bbg, fg=t["text"],
                 wraplength=380, justify="left",
                 font=("Segoe UI", 10)).pack(anchor="w")

    elif ftype == "image":
        if content and not content.startswith("MISSING::") and os.path.exists(content):
            try:
                pil = Image.open(content); pil.thumbnail((260, 180))
                imgtk = ImageTk.PhotoImage(pil)
                lb = tk.Label(bubble, image=imgtk, bg=bbg)
                lb.image = imgtk; lb.pack()
                lb.bind("<Button-1>", lambda e, p=content: _preview_img(p))
                fn = os.path.basename(content)
                tk.Button(bubble, text="⬇ Save", bg=t["acc"], fg="white",
                          relief=tk.FLAT, cursor="hand2",
                          font=("Segoe UI", 8),
                          command=lambda p=content, n=fn: _save_file(p, n)
                          ).pack(anchor="w", pady=(2, 0))
            except:
                tk.Label(bubble, text="🖼 [Image]", bg=bbg, fg=t["text"]).pack()
        else:
            safe_fn = content.replace("MISSING::","") if content else ""
            orig_fn = msg.get("orig_fname", safe_fn) or safe_fn
            fr2 = tk.Frame(bubble, bg=bbg); fr2.pack(anchor="w")
            tk.Label(fr2, text="🖼 Image", bg=bbg, fg=t["text"],
                     font=("Segoe UI",9)).pack(side=tk.LEFT)
            if safe_fn:
                tk.Button(fr2, text="⬇ Request", bg=t["acc"], fg="white",
                          relief=tk.FLAT, cursor="hand2", font=("Segoe UI",8),
                          command=lambda fn=safe_fn: _request_file(fn)
                          ).pack(side=tk.LEFT, padx=4)

    elif ftype == "voice" and content:
        vr = tk.Frame(bubble, bg=bbg); vr.pack(anchor="w")
        if not content.startswith("MISSING::") and os.path.exists(content):
            _pbtn = tk.Button(vr, text="▶ Play", bg=t["acc2"], fg="white",
                              relief=tk.FLAT, cursor="hand2")
            _pbtn.config(command=lambda p=content, b=_pbtn: _play_audio(p, b))
            _pbtn.pack(side=tk.LEFT)
            tk.Label(vr, text="  🎙 Voice",
                     bg=bbg, fg=t["text"], font=("Segoe UI", 9)).pack(side=tk.LEFT, padx=4)
        else:
            safe_fn = content.replace("MISSING::","") if content else ""
            tk.Label(vr, text="🎙 Voice note", bg=bbg, fg=t["text"],
                     font=("Segoe UI",9)).pack(side=tk.LEFT)
            if safe_fn:
                tk.Button(vr, text="⬇ Request", bg=t["acc"], fg="white",
                          relief=tk.FLAT, cursor="hand2", font=("Segoe UI",8),
                          command=lambda fn=safe_fn: _request_file(fn)
                          ).pack(side=tk.LEFT, padx=4)

    elif ftype == "video" and content:
        tk.Button(bubble, text="🎞 Play Video ▶", bg=bbg, fg=t["text"],
                  relief=tk.FLAT, cursor="hand2",
                  command=lambda p=content: _open_file(p)).pack(anchor="w")

    else:
        fname = os.path.basename(content) if content else "File"
        fr = tk.Frame(bubble, bg=bbg); fr.pack(anchor="w")
        tk.Label(fr, text=f"📄 {fname}", bg=bbg,
                 fg=t["text"],
                 font=("Segoe UI", 9)).pack(side=tk.LEFT)
        if content and os.path.exists(content):
            tk.Button(fr, text="Open", bg=t["acc"], fg="white",
                      relief=tk.FLAT, cursor="hand2",
                      font=("Segoe UI", 8),
                      command=lambda p=content: _open_file(p)
                      ).pack(side=tk.LEFT, padx=4)
            tk.Button(fr, text="⬇ Save", bg="#5b7fa6", fg="white",
                      relief=tk.FLAT, cursor="hand2",
                      font=("Segoe UI", 8),
                      command=lambda p=content, n=fname: _save_file(p, n)
                      ).pack(side=tk.LEFT, padx=2)

    # Reaction row
    rrow = tk.Frame(bubble, bg=bbg); rrow.pack(anchor="w", pady=(2, 0))
    msg["_rrow"] = rrow

    # Timestamp + tick
    trow = tk.Frame(bubble, bg=bbg); trow.pack(fill=tk.X, pady=(4, 0))
    try:
        tdisp = datetime.fromisoformat(
            ts_iso.split("::")[0]).strftime("%H:%M")
    except: tdisp = ""
    tick = tk.Label(trow, text=(" ✓" if is_me else ""),
                    bg=bbg, fg="#888", font=("Segoe UI", 7))
    tick.pack(side=tk.RIGHT)
    tk.Label(trow, text=tdisp, bg=bbg, fg=t["time"],
             font=("Segoe UI", 7)).pack(side=tk.RIGHT, padx=2)

    widget_map[mid] = {
        "row": row, "bubble": bubble, "is_me": is_me,
        "tick": tick, "ftype": ftype, "rrow": rrow
    }

    # Right-click menu
    bubble.bind("<Button-3>", lambda e, m=mid: _ctx_menu(e, m))
    for child in bubble.winfo_children():
        child.bind("<Button-3>", lambda e, m=mid: _ctx_menu(e, m))

    if scroll:
        root.after(60, _scroll_bottom)


def _store_and_show(msg):
    """Store message and render if in current chat."""
    mid = msg.get("mid", gid()); msg["mid"] = mid
    ck  = msg.get("chat_key", "Group")
    msg_store[mid] = msg
    chat_lists.setdefault(ck, [])
    if mid not in chat_lists[ck]:
        chat_lists[ck].append(mid)
    if ck == current_chat:
        _render_msg(msg, scroll=True)
    else:
        _msg_ts = msg.get("ts", "")
        _last_read = _read_state.get(ck, "")
        if _msg_ts and _last_read and _msg_ts <= _last_read:
            pass  # already seen in a previous session — don't re-count as unread
        else:
            unread[ck] = unread.get(ck, 0) + 1
        _rebuild_sidebar()

# ══════════════════════════════════════════════════════════════════════════════
# CONTEXT MENU
# ══════════════════════════════════════════════════════════════════════════════
EMOJIS = ["❤️","😂","👍","👎","😮","😢","🔥","🎉"]

def _ctx_menu(event, mid):
    m = tk.Menu(root, tearoff=0)
    m.add_command(label="↩  Reply", command=lambda: _prep_reply(mid))
    m.add_command(label="📋  Copy",  command=lambda: _copy_msg(mid))
    m.add_separator()
    sub = tk.Menu(m, tearoff=0)
    for em in EMOJIS:
        sub.add_command(label=em,
                        command=lambda e=em, i=mid: _send_react(i, e))
    m.add_cascade(label="😊  React", menu=sub)
    m.add_separator()
    m.add_command(label="🗑  Delete for me",
                  command=lambda: _del_local(mid))
    if widget_map.get(mid, {}).get("is_me"):
        m.add_command(label="🗑  Delete for everyone",
                      command=lambda: _del_perm(mid))
    try:    m.tk_popup(event.x_root, event.y_root)
    finally: m.grab_release()

def _prep_reply(mid):
    global reply_mid
    msg = msg_store.get(mid, {})
    reply_mid = mid
    preview = msg.get("content", "[media]")[:80]
    reply_var.set(f"↩ {msg.get('sender','')}:  {preview}")
    reply_bar.pack(fill=tk.X, padx=8, pady=(2, 0), before=inp_bar)

def _clear_reply():
    global reply_mid
    reply_mid = None
    reply_var.set("")
    reply_bar.pack_forget()

def _copy_msg(mid):
    root.clipboard_clear()
    root.clipboard_append(msg_store.get(mid, {}).get("content", ""))

def _del_local(mid):
    obj = widget_map.pop(mid, None)
    if obj: obj["row"].destroy()
    msg_store.pop(mid, None)
    for lst in chat_lists.values():
        if mid in lst: lst.remove(mid)

def _del_perm(mid):
    try: tcp.sendall(f"DELETE_PERM::{mid}::{username}\n".encode())
    except Exception as e: messagebox.showerror("Delete", str(e))

def _send_react(mid, emoji):
    try: tcp.sendall(f"REACT::{mid}::{username}::{emoji}\n".encode())
    except: pass
    _apply_react(mid, username, emoji)

def _apply_react(mid, user, emoji):
    msg = msg_store.get(mid)
    if not msg: return
    rxs = msg.setdefault("reactions", {})
    rxs.setdefault(emoji, set()).add(user)
    obj = widget_map.get(mid)
    if not obj: return
    rr = obj.get("rrow")
    if not rr: return
    for w in rr.winfo_children(): w.destroy()
    for em, us in rxs.items():
        if us:
            tk.Label(rr, text=f"{em}{len(us)}",
                     bg=T()["sepbg"], fg=T()["text"],
                     font=("Segoe UI Emoji", 9),
                     padx=4, pady=1).pack(side=tk.LEFT, padx=2)

# ══════════════════════════════════════════════════════════════════════════════
# SEARCH
# ══════════════════════════════════════════════════════════════════════════════
def _toggle_search():
    if srch_bar.winfo_ismapped():
        srch_bar.pack_forget()
    else:
        srch_bar.pack(fill=tk.X, padx=8, pady=2, before=chat_fr)
        srch_e.focus_set()

def _do_search(*_):
    q = srch_e.get().strip().lower(); t = T()
    for mid, obj in widget_map.items():
        hit = q and q in msg_store.get(mid, {}).get("content", "").lower()
        obj["bubble"].config(
            bg="#fff7a8" if hit else
               (t["mine"] if obj["is_me"] else t["other"]))

srch_btn.config(command=_toggle_search)
srch_e.bind("<KeyRelease>", _do_search)

# ══════════════════════════════════════════════════════════════════════════════
# MEDIA HELPERS
# ══════════════════════════════════════════════════════════════════════════════
def _preview_img(path):
    w = tk.Toplevel(root); w.title("Image Preview")
    try:
        img = Image.open(path); imgtk = ImageTk.PhotoImage(img)
        tk.Label(w, image=imgtk).pack(); w.imgtk = imgtk
    except: tk.Label(w, text="Cannot open image").pack()

def _open_file(path):
    try:
        if os.name == "nt": os.startfile(path)
        else: subprocess.Popen(["xdg-open", path])
    except Exception as e: messagebox.showerror("Open", str(e))

def _save_file(src, fname):
    dst = filedialog.asksaveasfilename(
        initialfile=fname,
        title="Save file as",
        defaultextension=os.path.splitext(fname)[1])
    if not dst: return
    try:
        import shutil; shutil.copy2(src, dst)
        messagebox.showinfo("Saved", "File saved successfully.")
    except Exception as e: messagebox.showerror("Save failed", str(e))

def _request_file(safe_fname):
    """Show info — file was sent to the other machine, not this one."""
    messagebox.showinfo(
        "File Not Available",
        f"This file ({safe_fname}) was received on another device.\n"
        "Ask the sender to share it again directly with you.")

_voice_threads = {}

def _play_audio(path, play_btn=None):
    state = _voice_threads.get(path)
    if state:
        state["paused"] = not state["paused"]
        if play_btn:
            lbl = "▶ Play" if state["paused"] else "⏸ Pause"
            root.after(0, play_btn.config, {"text": lbl})
        return
    if not HAS_AUDIO:
        if USE_SA:
            def _run2():
                try:
                    data2, sr2 = sf.read(path, dtype="int16")
                    sa.WaveObject(data2.tobytes(), 1, 2, sr2).play().wait_done()
                except Exception as e:
                    root.after(0, messagebox.showerror, "Play", str(e))
                finally:
                    if play_btn: root.after(0, play_btn.config, {"text": "▶ Play"})
            if play_btn: root.after(0, play_btn.config, {"text": "⏸ Pause"})
            threading.Thread(target=_run2, daemon=True).start()
            return
        messagebox.showwarning("Audio", "Install sounddevice + soundfile + numpy")
        return
    def _run():
        st = {"paused": False, "stop": False}
        _voice_threads[path] = st
        if play_btn: root.after(0, play_btn.config, {"text": "⏸ Pause"})
        try:
            data, sr = sf.read(path, dtype="float32")
            if data.ndim == 1: data = data.reshape(-1, 1)
            channels = data.shape[1]
            idx = [0]
            def cb(outdata, frames, time_info, status):
                if st["stop"]:
                    outdata[:] = 0; return
                if st["paused"]:
                    outdata[:] = 0; return
                chunk = data[idx[0]:idx[0]+frames]
                if len(chunk) < frames:
                    outdata[:len(chunk)] = chunk
                    outdata[len(chunk):] = 0
                    st["stop"] = True
                else:
                    outdata[:] = chunk
                idx[0] += frames
            with sd.OutputStream(samplerate=sr, channels=channels,
                                 callback=cb, dtype="float32") as stream:
                st["stream"] = stream
                while not st["stop"]:
                    time.sleep(0.05)
        except Exception as e:
            root.after(0, messagebox.showerror, "Play", str(e))
        finally:
            _voice_threads.pop(path, None)
            if play_btn: root.after(0, play_btn.config, {"text": "▶ Play"})
    threading.Thread(target=_run, daemon=True).start()

# ══════════════════════════════════════════════════════════════════════════════
# TYPING
# ══════════════════════════════════════════════════════════════════════════════
def _show_typing(user, chat):
    if chat != current_chat: return
    typing_lbl.config(text=f"{user} is typing...")
    if user in typing_jobs: root.after_cancel(typing_jobs[user])
    typing_jobs[user] = root.after(
        2500, lambda: typing_lbl.config(text=""))

def _update_users(names):
    global online_users
    online_users = [n for n in names if n]
    _rebuild_sidebar(); _update_header()

# ══════════════════════════════════════════════════════════════════════════════
# CLIPBOARD SYNC
# ══════════════════════════════════════════════════════════════════════════════
clip_sync_enabled = False
_last_clip = ""

def _clip_notify(sender, chat_key, content):
    # Clipboard itself always updates so Ctrl+V works regardless of which
    # chat window happens to be open — only the VISUAL banner is scoped.
    try:
        root.clipboard_clear(); root.clipboard_append(content)
    except: pass

    # Only show the banner if the receiver is currently looking at the
    # SAME chat this clip was shared in — a private share must never
    # appear while viewing Group Chat, and vice-versa.
    if chat_key != current_chat:
        return

    preview = content[:60] + ("..." if len(content)>60 else "")
    note = tk.Frame(msgs_frame, bg="#fffbe6", highlightbackground="#f0c040", highlightthickness=1)
    note.pack(fill=tk.X, padx=20, pady=3)
    tk.Label(note, text="📋  "+sender+" shared clipboard: \""+preview+"\"",
             bg="#fffbe6", fg="#7a5c00", font=("Segoe UI",9,"italic"),
             wraplength=500, justify="left", padx=8, pady=4).pack(anchor="w")
    tk.Label(note, text="✅ Copied to your clipboard  |  Press Ctrl+V to paste",
             bg="#fffbe6", fg="#2e7d32", font=("Segoe UI",8), padx=8, pady=2).pack(anchor="w")
    root.after(8000, lambda: note.destroy() if note.winfo_exists() else None)
    root.after(80, _scroll_bottom)

def _looks_like_filepath(s):
    """Detect raw filesystem paths (e.g. an internal voice-note path that
    ends up on the OS clipboard) so they are never auto-shared as if they
    were meaningful text."""
    s = s.strip()
    if len(s) < 3: return False
    if len(s) >= 3 and s[1] == ":" and s[2] in ("\\", "/"):
        return True  # e.g. C:\... or C:/...
    low = s.lower()
    if "files\\voice" in low or "files/voice" in low or \
       "files\\received" in low or "files/received" in low:
        return True
    _media_ext = (".wav",".mp3",".mp4",".jpg",".jpeg",".png",".gif",".mov",".avi",".mkv")
    if low.endswith(_media_ext) and " " not in s:
        return True
    return False

def _clip_monitor():
    global _last_clip, clip_sync_enabled
    while True:
        time.sleep(0.5)
        if not clip_sync_enabled or not tcp or not username: continue
        try: current = root.clipboard_get()
        except: continue
        if current and current != _last_clip and len(current) <= 5000:
            _last_clip = current
            if _looks_like_filepath(current):
                continue  # internal file path — not meaningful shared text
            try:
                tcp.sendall(("CLIP::"+username+"::"+current_chat+"::"+current+"\n").encode("utf-8"))
            except: pass

def _toggle_clip_sync():
    global clip_sync_enabled, _last_clip
    clip_sync_enabled = not clip_sync_enabled
    _last_clip = ""
    if clip_sync_enabled:
        clip_btn.config(text="📋 Sync ON", bg="#2e7d32", fg="white")
        info = tk.Frame(msgs_frame, bg="#e8f5e9", highlightbackground="#4caf50", highlightthickness=1)
        info.pack(fill=tk.X, padx=20, pady=3)
        tk.Label(info, text="📋 Clipboard Sync ENABLED  Copy anything (Ctrl+C) and all connected users get it instantly",
                 bg="#e8f5e9", fg="#1b5e20", font=("Segoe UI",9), wraplength=500, padx=8, pady=5).pack(anchor="w")
        root.after(80, _scroll_bottom)
        # Auto-dismiss this local "enabled" banner once the user has had time to read it
        root.after(6000, lambda: info.destroy() if info.winfo_exists() else None)
    else:
        clip_btn.config(text="📋 Sync OFF", bg=T()["ibg"], fg=T()["text"])

clip_btn.config(command=_toggle_clip_sync)

# ══════════════════════════════════════════════════════════════════════════════
# LAN NETWORK PERFORMANCE MONITOR
# Offline-only test — measures latency, packet loss, download throughput and
# upload throughput between THIS client and the actual connected LAN Chat
# server (server_ip / tcp socket already established at login). No internet
# and no localhost shortcut is used — all traffic goes over the real LAN
# connection the chat itself uses.
#
# Protocol additions:
#   PING::<eid>::               (C->S) small round trip  -> latency/packet-loss
#   PONG::<eid>::                (S->C) echo reply
#   NETUP::<eid>::<payload>      (C->S) client uploads payload, server just acks
#   NETACK::<eid>                (S->C) ack for NETUP -> measures UPLOAD speed
#   NETDOWN::<eid>::<size>       (C->S) client requests <size> bytes from server
#   NETDATA::<eid>::<payload>    (S->C) server sends payload -> measures DOWNLOAD speed
# ══════════════════════════════════════════════════════════════════════════════
_net_pending   = {}                 # echo_id -> send_time (perf_counter)   [latency]
_net_results   = []                 # list of rtt_seconds                  [latency]
_net_up_pending  = {}                # echo_id -> (send_time, payload_len)  [upload]
_net_up_results  = []                # list of (elapsed_seconds, payload_len)
_net_down_pending = {}               # echo_id -> send_time                 [download]
_net_down_results = []               # list of (elapsed_seconds, payload_len)
_net_lock      = threading.Lock()
_net_running   = False

def _net_test_record_pong(eid, plen):
    """Latency ping reply — called from _recv_loop on PONG::."""
    with _net_lock:
        send_time = _net_pending.pop(eid, None)
    if send_time is not None:
        rtt = time.perf_counter() - send_time
        with _net_lock:
            _net_results.append(rtt)

def _net_test_record_upack(eid):
    """Upload test ack — called from _recv_loop on NETACK::."""
    with _net_lock:
        info = _net_up_pending.pop(eid, None)
    if info is not None:
        send_time, plen = info
        elapsed = time.perf_counter() - send_time
        with _net_lock:
            _net_up_results.append((elapsed, plen))

def _net_test_record_downdata(eid, plen):
    """Download test payload received — called from _recv_loop on NETDATA::."""
    with _net_lock:
        send_time = _net_down_pending.pop(eid, None)
    if send_time is not None:
        elapsed = time.perf_counter() - send_time
        with _net_lock:
            _net_down_results.append((elapsed, plen))

def _net_run_test(status_var, result_box, run_btn):
    """Runs in a background thread over the SAME tcp socket already connected
    to the real LAN chat server (never localhost, never the internet)."""
    global _net_running
    if not tcp:
        root.after(0, status_var.set, "Not connected to server.")
        return
    _net_running = True

    with _net_lock:
        _net_pending.clear();      _net_results.clear()
        _net_up_pending.clear();   _net_up_results.clear()
        _net_down_pending.clear(); _net_down_results.clear()

    LAT_COUNT    = 15            # small pings -> latency + packet loss
    XFER_COUNT   = 4             # payload count for each of upload/download
    XFER_PAYLOAD = "X" * 65536   # 64 KB filler payload per transfer test

    def _fail(msg):
        global _net_running
        root.after(0, status_var.set, msg)
        _net_running = False

    # ── 1) Latency + packet loss ──────────────────────────────────────────────
    root.after(0, status_var.set, "Testing latency...")
    for i in range(LAT_COUNT):
        eid = f"L{i}-{gid()[:8]}"
        with _net_lock:
            _net_pending[eid] = time.perf_counter()
        try:
            tcp.sendall(("PING::" + eid + "::\n").encode("utf-8"))
        except Exception:
            _fail("Connection error during latency test."); return
        time.sleep(0.04)

    # ── 2) Upload throughput (client -> server) ───────────────────────────────
    root.after(0, status_var.set, "Testing upload speed...")
    for i in range(XFER_COUNT):
        eid = f"U{i}-{gid()[:8]}"
        with _net_lock:
            _net_up_pending[eid] = (time.perf_counter(), len(XFER_PAYLOAD))
        try:
            tcp.sendall(("NETUP::" + eid + "::" + XFER_PAYLOAD + "\n").encode("utf-8"))
        except Exception:
            _fail("Connection error during upload test."); return
        time.sleep(0.05)

    # ── 3) Download throughput (server -> client) ─────────────────────────────
    root.after(0, status_var.set, "Testing download speed...")
    for i in range(XFER_COUNT):
        eid = f"D{i}-{gid()[:8]}"
        with _net_lock:
            _net_down_pending[eid] = time.perf_counter()
        try:
            tcp.sendall(("NETDOWN::" + eid + "::" + str(len(XFER_PAYLOAD)) + "\n").encode("utf-8"))
        except Exception:
            _fail("Connection error during download test."); return
        time.sleep(0.05)

    # ── Wait for all replies (recv_loop fills results asynchronously) ─────────
    total_expected = LAT_COUNT + XFER_COUNT + XFER_COUNT
    deadline = time.time() + 6.0
    while time.time() < deadline:
        with _net_lock:
            got = len(_net_results) + len(_net_up_results) + len(_net_down_results)
        if got >= total_expected:
            break
        time.sleep(0.1)

    with _net_lock:
        lat_list  = list(_net_results)
        up_list   = list(_net_up_results)
        down_list = list(_net_down_results)
        _net_pending.clear(); _net_up_pending.clear(); _net_down_pending.clear()

    received   = len(lat_list) + len(up_list) + len(down_list)
    packet_loss = round((total_expected - received) / total_expected * 100, 1)

    avg_latency = round((sum(lat_list) / len(lat_list)) * 1000, 1) if lat_list else None

    def _avg_mbps(samples):
        if not samples: return 0.0
        vals = [(plen * 8) / elapsed / 1_000_000 for elapsed, plen in samples if elapsed > 0]
        return round(sum(vals) / len(vals), 2) if vals else 0.0

    upload_mbps   = _avg_mbps(up_list)
    download_mbps = _avg_mbps(down_list)

    # ── Quality rating ─────────────────────────────────────────────────────────
    if avg_latency is None:
        quality, qcolor = "Poor (no response)", "#e74c3c"
    elif avg_latency < 10 and packet_loss == 0:
        quality, qcolor = "Excellent", "#2e7d32"
    elif avg_latency < 40 and packet_loss < 10:
        quality, qcolor = "Moderate", "#f39c12"
    else:
        quality, qcolor = "Poor", "#e74c3c"

    def _show_result():
        result_box.config(state=tk.NORMAL)
        result_box.delete("1.0", tk.END)
        lat_txt = f"{avg_latency} ms" if avg_latency is not None else "No reply"
        rows = [
            ("Latency:",             lat_txt),
            ("Packet Loss:",         f"{packet_loss}%"),
            ("Download Throughput:", f"{download_mbps} Mbps"),
            ("Upload Throughput:",   f"{upload_mbps} Mbps"),
            ("Connection Quality:",  quality),
        ]
        for i, (label, val) in enumerate(rows):
            result_box.insert(tk.END, f"{label:<20}{val}\n")
        # colour the quality line
        q_line = len(rows)
        result_box.tag_add("q", f"{q_line}.20", f"{q_line}.end")
        result_box.tag_config("q", foreground=qcolor)
        result_box.config(state=tk.DISABLED)
        status_var.set("Test complete.")
        run_btn.config(state=tk.NORMAL, text="\U0001f504 Run Test Again")

    root.after(0, _show_result)
    with _net_lock:
        pass
    _net_running = False

def _open_network_monitor():
    """Opens the LAN Network Performance Monitor window. All measurements are
    taken against the currently connected LAN Chat server (server_ip below),
    never localhost and never the internet."""
    if _net_running:
        return
    win = tk.Toplevel(root)
    win.title("LAN Network Performance Monitor")
    win.geometry("400x340")
    win.resizable(False, False)
    t = T()
    win.config(bg=t["bg"])

    tk.Label(win, text="\U0001f4f6 LAN Network Performance",
             bg=t["bg"], fg=t["text"],
             font=("Segoe UI", 13, "bold")).pack(pady=(16, 2))

    target_txt = f"Testing against server: {server_ip or 'unknown'}"
    tk.Label(win, text=target_txt,
             bg=t["bg"], fg=t["acc2"], font=("Segoe UI", 9, "bold")).pack()

    tk.Label(win, text="Latency, packet loss, download and upload throughput\nmeasured directly over the LAN (no internet used).",
             bg=t["bg"], fg=t["time"], font=("Segoe UI", 9),
             justify="center").pack(pady=(4, 10))

    status_var = tk.StringVar(value="Ready.")
    status_lbl2 = tk.Label(win, textvariable=status_var,
                           bg=t["bg"], fg=t["acc2"], font=("Segoe UI", 9))
    status_lbl2.pack()

    result_box = tk.Text(win, height=7, width=40, font=("Consolas", 10),
                         relief=tk.FLAT, bg=t["ibg"], fg=t["text"],
                         state=tk.DISABLED)
    result_box.pack(padx=20, pady=12)

    def _start():
        run_btn.config(state=tk.DISABLED, text="Testing...")
        status_var.set("Starting test...")
        threading.Thread(target=_net_run_test,
                         args=(status_var, result_box, run_btn),
                         daemon=True).start()

    run_btn = tk.Button(win, text="\u25b6 Run Test", command=_start,
                        bg=t["acc2"], fg="white", relief=tk.FLAT,
                        font=("Segoe UI", 10, "bold"),
                        padx=16, pady=8, cursor="hand2")
    run_btn.pack(pady=(0, 16))

    _start()  # auto-run once on open

netstat_btn.config(command=_open_network_monitor)


# ══════════════════════════════════════════════════════════════════════════════
# SEND
# ══════════════════════════════════════════════════════════════════════════════
def _send_text(event=None):
    if event and ((event.state & 0x1) or (event.state & 0x8)):
        entry_box.insert(tk.INSERT, "\n"); return "break"
    text = entry_box.get("1.0", tk.END).strip()
    if not text or not tcp: return "break"
    mid = gid()
    msg = {
        "mid": mid, "sender": username,
        "content": text, "ftype": "text",
        "ts": datetime.now().isoformat(),
        "chat_key": current_chat,
        "reply_to": reply_mid
    }
    _store_and_show(msg)
    obj = widget_map.get(mid)
    if obj: obj["tick"].config(text=" ✓")
    try:
        tcp.sendall(
            f"MSG::{mid}::{text}::{current_chat}::{reply_mid or ''}\n"
            .encode())
    except Exception as e: messagebox.showerror("Send", str(e))
    entry_box.delete("1.0", tk.END)
    _clear_reply()
    return "break"

def _send_typing(event=None):
    if tcp and username:
        try: tcp.sendall(
            f"TYPING::{username}::{current_chat}\n".encode())
        except: pass

def _send_file():
    p = filedialog.askopenfilename()
    if not p or not tcp: return
    ext = os.path.splitext(p)[1].lower()
    if   ext in [".png",".jpg",".jpeg",".gif",".bmp",".webp"]: ft = "image"
    elif ext in [".mp4",".mov",".avi",".mkv"]:                  ft = "video"
    elif ext in [".wav",".mp3",".ogg"]:                         ft = "voice"
    else:                                                        ft = "file"
    mid = gid()
    _store_and_show({
        "mid": mid, "sender": username, "content": p,
        "ftype": ft, "ts": datetime.now().isoformat(),
        "chat_key": current_chat
    })
    def _run():
        try:
            sz = os.path.getsize(p); fn = os.path.basename(p)
            tcp.sendall(
                f"FILE::{mid}::{fn}::{sz}::{ft}::{current_chat}\n"
                .encode())
            with open(p, "rb") as f:
                while True:
                    chunk = f.read(4096)
                    if not chunk: break
                    tcp.sendall(chunk)
        except Exception as e:
            root.after(0, messagebox.showerror, "File send", str(e))
    threading.Thread(target=_run, daemon=True).start()

# ══════════════════════════════════════════════════════════════════════════════
# VOICE RECORDING
# ══════════════════════════════════════════════════════════════════════════════
def _rec_toggle():
    global recording, rec_frames, rec_stream, rec_start
    if not HAS_AUDIO:
        messagebox.showwarning("Audio",
            "Install sounddevice + soundfile + numpy for voice notes")
        return
    if not recording:
        recording = True; rec_frames = []; rec_start = time.time()
        rec_btn.config(text="⏹", bg="#e74c3c", fg="white")
        def cb(indata, fc, ti, st):
            if recording: rec_frames.append(indata.copy())
        try:
            rec_stream = sd.InputStream(samplerate=SR, channels=CH,
                                        callback=cb)
            rec_stream.start()
        except Exception as e:
            recording = False
            rec_btn.config(text="🎙", bg=T()["ibg"], fg=T()["text"])
            messagebox.showerror("Record", str(e)); return
        def _ticker():
            if recording:
                rec_btn.config(
                    text=f"⏹ {int(time.time()-rec_start)}s")
                if time.time() - rec_start >= MAX_SEC:
                    _rec_toggle(); return
                root.after(1000, _ticker)
        root.after(1000, _ticker)
    else:
        recording = False
        rec_btn.config(text="🎙", bg=T()["ibg"], fg=T()["text"])
        try: rec_stream.stop(); rec_stream.close()
        except: pass
        if not rec_frames: return
        audio = np.concatenate(rec_frames, axis=0)
        nm    = "voice_" + datetime.now().strftime("%Y%m%d%H%M%S") + ".wav"
        path  = os.path.join(VOICE_DIR, nm)
        sf.write(path, audio, SR, subtype="PCM_16")
        mid = gid()
        _store_and_show({
            "mid": mid, "sender": username, "content": path,
            "ftype": "voice", "ts": datetime.now().isoformat(),
            "chat_key": current_chat
        })
        def _run():
            try:
                sz = os.path.getsize(path)
                tcp.sendall(
                    f"FILE::{mid}::{nm}::{sz}::voice::{current_chat}\n"
                    .encode())
                with open(path, "rb") as f:
                    while True:
                        chunk = f.read(4096)
                        if not chunk: break
                        tcp.sendall(chunk)
            except Exception as e:
                root.after(0, messagebox.showerror, "Voice send", str(e))
        threading.Thread(target=_run, daemon=True).start()

rec_btn.config(command=lambda:
    threading.Thread(target=_rec_toggle, daemon=True).start())

# ══════════════════════════════════════════════════════════════════════════════
# RECEIVE LOOP  — runs in background thread, posts to root.after() for UI
# ══════════════════════════════════════════════════════════════════════════════
def _recv_loop():
    buf = b""
    while True:
        try:
            data = tcp.recv(8192)
            if not data: break
            buf += data

            while b"\n" in buf:
                raw, buf = buf.split(b"\n", 1)
                txt = raw.decode("utf-8", errors="ignore").strip()
                if not txt: continue

                # USERS::<name1>,<name2>,...
                if txt.startswith("USERS::"):
                    names = txt[7:].split(",") if txt[7:] else []
                    root.after(0, _update_users, names)
                    continue

                # TYPING::<user>::<chat_key>
                if txt.startswith("TYPING::"):
                    p = txt.split("::")
                    if len(p) >= 3 and p[1] != username:
                        root.after(0, _show_typing, p[1], p[2])
                    continue

                # REACT::<mid>::<user>::<emoji>
                if txt.startswith("REACT::"):
                    p = txt.split("::")
                    if len(p) >= 4:
                        root.after(0, _apply_react, p[1], p[2], p[3])
                    continue

                # SEEN::<mid>::<user>
                if txt.startswith("SEEN::"):
                    try: _, mid, _ = txt.split("::", 2)
                    except: continue
                    obj = widget_map.get(mid)
                    if obj and obj["is_me"]:
                        root.after(0, lambda o=obj:
                            o["tick"].config(text=" ✓✓", fg="#53bdeb"))
                    continue

                # CLIP::<sender>::<chat_key>::<content>  Clipboard Sync
                # chat_key = "Group" for a group-wide share, or the intended
                # recipient's username for a private share (server already
                # routes private shares only to that recipient — this parse
                # just keeps the client's private re-keying consistent with
                # how MSG:: / FILE:: are handled).
                if txt.startswith("CLIP::"):
                    try:
                        p = txt.split("::", 3)
                        sndr = p[1] if len(p) >= 2 else ""
                        cck  = p[2] if len(p) >= 3 else "Group"
                        cnt  = p[3] if len(p) >= 4 else ""
                    except: continue
                    if cck == username:
                        cck = sndr
                    if sndr != username and cnt:
                        root.after(0, _clip_notify, sndr, cck, cnt)
                    continue

                # PONG::<echo_id>::<payload>  Network Performance reply
                # Server echoes back verbatim; payload length itself is measured
                # here (not declared) so throughput can be computed accurately.
                if txt.startswith("PONG::"):
                    try:
                        _pp = txt.split("::",2)
                        _eid = _pp[1] if len(_pp)>=2 else ""
                        _pld = _pp[2] if len(_pp)>=3 else ""
                    except: continue
                    _net_test_record_pong(_eid, len(_pld))
                    continue

                # NETACK::<eid>  Upload-throughput ack from server
                if txt.startswith("NETACK::"):
                    try: _ueid = txt.split("::",1)[1].strip()
                    except: continue
                    _net_test_record_upack(_ueid)
                    continue

                # NETDATA::<eid>::<payload>  Download-throughput payload from server
                if txt.startswith("NETDATA::"):
                    try:
                        _dp = txt.split("::",2)
                        _deid = _dp[1] if len(_dp)>=2 else ""
                        _dpld = _dp[2] if len(_dp)>=3 else ""
                    except: continue
                    _net_test_record_downdata(_deid, len(_dpld))
                    continue

                # DELIVERED::<mid>  (private msg receipt)
                if txt.startswith("DELIVERED::"):
                    try: mid = txt.split("::", 1)[1].strip()
                    except: continue
                    obj = widget_map.get(mid)
                    if obj and obj["is_me"]:
                        root.after(0, lambda o=obj:
                            o["tick"].config(text=" ✓✓", fg="#53bdeb"))
                    continue

                # DELETE_PERM::<mid>::<user>
                if txt.startswith("DELETE_PERM::"):
                    try: _, mid, _ = txt.split("::", 2)
                    except: continue
                    root.after(0, _del_local, mid)
                    continue

                # MSG::<sender>::<mid>::<content>::<ts>::<ftype>::<fpath>::<chat_key>::<reply_mid>
                if txt.startswith("MSG::"):
                    p = txt.split("::")
                    while len(p) < 9: p.append("")
                    _, sender, mid, content, ts, ftype, fpath, chat_key, reply_mid = p[:9]
                    chat_key = chat_key or "Group"
                    ftype    = ftype    or "text"

                    # ── PRIVATE ROUTING FIX ───────────────────────────────
                    # If chat_key == my username, the msg was sent TO me
                    # re-key to sender so it goes into my chat with that sender
                    if chat_key == username:
                        chat_key = sender

                    # For LIVE messages: skip echo (we already showed it locally).
                    # For HISTORY messages: sender==username is VALID — show on right.
                    # We distinguish by checking if mid is already in msg_store.
                    if sender.strip().lower() == username.strip().lower():
                        if mid in msg_store:
                            continue  # already rendered locally — skip
                        # else: this is history — fall through and render

                    # For file/image/voice history: reconstruct local path
                    # fpath field = safe filename stored on server
                    # content field = [file::originalname] — not a path
                    resolved_content = content
                    if ftype in ("image","voice","video","file") and fpath:
                        if ftype == "voice":
                            local_path = os.path.join(VOICE_DIR, fpath)
                        else:
                            local_path = os.path.join(RECV_DIR, fpath)
                        if os.path.exists(local_path):
                            resolved_content = local_path
                        else:
                            # File not on this machine — keep fpath as marker
                            # so render_msg can show a Download button
                            resolved_content = "MISSING::" + fpath

                    msg = {
                        "mid": mid, "sender": sender,
                        "content": resolved_content, "ftype": ftype,
                        "ts": ts, "chat_key": chat_key,
                        "reply_to": reply_mid or None,
                        "orig_fname": fpath  # keep safe filename for download
                    }
                    root.after(0, _store_and_show, msg)
                    # Send seen receipt — PRIVATE chats only (not Group),
                    # since a single "seen" tick doesn't meaningfully
                    # represent "read by everyone" in a group conversation.
                    if chat_key != "Group":
                        try:
                            tcp.sendall(
                                f"SEEN::{mid}::{username}\n".encode())
                        except: pass
                    continue

                # FILE::<sender>::<mid>::<fname>::<size>::<ftype>::<chat_key>
                if txt.startswith("FILE::"):
                    try:
                        p = txt.split("::", 6)
                        while len(p) < 7: p.append("")
                        _, sender, mid, fname, size_s, ftype, chat_key = p[:7]
                        chat_key = chat_key or "Group"
                        size = int(size_s)
                    except: continue

                    # Same private routing fix for files
                    if chat_key == username:
                        chat_key = sender

                    fb = b""
                    while len(fb) < size:
                        chunk = tcp.recv(min(8192, size - len(fb)))
                        if not chunk: break
                        fb += chunk

                    # fname is now the safe filename (server sends safe name)
                    dest_dir = (VOICE_DIR if ftype == "voice" else RECV_DIR)
                    path = os.path.join(dest_dir, fname)
                    try:
                        with open(path, "wb") as f: f.write(fb)
                    except: pass

                    msg = {
                        "mid": mid, "sender": sender,
                        "content": path, "ftype": ftype,
                        "ts": datetime.now().isoformat(),
                        "chat_key": chat_key,
                        "orig_fname": fname
                    }
                    root.after(0, _store_and_show, msg)
                    continue

        except Exception: break

    root.after(0, lambda: messagebox.showwarning(
        "Disconnected", "Lost connection to server."))

# ══════════════════════════════════════════════════════════════════════════════
# NETWORK HELPERS
# ══════════════════════════════════════════════════════════════════════════════
def _discover_server(timeout=2.0):
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
        s.settimeout(timeout)
        s.sendto(b"LANCHAT_DISCOVER", ("<broadcast>", DISC_PORT))
        data, _ = s.recvfrom(1024)
        txt = data.decode()
        if txt.startswith("LANCHAT_REPLY::"):
            return txt.split("::", 1)[1]
    except: return None
    finally:
        try: s.close()
        except: pass

def _get_ip(status_lbl):
    ip = l_ip.get().strip()
    if not ip:
        status_lbl.config(text="🔍 Searching for server...", fg="#555")
        auth_frame.update_idletasks()
        ip = _discover_server()
    if not ip:
        status_lbl.config(
            text="❌ Server not found. Enter IP manually.", fg="red")
    return ip

# ══════════════════════════════════════════════════════════════════════════════
# AUTH ACTIONS
# ══════════════════════════════════════════════════════════════════════════════
def _enter_chat(canonical, ip_used):
    """Switch from auth screen to chat UI."""
    global username, server_ip
    username   = canonical
    server_ip  = ip_used
    _load_read_state()
    ph = get_avatar(username, 38)
    av_lbl.config(image=ph); av_lbl.image = ph
    nick_lbl.config(text=username)
    threading.Thread(target=_recv_loop, daemon=True).start()
    threading.Thread(target=_clip_monitor, daemon=True).start()
    auth_frame.place_forget()
    paned.pack(fill=tk.BOTH, expand=True)
    _switch_chat("Group")
    apply_theme()

def do_login():
    global tcp
    ip = _get_ip(l_status)
    if not ip: return
    u = l_u.get().strip(); p = l_p.get().strip()
    if not u or not p:
        l_status.config(text="❌ Enter username and password", fg="red")
        return
    l_status.config(text="Connecting...", fg="#555")
    auth_frame.update_idletasks()
    try:
        tcp = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        tcp.connect((ip, PORT))
        tcp.recv(4096)   # AUTH::READY
        tcp.sendall(f"AUTH::LOGIN::{u}::{shpw(p)}\n".encode())
        resp = tcp.recv(4096).decode().strip()
        if not resp.startswith("AUTH::OK"):
            tcp.close(); tcp = None
            l_status.config(
                text="❌ " + resp.replace("AUTH::FAIL::", "").strip(),
                fg="red")
            return
        canonical = resp.split("::")[2] if resp.count("::") >= 2 else u
        _enter_chat(canonical, ip)
    except Exception as e:
        if tcp:
            try: tcp.close()
            except: pass
        tcp = None
        l_status.config(text=f"❌ {e}", fg="red")

def do_register():
    ip = _get_ip(r_status)
    if not ip: return
    u   = r_u.get().strip()
    fn  = r_fn.get().strip()
    ln  = r_ln.get().strip()
    p   = r_p.get().strip()
    p2  = r_p2.get().strip()

    if len(u) < 3:
        r_status.config(text="❌ Username: min 3 characters", fg="red"); return
    if not all(c.isalnum() or c in "_-" for c in u):
        r_status.config(
            text="❌ Username: letters, numbers, _ or - only", fg="red")
        return
    if not fn:
        r_status.config(text="❌ First name is required", fg="red"); return
    if not ln:
        r_status.config(text="❌ Last name is required",  fg="red"); return
    if len(p) < MIN_PW:
        r_status.config(
            text=f"❌ Password: min {MIN_PW} characters", fg="red"); return
    if p != p2:
        r_status.config(text="❌ Passwords do not match", fg="red"); return

    r_status.config(text="Registering...", fg="#555")
    auth_frame.update_idletasks()
    try:
        tmp = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        tmp.connect((ip, PORT)); tmp.recv(4096)
        tmp.sendall(f"AUTH::REGISTER::{u}::{shpw(p)}\n".encode())
        res = tmp.recv(4096).decode().strip(); tmp.close()
        if "OK" in res:
            if _rav[0]:
                try:
                    Image.open(_rav[0]).save(
                        os.path.join(AVATAR_DIR, f"{u}.png"))
                    avatar_cache.clear()
                except: pass
            r_status.config(
                text="✅ Account created! Go back and Login.", fg="green")
        else:
            r_status.config(
                text="❌ " + res.replace("AUTH::FAIL::", "").strip(),
                fg="red")
    except Exception as e:
        r_status.config(text=f"❌ {e}", fg="red")

def do_reset():
    ip = _get_ip(l_status)
    if not ip: return
    u = l_u.get().strip(); p = l_p.get().strip()
    if not u or not p:
        l_status.config(
            text="❌ Enter username and new password", fg="red"); return
    try:
        tmp = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        tmp.connect((ip, PORT)); tmp.recv(4096)
        tmp.sendall(f"AUTH::RESET::{u}::{shpw(p)}\n".encode())
        res = tmp.recv(4096).decode().strip(); tmp.close()
        if "OK" in res:
            l_status.config(
                text="✅ Password reset! You can login now.", fg="green")
        else:
            l_status.config(
                text="❌ " + res.replace("AUTH::FAIL::", "").strip(),
                fg="red")
    except Exception as e:
        l_status.config(text=f"❌ {e}", fg="red")

def do_logout():
    global tcp, username, server_ip, current_chat
    if not messagebox.askyesno("Logout", "Are you sure you want to logout?"):
        return
    try:
        if tcp: tcp.close()
    except: pass
    tcp = None; username = None; server_ip = ""; current_chat = "Group"
    # Clear state
    msg_store.clear(); chat_lists.clear(); chat_lists["Group"] = []
    unread.clear(); online_users.clear(); typing_jobs.clear()
    date_shown.clear(); widget_map.clear()
    for w in msgs_frame.winfo_children(): w.destroy()
    for w in conv_inner.winfo_children(): w.destroy()
    nick_lbl.config(text="Not logged in")
    l_u.delete(0, tk.END); l_p.delete(0, tk.END)
    l_status.config(text="", fg="red")
    paned.pack_forget()
    login_card.place(relx=0.5, rely=0.5, anchor="center",
                     width=440, height=330)
    auth_frame.place(relx=0, rely=0, relwidth=1, relheight=1)

# ── Auth buttons ──────────────────────────────────────────────────────────────
tk.Button(_lb, text="Register",
          command=show_reg,
          bg="#1a73e8", fg="white", relief=tk.FLAT,
          font=("Segoe UI", 9, "bold"), padx=10,
          cursor="hand2").pack(side=tk.LEFT)

tk.Button(_lb, text="Forgot / Reset",
          command=do_reset,
          bg="#888888", fg="white", relief=tk.FLAT,
          font=("Segoe UI", 9), padx=10,
          cursor="hand2").pack(side=tk.LEFT, padx=6)

tk.Button(_lb, text="  Login  ",
          command=do_login,
          bg="#075e54", fg="white", relief=tk.FLAT,
          font=("Segoe UI", 10, "bold"), padx=16,
          cursor="hand2").pack(side=tk.RIGHT)

# Register create button
tk.Button(_rb, text="  Create Account  ",
          command=do_register,
          bg="#075e54", fg="white", relief=tk.FLAT,
          font=("Segoe UI", 10, "bold"), padx=16,
          cursor="hand2").pack(side=tk.RIGHT)

# Logout
logout_btn.config(command=do_logout)

# ── Bindings ──────────────────────────────────────────────────────────────────
entry_box.bind("<Return>",   _send_text)
entry_box.bind("<KeyPress>", _send_typing)
send_btn.config(command=lambda: _send_text())
file_btn.config(command=_send_file)

# ── Start ─────────────────────────────────────────────────────────────────────
apply_theme()
root.mainloop()