# ─────────────────────────────────────────────────────────────────────────────
# LAN Chat — Server
# ─────────────────────────────────────────────────────────────────────────────
import tkinter as tk
from tkinter import scrolledtext
import threading, socket, sqlite3, os, datetime

HOST     = "0.0.0.0"
PORT     = 5000
UDP_PORT = 5001
BASE     = os.path.abspath(".")
DB_U     = os.path.join(BASE, "users.db")
DB_M     = os.path.join(BASE, "messages.db")

for _d in ["files/received", "files/voice", "files/avatars"]:
    os.makedirs(os.path.join(BASE, _d), exist_ok=True)

# ── DATABASE ──────────────────────────────────────────────────────────────────
def db_init():
    c = sqlite3.connect(DB_U)
    c.execute("""CREATE TABLE IF NOT EXISTS users(
        id INTEGER PRIMARY KEY, username TEXT UNIQUE,
        password TEXT, created_at TEXT)""")
    c.commit(); c.close()
    c = sqlite3.connect(DB_M)
    c.execute("""CREATE TABLE IF NOT EXISTS messages(
        id INTEGER PRIMARY KEY, msg_id TEXT UNIQUE,
        sender TEXT, content TEXT, timestamp TEXT,
        ftype TEXT DEFAULT 'text', fpath TEXT DEFAULT '',
        chat_key TEXT DEFAULT 'Group', reply_mid TEXT DEFAULT '')""")
    c.commit(); c.close()

def db_register(u, pw):
    try:
        c = sqlite3.connect(DB_U)
        if c.execute("SELECT 1 FROM users WHERE LOWER(username)=?", (u.lower(),)).fetchone():
            c.close(); return False, "Username already taken"
        c.execute("INSERT INTO users(username,password,created_at) VALUES(?,?,?)",
                  (u, pw, datetime.datetime.now().isoformat()))
        c.commit(); c.close(); return True, "OK"
    except Exception as e: return False, str(e)

def db_login(u, pw):
    c = sqlite3.connect(DB_U)
    row = c.execute("SELECT username,password FROM users WHERE LOWER(username)=?", (u.lower(),)).fetchone()
    c.close()
    if not row or row[1] != pw: return False, None
    return True, row[0]

def db_reset(u, pw):
    c = sqlite3.connect(DB_U)
    if not c.execute("SELECT 1 FROM users WHERE LOWER(username)=?", (u.lower(),)).fetchone():
        c.close(); return False, "User not found"
    c.execute("UPDATE users SET password=? WHERE LOWER(username)=?", (pw, u.lower()))
    c.commit(); c.close(); return True, "OK"

def db_is_new(u):
    try:
        c = sqlite3.connect(DB_M)
        n = c.execute("SELECT COUNT(*) FROM messages WHERE LOWER(sender)=?", (u.lower(),)).fetchone()[0]
        c.close(); return n == 0
    except: return True

def db_save(mid, sender, content, ftype="text", fpath="", chat_key="Group", reply_mid=""):
    def _run():
        try:
            c = sqlite3.connect(DB_M)
            c.execute(
                "INSERT OR IGNORE INTO messages"
                "(msg_id,sender,content,timestamp,ftype,fpath,chat_key,reply_mid)"
                " VALUES(?,?,?,?,?,?,?,?)",
                (mid, sender, content, datetime.datetime.now().isoformat(),
                 ftype, fpath, chat_key, reply_mid))
            c.commit(); c.close()
        except: pass
    threading.Thread(target=_run, daemon=True).start()

def db_history(limit=500):
    try:
        c = sqlite3.connect(DB_M)
        rows = c.execute(
            "SELECT msg_id,sender,content,timestamp,ftype,fpath,chat_key,reply_mid"
            " FROM messages ORDER BY id ASC LIMIT ?", (limit,)).fetchall()
        c.close(); return rows
    except: return []

def db_delete(mid):
    try:
        c = sqlite3.connect(DB_M)
        c.execute("DELETE FROM messages WHERE msg_id=?", (mid,))
        c.commit(); c.close()
    except: pass

# ── SERVER STATE ──────────────────────────────────────────────────────────────
clients  = {}          # { username -> socket }
lock     = threading.Lock()
srv_sock = None
running  = False

def tx(conn, line):
    try: conn.sendall((line + "\n").encode("utf-8"))
    except: pass

def txb(conn, data):
    try: conn.sendall(data)
    except: pass

def broadcast(line, exclude=None):
    with lock: tgts = list(clients.items())
    for u, c in tgts:
        if u == exclude: continue
        try: c.sendall((line + "\n").encode("utf-8"))
        except:
            with lock: clients.pop(u, None)

def broadcast_bytes(data, exclude=None):
    with lock: tgts = list(clients.items())
    for u, c in tgts:
        if u == exclude: continue
        try: c.sendall(data)
        except: pass

def user_list():
    with lock: names = list(clients.keys())
    broadcast("USERS::" + ",".join(names))

def get_conn(u):
    with lock: return clients.get(u)

# ── GUI LOG ───────────────────────────────────────────────────────────────────
_log_widget = None

def log(msg):
    ts = datetime.datetime.now().strftime("%H:%M:%S")
    line = f"[{ts}] {msg}"
    print(line)
    if _log_widget:
        try:
            _log_widget.config(state=tk.NORMAL)
            _log_widget.insert(tk.END, line + "\n")
            _log_widget.see(tk.END)
            _log_widget.config(state=tk.DISABLED)
        except: pass

# ── CLIENT HANDLER ────────────────────────────────────────────────────────────
def handle_client(conn, addr):
    # ── AUTH ──────────────────────────────────────────────────────────────────
    try:
        tx(conn, "AUTH::READY")
        line = conn.recv(4096).decode("utf-8", errors="ignore").strip()
    except: conn.close(); return

    if line.startswith("AUTH::REGISTER::"):
        try: _, _, u, pw = line.split("::", 3)
        except: tx(conn, "AUTH::FAIL::Bad format"); conn.close(); return
        ok, msg = db_register(u, pw)
        tx(conn, "AUTH::OK" if ok else f"AUTH::FAIL::{msg}")
        if ok: log(f"New user registered: {u}")
        conn.close(); return

    if line.startswith("AUTH::RESET::"):
        try: _, _, u, pw = line.split("::", 3)
        except: tx(conn, "AUTH::FAIL::Bad format"); conn.close(); return
        ok, msg = db_reset(u, pw)
        tx(conn, "AUTH::OK" if ok else f"AUTH::FAIL::{msg}")
        conn.close(); return

    if not line.startswith("AUTH::LOGIN::"):
        tx(conn, "AUTH::FAIL::Unknown command"); conn.close(); return
    try: _, _, u, pw = line.split("::", 3)
    except: tx(conn, "AUTH::FAIL::Bad format"); conn.close(); return

    ok, name = db_login(u, pw)
    if not ok:
        tx(conn, "AUTH::FAIL::Incorrect username or password")
        conn.close(); return

    tx(conn, f"AUTH::OK::{name}")
    with lock: clients[name] = conn
    log(f"{name} connected from {addr[0]}")

    ts = datetime.datetime.now().isoformat()
    tx(conn, f"MSG::Server::sys-welcome::Welcome {name}!::{ts}::text::::Group::")
    broadcast(f"MSG::Server::sys-join-{name}::{name} joined the chat!::{ts}::text::::Group::",
              exclude=name)

    # ── HISTORY (returning users only) ────────────────────────────────────────
    if not db_is_new(name):
        for mid, sender, content, mts, ftype, fpath, ck, rmid in db_history():
            ck = ck or "Group"
            ft = ftype or "text"
            if ck == "Group" or name in (ck, sender):
                if ck != "Group":
                    send_ck = sender if name == ck else ck
                else:
                    send_ck = ck
                try:
                    conn.sendall(
                        f"MSG::{sender}::{mid}::{content}::{mts}"
                        f"::{ft}::{fpath}::{send_ck}::{rmid}\n".encode("utf-8"))
                except: pass

    user_list()

    # ── MAIN LOOP ─────────────────────────────────────────────────────────────
    buf = b""
    while running:
        try:
            data = conn.recv(8192)
            if not data: raise ConnectionResetError()
            buf += data

            while b"\n" in buf:
                raw, buf = buf.split(b"\n", 1)
                txt = raw.decode("utf-8", errors="ignore").strip()
                if not txt: continue

                # TEXT MESSAGE
                # In:  MSG::<mid>::<content>::<chat_key>::<reply_mid>
                # Out: MSG::<sender>::<mid>::<content>::<ts>::text::::<chat_key>::<reply_mid>
                if txt.startswith("MSG::"):
                    try:
                        p = txt.split("::", 4)
                        while len(p) < 5: p.append("")
                        _, mid, content, chat_key, reply_mid = p[:5]
                        chat_key = chat_key or "Group"
                    except: continue

                    ts      = datetime.datetime.now().isoformat()
                    payload = (f"MSG::{name}::{mid}::{content}::{ts}"
                               f"::text::::{chat_key}::{reply_mid}")

                    # BROADCAST FIRST — save DB after (no delay)
                    if chat_key == "Group":
                        broadcast(payload, exclude=name)
                    else:
                        dest = get_conn(chat_key)
                        if dest: tx(dest, payload)
                        tx(conn, f"DELIVERED::{mid}")

                    db_save(mid, name, content, chat_key=chat_key, reply_mid=reply_mid)
                    log(f"{name}→{'Group' if chat_key=='Group' else chat_key}: {content[:40]}")
                    continue

                # FILE MESSAGE
                # In:  FILE::<mid>::<fname>::<size>::<ftype>::<chat_key>
                # Out: FILE::<sender>::<mid>::<fname>::<size>::<ftype>::<chat_key>
                if txt.startswith("FILE::"):
                    try:
                        p = txt.split("::", 5)
                        while len(p) < 6: p.append("")
                        _, mid, fname, size_s, ftype, chat_key = p[:6]
                        chat_key = chat_key or "Group"
                        size = int(size_s)
                    except: continue

                    fb = b""
                    while len(fb) < size:
                        chunk = conn.recv(min(8192, size - len(fb)))
                        if not chunk: raise ConnectionResetError()
                        fb += chunk

                    safe = datetime.datetime.now().strftime("%Y%m%d%H%M%S") + "_" + fname
                    ddir = os.path.join(BASE, "files", "voice" if ftype == "voice" else "received")
                    fpath_full = os.path.join(ddir, safe)
                    try:
                        with open(fpath_full, "wb") as f: f.write(fb)
                    except: pass

                    hdr = (f"FILE::{name}::{mid}::{safe}::{size}"
                           f"::{ftype}::{chat_key}\n").encode()

                    if chat_key == "Group":
                        broadcast_bytes(hdr, exclude=name)
                        broadcast_bytes(fb,  exclude=name)
                    else:
                        dest = get_conn(chat_key)
                        if dest: txb(dest, hdr); txb(dest, fb)
                        tx(conn, f"DELIVERED::{mid}")

                    db_save(mid, name, f"[file::{fname}]", ftype=ftype, fpath=safe, chat_key=chat_key)
                    log(f"{name} sent file: {fname} ({ftype})")
                    continue

                # TYPING::<user>::<chat_key>
                if txt.startswith("TYPING::"):
                    p  = txt.split("::")
                    ck = p[2] if len(p) >= 3 else "Group"
                    if ck == "Group": broadcast(txt, exclude=name)
                    else:
                        d = get_conn(ck)
                        if d: tx(d, txt)
                    continue

                # REACT::<mid>::<user>::<emoji>
                if txt.startswith("REACT::"):
                    broadcast(txt); continue

                # CLIP::<sender>::<chat_key>::<content>  Clipboard Sync
                # Routed exactly like private/group messages: a private share
                # (chat_key = a specific username) goes ONLY to that recipient,
                # never to the whole group — private shares can never leak
                # into Group Chat.
                if txt.startswith("CLIP::"):
                    try:
                        _cp = txt.split("::", 3)
                        _cck = _cp[2] if len(_cp) >= 3 else "Group"
                    except: _cck = "Group"
                    if _cck == "Group":
                        broadcast(txt, exclude=name)
                    else:
                        _cdest = get_conn(_cck)
                        if _cdest: tx(_cdest, txt)
                    continue

                # PING::<echo_id>::<payload>  Network Performance — latency test
                # Server echoes back immediately (used for latency + packet loss).
                if txt.startswith("PING::"):
                    tx(conn, "PONG::" + txt[6:])
                    continue

                # NETUP::<echo_id>::<payload>  Network Performance — upload test
                # Client is measuring how fast IT can push data to this server;
                # server only needs to acknowledge receipt (tiny reply).
                if txt.startswith("NETUP::"):
                    try:
                        _up = txt.split("::", 2)
                        _ueid = _up[1] if len(_up) >= 2 else ""
                    except: continue
                    tx(conn, "NETACK::" + _ueid)
                    continue

                # NETDOWN::<echo_id>::<size>  Network Performance — download test
                # Client requests <size> bytes; server sends that much data back
                # so the client can measure real download throughput from this
                # LAN server (not localhost, not the internet).
                if txt.startswith("NETDOWN::"):
                    try:
                        _dp = txt.split("::", 2)
                        _deid = _dp[1] if len(_dp) >= 2 else ""
                        _dsize = int(_dp[2]) if len(_dp) >= 3 and _dp[2].isdigit() else 0
                        _dsize = max(0, min(_dsize, 2_000_000))  # cap at 2MB for safety
                    except: continue
                    _payload = "Y" * _dsize
                    tx(conn, "NETDATA::" + _deid + "::" + _payload)
                    continue

                # SEEN::<mid>::<user>
                if txt.startswith("SEEN::"):
                    broadcast(txt); continue

                # DELETE_PERM::<mid>::<user>
                if txt.startswith("DELETE_PERM::"):
                    try: _, mid, _ = txt.split("::", 2)
                    except: continue
                    db_delete(mid)
                    broadcast(f"DELETE_PERM::{mid}::{name}")
                    continue

        except (ConnectionResetError, OSError): break
        except Exception as ex: log(f"ERR {name}: {ex}"); break

    with lock: clients.pop(name, None)
    try: conn.close()
    except: pass
    log(f"{name} disconnected")
    ts = datetime.datetime.now().isoformat()
    broadcast(f"MSG::Server::sys-left-{name}::{name} left.::{ts}::text::::Group::")
    user_list()


def udp_discovery():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.bind(("", UDP_PORT))
        while running:
            try:
                data, addr = s.recvfrom(2048)
                if data.decode(errors="ignore").strip() == "LANCHAT_DISCOVER":
                    ip = socket.gethostbyname(socket.gethostname())
                    s.sendto(f"LANCHAT_REPLY::{ip}".encode(), addr)
            except: pass
        s.close()
    except: pass

def accept_loop():
    global running
    while running:
        try:
            conn, addr = srv_sock.accept()
            threading.Thread(target=handle_client, args=(conn, addr), daemon=True).start()
        except: break

# ── GUI ───────────────────────────────────────────────────────────────────────
root = tk.Tk()
root.title("LAN Chat Server")
root.geometry("640x520")
root.minsize(560, 440)
root.resizable(True, True)
try:
    ico = os.path.join(BASE, "icon.ico")
    if os.path.exists(ico): root.iconbitmap(ico)
except: pass

# Colours
CLR_ON  = "#1db954"
CLR_OFF = "#e74c3c"
CLR_BG  = "#1e1e2e"
CLR_PAN = "#2a2a3e"
CLR_TXT = "#cdd6f4"
CLR_SUB = "#9399b2"

root.config(bg=CLR_BG)

# Title bar
title_fr = tk.Frame(root, bg=CLR_PAN, pady=14)
title_fr.pack(fill=tk.X)
tk.Label(title_fr, text="💬  LAN Chat Server", bg=CLR_PAN,
         fg=CLR_TXT, font=("Segoe UI", 16, "bold")).pack(side=tk.LEFT, padx=20)

status_dot = tk.Label(title_fr, text="⚫", bg=CLR_PAN, fg=CLR_OFF, font=("Segoe UI", 14))
status_dot.pack(side=tk.LEFT)
status_lbl = tk.Label(title_fr, text="Offline", bg=CLR_PAN, fg=CLR_OFF, font=("Segoe UI", 11, "bold"))
status_lbl.pack(side=tk.LEFT, padx=6)

# Info bar
ip_fr = tk.Frame(root, bg=CLR_BG, pady=10)
ip_fr.pack(fill=tk.X, padx=20)

def info_pair(parent, label):
    box = tk.Frame(parent, bg=CLR_BG)
    box.pack(side=tk.LEFT, padx=(0, 24))
    tk.Label(box, text=label, bg=CLR_BG, fg=CLR_SUB, font=("Segoe UI", 8)).pack(anchor="w")
    val = tk.Label(box, text="—", bg=CLR_BG, fg="#89dceb", font=("Segoe UI", 11, "bold"))
    val.pack(anchor="w")
    return val

ip_val   = info_pair(ip_fr, "SERVER IP")
port_lbl = info_pair(ip_fr, "PORT")
port_lbl.config(text=str(PORT))
conn_lbl = info_pair(ip_fr, "CLIENTS ONLINE")
conn_lbl.config(text="0")

# Log area
log_fr = tk.Frame(root, bg=CLR_BG)
log_fr.pack(fill=tk.BOTH, expand=True, padx=20, pady=(4, 8))
tk.Label(log_fr, text="Activity Log", bg=CLR_BG,
         fg=CLR_TXT, font=("Segoe UI", 9, "bold")).pack(anchor="w")
log_box = scrolledtext.ScrolledText(
    log_fr, bg="#12121e", fg="#a6e3a1",
    font=("Consolas", 9), relief=tk.FLAT,
    state=tk.DISABLED, wrap=tk.WORD)
log_box.pack(fill=tk.BOTH, expand=True, pady=(4, 0))
_log_widget = log_box

# Buttons
btn_fr = tk.Frame(root, bg=CLR_BG, pady=12)
btn_fr.pack(fill=tk.X, padx=20)

def start_server():
    global srv_sock, running
    if running: return
    try:
        db_init()
        srv_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        srv_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        srv_sock.bind((HOST, PORT))
        srv_sock.listen(60)
        running = True
        ip = socket.gethostbyname(socket.gethostname())
        ip_val.config(text=ip)
        status_dot.config(text="🟢", fg=CLR_ON)
        status_lbl.config(text="Online", fg=CLR_ON)
        start_btn.config(state=tk.DISABLED, bg="#555")
        stop_btn.config(state=tk.NORMAL, bg=CLR_OFF)
        log(f"Server started on {ip}:{PORT}")
        log("Waiting for clients to connect...")
        threading.Thread(target=accept_loop, daemon=True).start()
        threading.Thread(target=udp_discovery, daemon=True).start()
        update_conn_count()
    except Exception as e:
        log(f"Error starting server: {e}")

def stop_server():
    global running
    if not running: return
    running = False
    try: srv_sock.close()
    except: pass
    with lock:
        for c in clients.values():
            try: c.close()
            except: pass
        clients.clear()
    status_dot.config(text="⚫", fg=CLR_OFF)
    status_lbl.config(text="Offline", fg=CLR_OFF)
    ip_val.config(text="—")
    start_btn.config(state=tk.NORMAL, bg=CLR_ON)
    stop_btn.config(state=tk.DISABLED, bg="#555")
    conn_lbl.config(text="0")
    log("Server stopped.")

def update_conn_count():
    if not running: return
    with lock: n = len(clients)
    conn_lbl.config(text=str(n))
    root.after(1000, update_conn_count)

start_btn = tk.Button(btn_fr, text="▶  START SERVER",
                      command=start_server,
                      bg=CLR_ON, fg="white",
                      font=("Segoe UI", 12, "bold"),
                      relief=tk.FLAT, padx=24, pady=10,
                      cursor="hand2", activebackground="#17a844")
start_btn.pack(side=tk.LEFT)

stop_btn = tk.Button(btn_fr, text="⏹  STOP SERVER",
                     command=stop_server,
                     bg="#555", fg="white",
                     font=("Segoe UI", 12, "bold"),
                     relief=tk.FLAT, padx=24, pady=10,
                     cursor="hand2", state=tk.DISABLED)
stop_btn.pack(side=tk.LEFT, padx=16)

clear_btn = tk.Button(btn_fr, text="🗑 Clear Log",
                      command=lambda: (log_box.config(state=tk.NORMAL),
                                       log_box.delete("1.0", tk.END),
                                       log_box.config(state=tk.DISABLED)),
                      bg=CLR_PAN, fg=CLR_TXT,
                      font=("Segoe UI", 9), relief=tk.FLAT,
                      padx=10, pady=10, cursor="hand2")
clear_btn.pack(side=tk.RIGHT)

def on_close():
    if running: stop_server()
    root.destroy()

root.protocol("WM_DELETE_WINDOW", on_close)
log("LAN Chat Server ready. Press START to begin.")
log(f"Database: {DB_U}")
root.mainloop()