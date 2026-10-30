from flask import Flask, render_template, request, redirect, url_for, flash, send_file, session, g, abort, has_request_context
import sqlite3, os, shutil, secrets, hashlib, hmac, time, re, logging, functools
from logging.handlers import RotatingFileHandler
from datetime import datetime, timedelta
from io import BytesIO
from urllib.parse import urlparse
import tempfile
from werkzeug.security import generate_password_hash, check_password_hash

ROOT = os.path.dirname(os.path.abspath(__file__))
# Data location. Defaults to the program folder for backward compatibility with
# existing installations; set QD_DATA_DIR to keep patient data and secrets
# outside the code folder (recommended).
DATA_DIR = os.environ.get("QD_DATA_DIR") or ROOT
os.makedirs(DATA_DIR, exist_ok=True)
DB = os.path.join(DATA_DIR, "quality_dental.db")

# The old hard-coded fallback key is public (it is in the source code), so it must never be used.
LEGACY_DEFAULT_KEY = "change-this-quality-dental-key-before-online-use"

def _load_secret_key():
    """SECRET_KEY from the environment, otherwise a per-installation random key stored in DATA_DIR."""
    env_key = os.environ.get("SECRET_KEY")
    if env_key:
        if env_key == LEGACY_DEFAULT_KEY or len(env_key) < 32:
            raise RuntimeError("SECRET_KEY is the old public default or shorter than 32 characters. Refusing to start.")
        return env_key
    path = os.path.join(DATA_DIR, ".qd_secret_key")
    if os.path.exists(path):
        with open(path, encoding="utf-8") as f:
            key = f.read().strip()
        if len(key) < 32 or key == LEGACY_DEFAULT_KEY:
            raise RuntimeError(f"Invalid secret key in {path}. Delete it to generate a new one.")
        return key
    key = secrets.token_urlsafe(48)
    with open(path, "w", encoding="utf-8") as f:
        f.write(key)
    return key

app = Flask(__name__)
app.secret_key = _load_secret_key()

IDLE_TIMEOUT = int(os.environ.get("QD_IDLE_MINUTES", "15")) * 60   # auto-logoff after inactivity
ABSOLUTE_TIMEOUT = 8 * 3600                                          # one working day
MAX_FAILED_LOGINS = 5
LOCKOUT_SECONDS = 15 * 60
IP_MAX_FAILURES = 30
IP_WINDOW = 15 * 60
MIN_PASSWORD_LENGTH = 10

app.config.update(
    MAX_CONTENT_LENGTH=20 * 1024 * 1024,   # caps backup uploads (disk-fill / DoS protection)
    SESSION_COOKIE_NAME="qd_session",
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=os.environ.get("QD_HTTPS") == "1",   # enable once served over HTTPS
    PERMANENT_SESSION_LIFETIME=timedelta(seconds=ABSOLUTE_TIMEOUT),
)

# Technical error log (never write patient data here).
_log_dir = os.path.join(DATA_DIR, "logs")
os.makedirs(_log_dir, exist_ok=True)
_handler = RotatingFileHandler(os.path.join(_log_dir, "app.log"), maxBytes=1_000_000, backupCount=5, encoding="utf-8")
_handler.setLevel(logging.WARNING)
_handler.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
app.logger.addHandler(_handler)

def db():
    con = sqlite3.connect(DB, timeout=10)
    con.row_factory = sqlite3.Row
    return con

# Security tables. Kept separate so a restored backup can be given the *current* users and audit trail.
AUTH_SCHEMA = """
CREATE TABLE IF NOT EXISTS users(
  id INTEGER PRIMARY KEY AUTOINCREMENT, username TEXT NOT NULL UNIQUE COLLATE NOCASE, full_name TEXT,
  password_hash TEXT NOT NULL, role TEXT NOT NULL, active INTEGER NOT NULL DEFAULT 1,
  must_change_pw INTEGER NOT NULL DEFAULT 0, failed_count INTEGER NOT NULL DEFAULT 0, locked_until REAL,
  created_at TEXT DEFAULT CURRENT_TIMESTAMP, last_login TEXT);
CREATE TABLE IF NOT EXISTS user_sessions(
  id INTEGER PRIMARY KEY AUTOINCREMENT, token_hash TEXT NOT NULL UNIQUE, user_id INTEGER NOT NULL,
  created_at REAL NOT NULL, last_seen REAL NOT NULL, ip TEXT, user_agent TEXT, revoked INTEGER NOT NULL DEFAULT 0);
CREATE TABLE IF NOT EXISTS audit_log(
  id INTEGER PRIMARY KEY AUTOINCREMENT, ts TEXT NOT NULL, user_id INTEGER, username TEXT, role TEXT,
  action TEXT NOT NULL, entity TEXT, entity_id TEXT, ip TEXT, detail TEXT);
"""
AUTH_TABLES = ("users", "user_sessions", "audit_log")

def init_db():
    with db() as c:
        c.executescript("""
        CREATE TABLE IF NOT EXISTS patients(
          id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT NOT NULL, phone TEXT,
          age TEXT, notes TEXT, created_at TEXT DEFAULT CURRENT_TIMESTAMP);
        CREATE TABLE IF NOT EXISTS appointments(
          id INTEGER PRIMARY KEY AUTOINCREMENT, patient_id INTEGER, patient_name TEXT NOT NULL,
          appt_date TEXT NOT NULL, appt_time TEXT, reason TEXT, status TEXT DEFAULT 'محجوز');
        CREATE TABLE IF NOT EXISTS accounts(
          id INTEGER PRIMARY KEY AUTOINCREMENT, entry_date TEXT NOT NULL, kind TEXT NOT NULL,
          amount REAL NOT NULL, description TEXT, patient_id INTEGER REFERENCES patients(id));
        CREATE TABLE IF NOT EXISTS teeth(
          id INTEGER PRIMARY KEY AUTOINCREMENT, patient_id INTEGER NOT NULL, tooth TEXT NOT NULL,
          condition TEXT NOT NULL DEFAULT 'سليم', UNIQUE(patient_id,tooth));
        """)
        c.executescript(AUTH_SCHEMA)
        # Safe migration for databases created by earlier versions.
        cols = [r[1] for r in c.execute("PRAGMA table_info(accounts)").fetchall()]
        if "patient_id" not in cols:
            c.execute("ALTER TABLE accounts ADD COLUMN patient_id INTEGER REFERENCES patients(id)")
init_db()

# FDI: upper-right, upper-left, lower-left, lower-right
TEETH = [str(q)+str(n) for q in (1,2,3,4) for n in range(1,9)]
CONDITIONS = ['سليم', 'تسوس', 'حشو', 'مفقود / خلع', 'علاج عصب']
APPT_STATUSES = ['محجوز', 'حضر', 'لم يحضر', 'ملغي']
ACCOUNT_KINDS = ['إيراد', 'مصروف']

# ---------------------------------------------------------------- roles & permissions
ROLES = {"admin": "مدير النظام", "dentist": "طبيب", "receptionist": "استقبال", "accountant": "محاسب"}
_ALL = frozenset(ROLES)
_CLINICAL = frozenset({"admin", "dentist"})
_FRONT = frozenset({"admin", "dentist", "receptionist"})
PERMISSIONS = {
    "patients.view": _FRONT, "patients.edit": _FRONT, "patients.notes": _CLINICAL,
    "patients.delete": frozenset({"admin"}),
    "appointments.view": _FRONT, "appointments.edit": _FRONT, "appointments.delete": frozenset({"admin"}),
    "payments.record": _ALL,
    "accounts.view": frozenset({"admin", "dentist", "accountant"}), "accounts.edit": frozenset({"admin", "accountant"}),
    "odontogram": _CLINICAL,
    "assistant": _FRONT,
    "admin": frozenset({"admin"}),
}

def can(perm, user=None):
    user = user if user is not None else g.get("user")
    return bool(user) and user["role"] in PERMISSIONS.get(perm, ())

def require(*perms):
    """Server-side authorization guard. Hidden menu items are NOT security; this is."""
    def deco(fn):
        @functools.wraps(fn)
        def wrapper(*args, **kwargs):
            if not all(can(p) for p in perms):
                audit("access.denied", request.endpoint, next(iter(kwargs.values()), None), ",".join(perms))
                abort(403)
            return fn(*args, **kwargs)
        return wrapper
    return deco

# ---------------------------------------------------------------- audit trail
def audit(action, entity=None, entity_id=None, detail=None, con=None, username=None):
    """Append-only activity record. Pass `con` when inside an open write transaction. No clinical text."""
    u = g.get("user") if has_request_context() else None
    row = (datetime.now().isoformat(timespec="seconds"), u["id"] if u else None,
           u["username"] if u else username, u["role"] if u else None, action, entity,
           None if entity_id is None else str(entity_id),
           request.remote_addr if has_request_context() else None, detail)
    sql = "INSERT INTO audit_log(ts,user_id,username,role,action,entity,entity_id,ip,detail) VALUES(?,?,?,?,?,?,?,?,?)"
    if con is not None:
        con.execute(sql, row)
    else:
        with db() as c:
            c.execute(sql, row)

# ---------------------------------------------------------------- sessions, CSRF, passwords
def _hash_token(token):
    return hashlib.sha256(token.encode()).hexdigest()

def csrf_token():
    if "csrf" not in session:
        session["csrf"] = secrets.token_urlsafe(32)
    return session["csrf"]

def start_session(con, user):
    token = secrets.token_urlsafe(32)
    now = time.time()
    con.execute("INSERT INTO user_sessions(token_hash,user_id,created_at,last_seen,ip,user_agent) VALUES(?,?,?,?,?,?)",
                (_hash_token(token), user["id"], now, now, request.remote_addr, (request.user_agent.string or "")[:200]))
    session.clear()                      # new session at login (prevents session fixation)
    session.permanent = True
    session["sid"] = token
    session["csrf"] = secrets.token_urlsafe(32)

def revoke_sessions(con, user_id, keep_id=None):
    con.execute("UPDATE user_sessions SET revoked=1 WHERE user_id=? AND id IS NOT ?", (user_id, keep_id))

def password_problem(password, username=""):
    if len(password) < MIN_PASSWORD_LENGTH:
        return f"كلمة المرور يجب ألا تقل عن {MIN_PASSWORD_LENGTH} أحرف."
    if username and username.lower() in password.lower():
        return "كلمة المرور يجب ألا تحتوي على اسم المستخدم."
    if password.isdigit() or len(set(password)) < 4:
        return "كلمة المرور ضعيفة جدًا؛ استخدم خليطًا من الحروف والأرقام."
    return None

def create_user(username, password, role, full_name="", must_change_pw=False):
    """Used by create_admin.py, the users page and tests."""
    if role not in ROLES:
        raise ValueError("unknown role")
    with db() as c:
        cur = c.execute("INSERT INTO users(username,full_name,password_hash,role,must_change_pw) VALUES(?,?,?,?,?)",
                        (username, full_name, generate_password_hash(password), role, 1 if must_change_pw else 0))
        return cur.lastrowid

def _safe_next(target):
    if target and target.startswith("/") and not target.startswith("//") and "\\" not in target:
        return target
    return url_for("home")

PUBLIC_ENDPOINTS = {"login", "static"}
PASSWORD_CHANGE_ENDPOINTS = {"change_password", "logout", "static"}

@app.before_request
def authenticate_and_protect():
    g.user = None
    token = session.get("sid")
    if token:
        with db() as c:
            row = c.execute("""SELECT s.id AS sid_id, s.created_at AS s_created, s.last_seen, s.revoked, u.*
                               FROM user_sessions s JOIN users u ON u.id=s.user_id WHERE s.token_hash=?""",
                            (_hash_token(token),)).fetchone()
            now = time.time()
            if (row and not row["revoked"] and row["active"]
                    and now - row["last_seen"] <= IDLE_TIMEOUT and now - row["s_created"] <= ABSOLUTE_TIMEOUT):
                c.execute("UPDATE user_sessions SET last_seen=? WHERE id=?", (now, row["sid_id"]))
                g.user = row
                g.session_row_id = row["sid_id"]
            else:
                if row and not row["revoked"]:
                    c.execute("UPDATE user_sessions SET revoked=1 WHERE id=?", (row["sid_id"],))
                session.pop("sid", None)
                g.session_expired = bool(row)
    # Deny by default: every endpoint except login/static needs a valid session.
    if g.user is None and request.endpoint is not None and request.endpoint not in PUBLIC_ENDPOINTS:
        if g.get("session_expired"):
            flash("انتهت الجلسة لعدم النشاط. سجّل الدخول مرة أخرى.")
        nxt = request.full_path.rstrip("?") if request.method == "GET" else None
        return redirect(url_for("login", next=nxt))
    if request.method in ("POST", "PUT", "PATCH", "DELETE"):
        origin = request.headers.get("Origin")
        if origin is not None and (origin == "null" or urlparse(origin).netloc != request.host):
            abort(403)
        sent = request.form.get("csrf_token") or request.headers.get("X-CSRF-Token") or ""
        expected = session.get("csrf") or ""
        if not expected or not hmac.compare_digest(sent, expected):
            abort(400)
    if g.user is not None and g.user["must_change_pw"] and request.endpoint not in PASSWORD_CHANGE_ENDPOINTS:
        flash("يجب تغيير كلمة المرور المؤقتة قبل المتابعة.")
        return redirect(url_for("change_password"))

@app.after_request
def security_headers(resp):
    resp.headers.setdefault("X-Frame-Options", "DENY")
    resp.headers.setdefault("X-Content-Type-Options", "nosniff")
    resp.headers.setdefault("Referrer-Policy", "same-origin")
    resp.headers.setdefault("Content-Security-Policy",
        "default-src 'self'; script-src 'self' 'unsafe-inline'; "
        "style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; font-src 'self' https://fonts.gstatic.com; "
        "img-src 'self' data:; object-src 'none'; base-uri 'self'; form-action 'self'; frame-ancestors 'none'")
    if request.endpoint != "static":
        resp.headers["Cache-Control"] = "no-store"   # do not keep patient pages in browser cache
        resp.headers["Pragma"] = "no-cache"
    return resp

@app.context_processor
def inject_security():
    return {"current_user": g.get("user"), "can": can, "csrf_token": csrf_token, "ROLES": ROLES}

def _error_page(code, title, message):
    return render_template("error.html", code=code, title=title, message=message), code

@app.errorhandler(400)
def bad_request(e):
    return _error_page(400, "طلب غير صالح", "انتهت صلاحية النموذج أو أنه غير صالح. ارجع للصفحة وأعد المحاولة.")

@app.errorhandler(403)
def forbidden(e):
    return _error_page(403, "غير مصرح", "ليس لديك صلاحية للوصول إلى هذه الصفحة أو تنفيذ هذا الإجراء.")

@app.errorhandler(413)
def too_large(e):
    return _error_page(413, "الملف كبير جدًا", "حجم الملف يتجاوز الحد المسموح (20 ميجابايت).")

# ---------------------------------------------------------------- authentication routes
_ip_failures = {}
_DUMMY_HASH = generate_password_hash(secrets.token_urlsafe(16))
LOGIN_ERROR = "اسم المستخدم أو كلمة المرور غير صحيحة، أو الحساب مقفل مؤقتًا."

@app.route("/login", methods=["GET", "POST"])
def login():
    if g.user:
        return redirect(url_for("home"))
    if request.method == "POST":
        ip = request.remote_addr or "?"
        now = time.time()
        fails = [t for t in _ip_failures.get(ip, []) if now - t < IP_WINDOW]
        _ip_failures[ip] = fails
        username = request.form.get("username", "").strip()[:64]
        password = request.form.get("password", "")
        if len(fails) >= IP_MAX_FAILURES:
            audit("login.throttled", "ip", ip, username=username)
            return render_template("login.html", error="محاولات كثيرة. انتظر 15 دقيقة ثم حاول مرة أخرى."), 429
        with db() as c:
            user = c.execute("SELECT * FROM users WHERE username=?", (username,)).fetchone()
            if user is None or not user["active"] or (user["locked_until"] or 0) > now:
                check_password_hash(_DUMMY_HASH, password)          # equalize response time
                action = "login.locked" if user is not None and (user["locked_until"] or 0) > now else "login.failed"
                audit(action, "user", user["id"] if user else None, con=c, username=username)
            elif check_password_hash(user["password_hash"], password):
                c.execute("UPDATE users SET failed_count=0, locked_until=NULL, last_login=? WHERE id=?",
                          (datetime.now().isoformat(timespec="seconds"), user["id"]))
                start_session(c, user)
                g.user = user
                audit("login.success", "user", user["id"], con=c)
                return redirect(_safe_next(request.args.get("next")))
            else:
                failed = user["failed_count"] + 1
                if failed >= MAX_FAILED_LOGINS:
                    c.execute("UPDATE users SET failed_count=0, locked_until=? WHERE id=?", (now + LOCKOUT_SECONDS, user["id"]))
                    audit("login.lockout", "user", user["id"], con=c, username=username)
                else:
                    c.execute("UPDATE users SET failed_count=? WHERE id=?", (failed, user["id"]))
                    audit("login.failed", "user", user["id"], con=c, username=username)
        fails.append(now)
        return render_template("login.html", error=LOGIN_ERROR, username=username), 401
    return render_template("login.html")

@app.route("/logout", methods=["POST"])
def logout():
    with db() as c:
        c.execute("UPDATE user_sessions SET revoked=1 WHERE id=?", (g.session_row_id,))
        audit("logout", "user", g.user["id"], con=c)
    session.clear()
    flash("تم تسجيل الخروج.")
    return redirect(url_for("login"))

@app.route("/account/password", methods=["GET", "POST"])
def change_password():
    if request.method == "POST":
        current = request.form.get("current_password", "")
        new = request.form.get("new_password", "")
        confirm = request.form.get("confirm_password", "")
        with db() as c:
            row = c.execute("SELECT password_hash FROM users WHERE id=?", (g.user["id"],)).fetchone()
            if not check_password_hash(row["password_hash"], current):
                audit("password.change_failed", "user", g.user["id"], con=c)
                flash("كلمة المرور الحالية غير صحيحة.")
            elif new != confirm:
                flash("كلمتا المرور الجديدتان غير متطابقتين.")
            elif new == current:
                flash("اختر كلمة مرور مختلفة عن الحالية.")
            elif password_problem(new, g.user["username"]):
                flash(password_problem(new, g.user["username"]))
            else:
                c.execute("UPDATE users SET password_hash=?, must_change_pw=0 WHERE id=?",
                          (generate_password_hash(new), g.user["id"]))
                revoke_sessions(c, g.user["id"], keep_id=g.session_row_id)   # sign out other devices
                audit("password.changed", "user", g.user["id"], con=c)
                flash("تم تغيير كلمة المرور بنجاح.")
                return redirect(url_for("home"))
        return redirect(url_for("change_password"))
    return render_template("change_password.html", min_len=MIN_PASSWORD_LENGTH)

USERNAME_RE = re.compile(r"^[A-Za-z0-9._-]{3,32}$")

@app.route("/users", methods=["GET", "POST"])
@require("admin")
def users():
    with db() as c:
        if request.method == "POST":
            username = request.form.get("username", "").strip()
            full_name = request.form.get("full_name", "").strip()[:100]
            role = request.form.get("role", "")
            password = request.form.get("password", "")
            if not USERNAME_RE.match(username):
                flash("اسم المستخدم: 3-32 حرفًا إنجليزيًا أو أرقام أو . _ -")
            elif role not in ROLES:
                flash("اختر دورًا صحيحًا.")
            elif password_problem(password, username):
                flash(password_problem(password, username))
            elif c.execute("SELECT 1 FROM users WHERE username=?", (username,)).fetchone():
                flash("اسم المستخدم مستخدم بالفعل.")
            else:
                cur = c.execute("INSERT INTO users(username,full_name,password_hash,role,must_change_pw) VALUES(?,?,?,?,1)",
                                (username, full_name, generate_password_hash(password), role))
                audit("user.create", "user", cur.lastrowid, f"role={role}", con=c)
                flash("تم إنشاء المستخدم. سيُطلب منه تغيير كلمة المرور عند أول دخول.")
            return redirect(url_for("users"))
        rows = c.execute("SELECT id,username,full_name,role,active,must_change_pw,locked_until,last_login FROM users ORDER BY username").fetchall()
    return render_template("users.html", users=rows, now=time.time(), min_len=MIN_PASSWORD_LENGTH)

@app.route("/users/<int:uid>/update", methods=["POST"])
@require("admin")
def update_user(uid):
    action = request.form.get("action", "")
    with db() as c:
        target = c.execute("SELECT * FROM users WHERE id=?", (uid,)).fetchone()
        if not target:
            abort(404)
        active_admins = c.execute("SELECT COUNT(*) FROM users WHERE role='admin' AND active=1").fetchone()[0]
        is_last_admin = target["role"] == "admin" and target["active"] and active_admins <= 1
        if action == "toggle_active":
            if uid == g.user["id"] or is_last_admin:
                flash("لا يمكن تعطيل حسابك الحالي أو آخر مدير نشط.")
            else:
                c.execute("UPDATE users SET active=? WHERE id=?", (0 if target["active"] else 1, uid))
                revoke_sessions(c, uid)
                audit("user.deactivate" if target["active"] else "user.activate", "user", uid, con=c)
                flash("تم تحديث حالة المستخدم.")
        elif action == "set_role":
            role = request.form.get("role", "")
            if role not in ROLES:
                flash("دور غير صالح.")
            elif uid == g.user["id"] or (is_last_admin and role != "admin"):
                flash("لا يمكن تغيير دور حسابك الحالي أو آخر مدير نشط.")
            else:
                c.execute("UPDATE users SET role=? WHERE id=?", (role, uid))
                revoke_sessions(c, uid)
                audit("user.role_change", "user", uid, f"{target['role']}->{role}", con=c)
                flash("تم تغيير الدور.")
        elif action == "reset_password":
            password = request.form.get("password", "")
            problem = password_problem(password, target["username"])
            if problem:
                flash(problem)
            else:
                c.execute("UPDATE users SET password_hash=?, must_change_pw=1, failed_count=0, locked_until=NULL WHERE id=?",
                          (generate_password_hash(password), uid))
                revoke_sessions(c, uid)
                audit("user.password_reset", "user", uid, con=c)
                flash("تم تعيين كلمة مرور مؤقتة؛ سيُطلب تغييرها عند الدخول.")
        elif action == "unlock":
            c.execute("UPDATE users SET failed_count=0, locked_until=NULL WHERE id=?", (uid,))
            audit("user.unlock", "user", uid, con=c)
            flash("تم فك قفل الحساب.")
        else:
            abort(400)
    return redirect(url_for("users"))

def _reauth_ok():
    """Sensitive admin actions require the current password again."""
    with db() as c:
        row = c.execute("SELECT password_hash FROM users WHERE id=?", (g.user["id"],)).fetchone()
    return bool(row) and check_password_hash(row["password_hash"], request.form.get("confirm_password", ""))

# ---------------------------------------------------------------- clinic routes
@app.route("/")
def home():
    patients = appts = income = expense = 0
    upcoming = []
    with db() as c:
        if can("patients.view"):
            patients = c.execute("SELECT COUNT(*) n FROM patients").fetchone()["n"]
        if can("appointments.view"):
            appts = c.execute("SELECT COUNT(*) n FROM appointments WHERE appt_date=?", (datetime.now().strftime("%Y-%m-%d"),)).fetchone()["n"]
            upcoming = c.execute("SELECT * FROM appointments ORDER BY appt_date, appt_time LIMIT 6").fetchall()
        if can("accounts.view"):
            income = c.execute("SELECT COALESCE(SUM(amount),0) n FROM accounts WHERE kind='إيراد'").fetchone()["n"]
            expense = c.execute("SELECT COALESCE(SUM(amount),0) n FROM accounts WHERE kind='مصروف'").fetchone()["n"]
    return render_template("home.html", patients=patients, appts=appts, income=income, expense=expense, upcoming=upcoming)

@app.route("/patients", methods=["GET","POST"])
@require("patients.view")
def patients():
    with db() as c:
        if request.method == "POST":
            if not can("patients.edit"):
                abort(403)
            name=request.form.get("name","").strip()
            if not name:
                flash("اكتب اسم المريض أولاً")
            else:
                cur = c.execute("INSERT INTO patients(name,phone,age,notes) VALUES(?,?,?,?)",
                          (name,request.form.get("phone",""),request.form.get("age",""),request.form.get("notes","")))
                audit("patient.create", "patient", cur.lastrowid, con=c)
                flash("تم حفظ المريض بنجاح")
            return redirect(url_for("patients"))
        q=request.args.get("q","").strip()
        rows=c.execute("SELECT * FROM patients WHERE name LIKE ? OR phone LIKE ? ORDER BY id DESC",
                       (f"%{q}%",f"%{q}%")).fetchall()
        audit("patient.list", "patient", None, "search" if q else None, con=c)
    return render_template("patients.html", patients=rows, q=q)

@app.route("/patients/<int:pid>", methods=["GET", "POST"])
@require("patients.view")
def patient_detail(pid):
    with db() as c:
        patient = c.execute("SELECT * FROM patients WHERE id=?", (pid,)).fetchone()
        if not patient:
            flash("المريض غير موجود")
            return redirect(url_for("patients"))
        if request.method == "POST":
            if not can("payments.record"):
                abort(403)
            try: amount = float(request.form.get("amount", "0"))
            except ValueError: amount = 0
            if amount <= 0:
                flash("أدخل مبلغاً صحيحاً")
            else:
                cur = c.execute("INSERT INTO accounts(entry_date,kind,amount,description,patient_id) VALUES(?,?,?,?,?)",
                          (request.form.get("entry_date") or datetime.now().strftime("%Y-%m-%d"), "إيراد", amount,
                           request.form.get("description", "دفعة من المريض").strip() or "دفعة من المريض", pid))
                audit("payment.create", "account", cur.lastrowid, f"patient={pid}", con=c)
                flash("تم تسجيل دفعة المريض وربطها بالحسابات")
            return redirect(url_for("patient_detail", pid=pid))
        payments = c.execute("SELECT * FROM accounts WHERE patient_id=? ORDER BY entry_date DESC, id DESC", (pid,)).fetchall()
        totals = c.execute("SELECT COALESCE(SUM(CASE WHEN kind='إيراد' THEN amount ELSE 0 END),0) paid, COALESCE(SUM(CASE WHEN kind='مصروف' THEN amount ELSE 0 END),0) refunds FROM accounts WHERE patient_id=?", (pid,)).fetchone()
        appts = c.execute("SELECT * FROM appointments WHERE patient_id=? OR patient_name=? ORDER BY appt_date DESC, appt_time DESC", (pid, patient["name"])).fetchall()
        audit("patient.view", "patient", pid, con=c)
    return render_template("patient_detail.html", patient=patient, payments=payments, totals=totals, appointments=appts, now=datetime.now().strftime("%Y-%m-%d"))

@app.route("/patients/<int:pid>/edit", methods=["GET", "POST"])
@require("patients.edit")
def edit_patient(pid):
    with db() as c:
        patient = c.execute("SELECT * FROM patients WHERE id=?", (pid,)).fetchone()
        if not patient:
            flash("المريض غير موجود")
            return redirect(url_for("patients"))
        if request.method == "POST":
            name = request.form.get("name", "").strip()
            if not name:
                flash("اسم المريض مطلوب")
                return render_template("edit_patient.html", patient=patient)
            # Roles without access to clinical notes never see them, so keep the stored value unchanged.
            notes = request.form.get("notes", "").strip() if can("patients.notes") else patient["notes"]
            c.execute("UPDATE patients SET name=?, phone=?, age=?, notes=? WHERE id=?",
                      (name, request.form.get("phone", "").strip(),
                       request.form.get("age", "").strip(), notes, pid))
            # Keep any existing appointment names in sync when the patient name changes.
            c.execute("UPDATE appointments SET patient_name=? WHERE patient_id=?", (name, pid))
            audit("patient.update", "patient", pid, con=c)
            flash("تم تحديث بيانات المريض بنجاح")
            return redirect(url_for("patients"))
    return render_template("edit_patient.html", patient=patient)

@app.route("/patients/<int:pid>/delete", methods=["POST"])
@require("patients.delete")
def delete_patient(pid):
    with db() as c:
        c.execute("DELETE FROM patients WHERE id=?", (pid,))
        c.execute("DELETE FROM teeth WHERE patient_id=?", (pid,))
        audit("patient.delete", "patient", pid, con=c)
        flash("تم حذف سجل المريض")
    return redirect(url_for("patients"))

@app.route("/appointments", methods=["GET","POST"])
@require("appointments.view")
def appointments():
    with db() as c:
        if request.method == "POST":
            if not can("appointments.edit"):
                abort(403)
            name=request.form.get("patient_name","").strip()
            date=request.form.get("appt_date","")
            status=request.form.get("status","محجوز")
            if status not in APPT_STATUSES:
                status = "محجوز"
            if name and date:
                linked = c.execute("SELECT id FROM patients WHERE name=? ORDER BY id DESC LIMIT 1", (name,)).fetchone()
                cur = c.execute("INSERT INTO appointments(patient_id,patient_name,appt_date,appt_time,reason,status) VALUES(?,?,?,?,?,?)",
                          (linked["id"] if linked else None, name, date, request.form.get("appt_time",""),
                           request.form.get("reason",""), status))
                audit("appointment.create", "appointment", cur.lastrowid, con=c)
                flash("تم حفظ الموعد")
            else: flash("اسم المريض والتاريخ مطلوبان")
            return redirect(url_for("appointments"))
        rows=c.execute("SELECT * FROM appointments ORDER BY appt_date DESC, appt_time DESC").fetchall()
        plist=c.execute("SELECT name FROM patients ORDER BY name").fetchall()
    return render_template("appointments.html", appointments=rows, patients=plist)

@app.route("/appointments/<int:aid>/edit", methods=["GET", "POST"])
@require("appointments.edit")
def edit_appointment(aid):
    with db() as c:
        appointment = c.execute("SELECT * FROM appointments WHERE id=?", (aid,)).fetchone()
        if not appointment:
            flash("الموعد غير موجود")
            return redirect(url_for("appointments"))
        if request.method == "POST":
            name = request.form.get("patient_name", "").strip()
            date = request.form.get("appt_date", "").strip()
            if not name or not date:
                flash("اسم المريض والتاريخ مطلوبان")
                patients_list = c.execute("SELECT name FROM patients ORDER BY name").fetchall()
                return render_template("edit_appointment.html", appointment=appointment, patients=patients_list)
            status = request.form.get("status", "محجوز")
            if status not in APPT_STATUSES:
                status = "محجوز"
            linked = c.execute("SELECT id FROM patients WHERE name=? ORDER BY id DESC LIMIT 1", (name,)).fetchone()
            c.execute("""UPDATE appointments SET patient_id=?, patient_name=?, appt_date=?, appt_time=?, reason=?, status=?
                         WHERE id=?""",
                      (linked["id"] if linked else None, name, date, request.form.get("appt_time", ""),
                       request.form.get("reason", ""), status, aid))
            audit("appointment.update", "appointment", aid, con=c)
            flash("تم تعديل الموعد بنجاح")
            return redirect(url_for("appointments"))
        patients_list = c.execute("SELECT name FROM patients ORDER BY name").fetchall()
    return render_template("edit_appointment.html", appointment=appointment, patients=patients_list)

@app.route("/appointments/<int:aid>/delete", methods=["POST"])
@require("appointments.delete")
def delete_appointment(aid):
    with db() as c:
        c.execute("DELETE FROM appointments WHERE id=?", (aid,))
        audit("appointment.delete", "appointment", aid, con=c)
    flash("تم حذف الموعد")
    return redirect(url_for("appointments"))

@app.route("/appointments/<int:aid>/status", methods=["POST"])
@require("appointments.edit")
def appointment_status(aid):
    status = request.form.get("status", "محجوز")
    if status not in APPT_STATUSES:
        abort(400)
    with db() as c:
        c.execute("UPDATE appointments SET status=? WHERE id=?", (status, aid))
        audit("appointment.status", "appointment", aid, con=c)
    return redirect(url_for("appointments"))

@app.route("/accounts", methods=["GET","POST"])
@require("accounts.view")
def accounts():
    with db() as c:
        if request.method == "POST":
            if not can("accounts.edit"):
                abort(403)
            try: amount=float(request.form.get("amount","0"))
            except ValueError: amount=0
            kind = request.form.get("kind", "إيراد")
            patient_id = request.form.get("patient_id") or None
            if patient_id is not None:
                try: patient_id = int(patient_id)
                except ValueError: patient_id = -1
                if not c.execute("SELECT 1 FROM patients WHERE id=?", (patient_id,)).fetchone():
                    flash("المريض المختار غير موجود")
                    return redirect(url_for("accounts"))
            if kind not in ACCOUNT_KINDS:
                flash("نوع الحركة غير صالح")
            elif amount > 0:
                description = request.form.get("description", "").strip()
                if patient_id and not description:
                    description = "دفعة من المريض" if kind == "إيراد" else "مصروف مرتبط بالمريض"
                cur = c.execute("INSERT INTO accounts(entry_date,kind,amount,description,patient_id) VALUES(?,?,?,?,?)",
                          (request.form.get("entry_date") or datetime.now().strftime("%Y-%m-%d"),
                           kind, amount, description, patient_id))
                audit("account.create", "account", cur.lastrowid, con=c)
                flash("تم تسجيل الحركة المالية")
            else: flash("أدخل مبلغاً صحيحاً")
            return redirect(url_for("accounts"))
        rows=c.execute("SELECT accounts.*, patients.name AS linked_patient FROM accounts LEFT JOIN patients ON patients.id=accounts.patient_id ORDER BY entry_date DESC, accounts.id DESC").fetchall()
        patient_list = c.execute("SELECT id,name FROM patients ORDER BY name").fetchall()
        income=c.execute("SELECT COALESCE(SUM(amount),0) n FROM accounts WHERE kind='إيراد'").fetchone()["n"]
        expense=c.execute("SELECT COALESCE(SUM(amount),0) n FROM accounts WHERE kind='مصروف'").fetchone()["n"]
    return render_template("accounts.html", entries=rows, income=income, expense=expense, patients=patient_list)

@app.route("/odontogram", methods=["GET"])
@require("odontogram")
def odontogram_hub():
    """Dedicated odontogram entry point: choose a patient or jump to a chart."""
    with db() as c:
        patients = c.execute("SELECT id, name, phone FROM patients ORDER BY name COLLATE NOCASE").fetchall()
    return render_template("odontogram_home.html", patients=patients)

@app.route("/odontogram/<int:pid>", methods=["GET","POST"])
@require("odontogram")
def odontogram(pid):
    with db() as c:
        patient=c.execute("SELECT * FROM patients WHERE id=?", (pid,)).fetchone()
        if not patient:
            flash("المريض غير موجود")
            return redirect(url_for("patients"))
        if request.method=="POST":
            for tooth in TEETH:
                condition=request.form.get("tooth_"+tooth, "سليم")
                if condition not in CONDITIONS:
                    condition = "سليم"
                c.execute("INSERT INTO teeth(patient_id,tooth,condition) VALUES(?,?,?) ON CONFLICT(patient_id,tooth) DO UPDATE SET condition=excluded.condition",
                          (pid,tooth,condition))
            audit("odontogram.update", "patient", pid, con=c)
            flash("تم حفظ مخطط الأسنان بنجاح")
            return redirect(url_for("odontogram", pid=pid))
        rows=c.execute("SELECT tooth,condition FROM teeth WHERE patient_id=?", (pid,)).fetchall()
        states={r["tooth"]:r["condition"] for r in rows}
        audit("odontogram.view", "patient", pid, con=c)
    return render_template("odontogram.html", patient=patient, teeth=TEETH, states=states, conditions=CONDITIONS)

@app.route("/backup", methods=["GET", "POST"])
@require("admin")
def backup():
    if request.method == "GET":
        # Downloads now require a POST with password confirmation from the settings page.
        return redirect(url_for("settings"))
    if not _reauth_ok():
        audit("backup.reauth_failed", "database")
        flash("كلمة المرور غير صحيحة؛ لم يتم تنزيل النسخة الاحتياطية.")
        return redirect(url_for("settings"))
    if os.path.exists(DB):
        # Consistent snapshot via SQLite's online backup API (safe while the app is in use).
        fd, snap_path = tempfile.mkstemp(prefix="qd_backup_", suffix=".db", dir=DATA_DIR)
        os.close(fd)
        try:
            src, dst = sqlite3.connect(DB), sqlite3.connect(snap_path)
            with dst:
                src.backup(dst)
            src.close(); dst.close()
            with open(snap_path, "rb") as f:
                data = f.read()
        finally:
            try: os.remove(snap_path)
            except OSError: pass
        audit("backup.download", "database")
        return send_file(BytesIO(data), as_attachment=True, download_name="Quality_Dental_Backup.db", mimetype="application/octet-stream")
    flash("لا توجد قاعدة بيانات للنسخ الاحتياطي")
    return redirect(url_for("home"))

@app.route("/settings", methods=["GET", "POST"])
@require("admin")
def settings():
    if request.method == "POST":
        if not _reauth_ok():
            audit("restore.reauth_failed", "database")
            flash("كلمة المرور غير صحيحة؛ لم يتم تغيير بياناتك.")
            return redirect(url_for("settings"))
        uploaded = request.files.get("backup_file")
        if not uploaded or not uploaded.filename:
            flash("اختَر ملف النسخة الاحتياطية أولاً")
            return redirect(url_for("settings"))
        # Accept only SQLite database backups and validate before touching the live database.
        fd, temp_path = tempfile.mkstemp(prefix="qd_restore_", suffix=".db", dir=DATA_DIR)
        os.close(fd)
        try:
            uploaded.save(temp_path)
            test = sqlite3.connect(temp_path)
            test.execute("PRAGMA trusted_schema=OFF")
            integrity = test.execute("PRAGMA integrity_check").fetchone()[0]
            tables = {r[0] for r in test.execute("SELECT name FROM sqlite_master WHERE type='table'").fetchall()}
            # Triggers/views in an uploaded file could silently run SQL later; never accept them.
            active_objects = test.execute("SELECT COUNT(*) FROM sqlite_master WHERE type IN ('trigger','view')").fetchone()[0]
            test.close()
            if integrity != "ok" or not {"patients", "appointments", "accounts"}.issubset(tables) or active_objects:
                audit("restore.rejected", "database")
                flash("الملف غير صالح أو ليس نسخة احتياطية متوافقة مع Quality Dental. لم يتم تغيير بياناتك.")
                return redirect(url_for("settings"))
            # Keep an automatic safety copy of the current database before restore.
            if os.path.exists(DB):
                stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                shutil.copy2(DB, os.path.join(DATA_DIR, f"quality_dental_before_restore_{stamp}.db"))
            # Upgrade older backup schema before switching it into service.
            con = sqlite3.connect(temp_path)
            con.execute("CREATE TABLE IF NOT EXISTS teeth (id INTEGER PRIMARY KEY AUTOINCREMENT, patient_id INTEGER NOT NULL, tooth TEXT NOT NULL, condition TEXT NOT NULL DEFAULT 'سليم', UNIQUE(patient_id,tooth))")
            acols = [r[1] for r in con.execute("PRAGMA table_info(accounts)").fetchall()]
            if "patient_id" not in acols:
                con.execute("ALTER TABLE accounts ADD COLUMN patient_id INTEGER REFERENCES patients(id)")
            # Never trust accounts or audit history from an uploaded file: replace them with the current ones,
            # so a restore cannot plant an attacker account or erase the audit trail.
            for t in AUTH_TABLES:
                con.execute(f"DROP TABLE IF EXISTS {t}")
            con.executescript(AUTH_SCHEMA)
            con.execute("ATTACH DATABASE ? AS cur", (DB,))
            for t in AUTH_TABLES:
                con.execute(f"INSERT INTO main.{t} SELECT * FROM cur.{t}")
            con.commit()
            con.execute("DETACH DATABASE cur")
            con.close()
            os.replace(temp_path, DB)
            audit("restore.completed", "database")
            flash("تمت استعادة النسخة الاحتياطية بنجاح. احتفظنا تلقائياً بنسخة من قاعدة البيانات السابقة داخل مجلد البيانات.")
            return redirect(url_for("home"))
        except Exception:
            app.logger.exception("Backup restore failed")
            flash("تعذرت استعادة النسخة الاحتياطية؛ لم نكمل العملية. تأكد أن الملف هو قاعدة بيانات البرنامج.")
            return redirect(url_for("settings"))
        finally:
            if os.path.exists(temp_path):
                try: os.remove(temp_path)
                except OSError: pass
    return render_template("settings.html")

@app.route("/assistant")
@require("assistant")
def assistant():
    return render_template("assistant.html")

def serve():
    """Production server (waitress) when available; falls back to the Flask dev server."""
    host = os.environ.get("QD_HOST", "0.0.0.0")
    port = int(os.environ.get("QD_PORT", "8000"))
    try:
        from waitress import serve as waitress_serve
        waitress_serve(app, host=host, port=port, threads=8)
    except ImportError:
        app.run(host=host, port=port, debug=False, threaded=True)

if __name__ == "__main__":
    serve()
