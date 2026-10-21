#!/usr/bin/env python3
"""
texpad -- a tiny local Overleaf.

  python3 texpad.py [project-dir] [--port 8765] [--no-open]   (macOS / Linux)
  python  texpad.py [project-dir] [--port 8765] [--no-open]   (Windows)

or just double-click run.sh / run.bat in this folder.

Left pane: your .tex files with a section outline. Select text and click one
of the four dots (or Alt+1..4) to mark it white/yellow/red/green -- a purely
local editing aid (progress colour-coding) that is never written into the
.tex source. Right pane: the compiled PDF, refreshed every time you save.
Nothing to install beyond a TeX distribution -- this file uses only the
Python standard library.

Binds to 127.0.0.1 only. Nothing is exposed to your network.
"""

import argparse
import base64
import bisect
import collections
import difflib
import hashlib
import html
import http.server
import json
import mimetypes
import os
import re
import shutil
import socketserver
import subprocess
import sys
import threading
import time
import unicodedata
import urllib.parse
import webbrowser
from pathlib import Path

EDITABLE = {".tex", ".bib", ".cls", ".sty", ".latexmkrc", ".md", ".txt"}
BUILD_DIR = "build"

ROOT: Path
MAIN = "main.tex"
STATE = {"log": "", "ok": None, "at": 0, "pages": 0, "busy": False}
LOCK = threading.Lock()


# --------------------------------------------------------------------------
#  TeX discovery and compilation
# --------------------------------------------------------------------------
def tex_env():
    """GUI-launched processes don't always inherit the shell's PATH -- most
    notably macOS, where /Library/TeX/texbin isn't on it unless a login shell
    put it there. Append every place a TeX distribution plausibly installed
    itself, per platform; harmless if a given path doesn't exist."""
    env = os.environ.copy()
    if sys.platform == "darwin":
        extra = ["/Library/TeX/texbin", "/usr/local/texlive/bin", "/opt/homebrew/bin",
                 "/usr/local/bin", "/usr/bin"]
    elif sys.platform.startswith("win"):
        local, prog, prog86 = (os.environ.get("LOCALAPPDATA", ""),
                                os.environ.get("PROGRAMFILES", ""),
                                os.environ.get("PROGRAMFILES(X86)", ""))
        extra = [os.path.join(local, "Programs", "MiKTeX", "miktex", "bin", "x64"),
                 os.path.join(prog, "MiKTeX", "miktex", "bin", "x64"),
                 os.path.join(prog86, "MiKTeX", "miktex", "bin"),
                 r"C:\texlive\2026\bin\windows", r"C:\texlive\2025\bin\windows"]
    else:
        extra = ["/usr/local/texlive/bin", "/usr/local/bin", "/usr/bin"]
    env["PATH"] = os.pathsep.join([env.get("PATH", "")] + extra)
    return env


def which(prog):
    return shutil.which(prog, path=tex_env()["PATH"])


# Heavy helpers (latexmk/biber, pdftoppm, synctex) run below normal CPU
# priority. Auto-compile fires on every pause in typing, and a full build plus
# re-rendering every page easily saturates a laptop's cores for several
# seconds -- at normal priority that competes with the browser and makes
# typing stall. Low priority means the OS always serves the editor first.
_NICE = shutil.which("nice") if os.name != "nt" else None
LOW_PRIO_KW = ({"creationflags": getattr(subprocess, "BELOW_NORMAL_PRIORITY_CLASS", 0)}
               if os.name == "nt" else {})


def low_prio(cmd):
    return ([_NICE, "-n", "10"] + cmd) if _NICE else cmd


# Page images are rendered on demand, one request per page; the browser fires
# them all at once after each compile. Cap concurrent pdftoppm runs so that
# burst can't pin every core at the same moment.
RENDER_SEM = threading.BoundedSemaphore(2)


def toolchain():
    return {
        "latexmk": which("latexmk"),
        "synctex": which("synctex"),
        "pdflatex": which("pdflatex"),
        "biber": which("biber"),
        "pdftoppm": which("pdftoppm"),
    }


def compile_project():
    """Run latexmk (or a manual pdflatex/biber sequence) and capture the log."""
    tc = toolchain()
    outdir = ROOT / BUILD_DIR
    outdir.mkdir(exist_ok=True)
    env = tex_env()

    if tc["latexmk"]:
        cmds = [[tc["latexmk"], "-pdf", "-synctex=1", "-interaction=nonstopmode",
                 "-file-line-error", f"-outdir={BUILD_DIR}", MAIN]]
    elif tc["pdflatex"]:
        base = [tc["pdflatex"], "-synctex=1", "-interaction=nonstopmode",
                "-file-line-error", f"-output-directory={BUILD_DIR}", MAIN]
        cmds = [base]
        if tc["biber"]:
            cmds.append([tc["biber"], f"--input-directory={BUILD_DIR}",
                         f"--output-directory={BUILD_DIR}", Path(MAIN).stem])
        cmds += [base, base]
    else:
        return False, ("No TeX distribution found.\n\n"
                       "Install one, then reload this page:\n\n"
                       "    brew install --cask basictex\n\n"
                       "then open a new terminal and run:\n\n"
                       "    sudo tlmgr update --self\n"
                       "    sudo tlmgr install latexmk biblatex biblatex-apa biber \\\n"
                       "         helvet mathptmx microtype titlesec enumitem fancyhdr \\\n"
                       "         lastpage siunitx booktabs caption subcaption stfloats \\\n"
                       "         flushend cleveref todonotes lipsum orcidlink multirow\n\n"
                       "MacTeX (~4 GB, everything preinstalled) also works:\n"
                       "    brew install --cask mactex-no-gui\n")

    out = []
    for cmd in cmds:
        try:
            p = subprocess.run(low_prio(cmd), cwd=str(ROOT), env=env, timeout=180,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               **LOW_PRIO_KW)
            out.append(p.stdout.decode("utf-8", "replace"))
        except subprocess.TimeoutExpired:
            return False, "".join(out) + "\n*** Timed out after 180 s."
        except Exception as exc:                                # noqa: BLE001
            return False, "".join(out) + f"\n*** Could not run {cmd[0]}: {exc}"

    log = "".join(out)
    pdf = outdir / (Path(MAIN).stem + ".pdf")
    return pdf.exists(), log


def problems(log):
    """Split a 3000-line TeX log into the handful of lines a human needs.

    Errors first, then warnings. nonstopmode still emits a PDF when the source
    has errors, so error COUNT -- not PDF existence -- is what decides whether
    a build is good.
    """
    errs, warns, seen = [], [], set()
    for line in log.splitlines():
        line = line.rstrip()
        if not line or line in seen:
            continue
        # "./sections/03_methods.tex:44: Undefined control sequence."  or  "! ..."
        if line.startswith("!") or re.match(r"^\.?/?\S+\.\w+:\d+: ", line) \
                or re.match(r"^(LaTeX|Package \w+) Error", line):
            seen.add(line)
            errs.append({"sev": "error", "text": line})
        elif re.match(r"^(Overfull|Underfull)", line):
            seen.add(line)
            warns.append({"sev": "box", "text": line})
        elif re.match(r"^(LaTeX Warning|Package \w+ Warning|LaTeX Font Warning)", line):
            seen.add(line)
            warns.append({"sev": "warn", "text": line})
    return errs[:40] + warns[:40]


def page_count(pdf: Path):
    """Page count without any third-party library.

    Modern pdfTeX puts the page tree inside compressed object streams, so a
    plain regex over the file finds nothing. Try pdfinfo, then inflate every
    Flate stream and count there, then fall back to the raw bytes.
    """
    try:
        info = which("pdfinfo")
        if info:
            out = subprocess.run([info, str(pdf)], capture_output=True, timeout=20,
                                 env=tex_env()).stdout.decode("utf-8", "replace")
            m = re.search(r"^Pages:\s+(\d+)", out, re.M)
            if m:
                return int(m.group(1))
    except Exception:                                           # noqa: BLE001
        pass

    try:
        import zlib
        data = pdf.read_bytes()
        blob = bytearray(data)
        for m in re.finditer(rb"stream\r?\n", data):
            end = data.find(b"endstream", m.end())
            if end < 0:
                continue
            try:
                blob += zlib.decompress(data[m.end():end])
            except Exception:                                   # noqa: BLE001
                continue
        n = len(re.findall(rb"/Type\s*/Page(?![s/\w])", bytes(blob)))
        if n:
            return n
        m = re.findall(rb"/Count\s+(\d+)", bytes(blob))
        if m:
            return max(int(x) for x in m)
    except Exception:                                           # noqa: BLE001
        pass
    return 1


# --------------------------------------------------------------------------
#  SyncTeX -- source <-> PDF position mapping
# --------------------------------------------------------------------------
def _synctex(args):
    exe = which("synctex")
    if not exe:
        return ""
    try:
        r = subprocess.run(low_prio([exe] + args), cwd=str(ROOT), env=tex_env(),
                           capture_output=True, timeout=20, **LOW_PRIO_KW)
        return r.stdout.decode("utf-8", "replace")
    except Exception:                                           # noqa: BLE001
        return ""


def sync_forward(relpath, line):
    """source line -> {page, x, y, w, h} in PDF points, origin top-left."""
    pdf = f"{BUILD_DIR}/{Path(MAIN).stem}.pdf"
    out = _synctex(["view", "-i", f"{int(line)}:1:{relpath}", "-o", pdf, "-d", "."])
    for block in out.split("Output:")[1:]:
        g = dict(re.findall(r"^(Page|h|v|W|H):([-\d.]+)", block, re.M))
        if len(g) == 5 and float(g["W"]) > 0:
            # v is the baseline measured from the top of the page
            return {"page": int(float(g["Page"])),
                    "x": float(g["h"]), "y": float(g["v"]) - float(g["H"]),
                    "w": float(g["W"]), "h": float(g["H"])}
    return None


def sync_reverse(page, x, y):
    """PDF point -> {path, line}. Accurate on glyphs, approximate in whitespace."""
    pdf = f"{BUILD_DIR}/{Path(MAIN).stem}.pdf"
    out = _synctex(["edit", "-o", f"{int(page)}:{x:.2f}:{y:.2f}:{pdf}", "-d", "."])
    m = re.search(r"^Input:(.+)$", out, re.M)
    n = re.search(r"^Line:(\d+)$", out, re.M)
    if not (m and n):
        return None
    try:
        rel = Path(os.path.normpath(m.group(1).strip())).resolve().relative_to(ROOT.resolve())
    except Exception:                                           # noqa: BLE001
        return None
    return {"path": str(rel), "line": int(n.group(1))}


# --------------------------------------------------------------------------
#  Project files
# --------------------------------------------------------------------------
def safe(rel: str) -> Path:
    p = (ROOT / rel).resolve()
    if ROOT.resolve() not in p.parents and p != ROOT.resolve():
        raise ValueError("outside project")
    if p.suffix.lower() not in EDITABLE and p.name not in EDITABLE:
        raise ValueError("not an editable file")
    return p


def file_list():
    out = []
    for p in sorted(ROOT.rglob("*")):
        if BUILD_DIR in p.parts or p.name.startswith("."):
            continue
        if p.is_file() and p.suffix.lower() in EDITABLE:
            out.append(str(p.relative_to(ROOT)))
    out.sort(key=lambda s: (s != MAIN, s.count("/"), s))
    return out


def outline(text):
    items = []
    for i, line in enumerate(text.splitlines(), 1):
        m = re.match(r"\s*\\(sub)*section\*?\{(.+?)\}", line)
        if m:
            depth = (m.group(0).count("sub"))
            items.append({"line": i, "title": m.group(2), "depth": depth})
    return items


# --------------------------------------------------------------------------
#  Highlight marks -- a purely local editing aid (which paragraphs still need
#  work), never written into the .tex source. Stored as {start,end,color}
#  character offsets per file in one sidecar JSON next to the project, keyed
#  by the same relative path the editor already uses.
# --------------------------------------------------------------------------
MARKS_FILE = ".texpad-marks.json"
MARKS_LOCK = threading.Lock()


def _load_marks():
    p = ROOT / MARKS_FILE
    if not p.exists():
        return {}
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except Exception:                                           # noqa: BLE001
        return {}


def marks_for(rel):
    with MARKS_LOCK:
        return _load_marks().get(rel, [])


def set_marks_for(rel, marks):
    with MARKS_LOCK:
        data = _load_marks()
        if marks:
            data[rel] = marks
        else:
            data.pop(rel, None)
        (ROOT / MARKS_FILE).write_text(json.dumps(data), encoding="utf-8")


# --------------------------------------------------------------------------
#  Git -- explicit, visible Push/Pull so marks (now tracked -- see above) and
#  file edits can travel to/from other devices (e.g. a phone running texpad
#  mobile) through the same repo. Nothing here runs automatically or
#  silently: both buttons are deliberate actions, same as typing `git push`
#  yourself. Auto-pulling on every file open was deliberately NOT done --
#  it would routinely no-op anyway once you have local uncommitted edits
#  (the normal state while writing), and a background op that sometimes
#  works and sometimes silently doesn't is worse than an explicit button.
# --------------------------------------------------------------------------
def is_git_repo():
    try:
        r = subprocess.run(["git", "rev-parse", "--is-inside-work-tree"],
                            cwd=str(ROOT), capture_output=True, timeout=10, text=True)
        return r.returncode == 0 and r.stdout.strip() == "true"
    except Exception:                                           # noqa: BLE001
        return False


def git_run(args, timeout=30):
    try:
        r = subprocess.run(["git"] + args, cwd=str(ROOT), capture_output=True,
                            timeout=timeout, text=True)
        return r.returncode == 0, (r.stdout + r.stderr).strip()
    except Exception as exc:                                    # noqa: BLE001
        return False, str(exc)


def git_pull():
    if not is_git_repo():
        return False, "This folder isn't a git repository."
    ok, out = git_run(["pull", "--no-edit"])
    if not ok and "conflict" in out.lower():
        out += ("\n\nThat's a real conflict (both sides edited the same lines) -- "
                "open a terminal here and resolve it by hand, same as any git conflict.")
    return ok, out


def git_push_all(message):
    if not is_git_repo():
        return False, "This folder isn't a git repository."
    ok, out = git_run(["add", "-A"])
    if not ok:
        return False, out
    ok, status = git_run(["status", "--porcelain"])
    if ok and status:
        ok, out = git_run(["commit", "-m", message])
        if not ok and "nothing to commit" not in out.lower():
            return False, out
    ok, out = git_run(["push"])
    if ok:
        return True, out or "Pushed."
    # Someone else (e.g. the phone) pushed since we last synced -- merge their
    # commits in and retry once, same as running `git pull && git push`
    # yourself. Only a real conflict (same lines touched on both sides) fails
    # this outright; that needs a terminal either way.
    if "rejected" in out.lower() or "fetch first" in out.lower() or "non-fast-forward" in out.lower():
        pull_ok, pull_out = git_pull()
        if not pull_ok:
            return False, "Push rejected (remote had newer commits); auto-merge failed:\n" + pull_out
        ok, out2 = git_run(["push"])
        if ok:
            return True, "Merged in remote changes, then pushed.\n" + out2
        return False, "Merged in remote changes, but push still failed:\n" + out2
    return False, out


# --------------------------------------------------------------------------
#  Comments (annotations) -- notes to the author, and the author's own, anchored to a span of text like
#  a comment on a Google Doc. They live next to the marks in .texpad-annotations.json (same lifecycle:
#  keyed by the same relative path, meant to be git-ignored like the marks) and are never written into
#  the .tex source. One comment:
#    {id, start, end, quote, prefix, suffix, kind: decide|info|source|check, status: open|resolved,
#     author, created, text, replies: [{author, text, created}]}
#  start/end are character offsets like the marks (UTF-16 units, as the page counts them). Fields that
#  are not listed are ignored by texpad and kept when it saves. The anchor follows edits through the very
#  mapping the marks use (xr_adjust_marks / adjustMarks). When start/end no longer hold `quote`, the anchor
#  is searched again -- prefix+quote+suffix, then each half, then quote alone, the nearest hit wins --
#  and reported 'detached' when nothing is found; a detached comment is never deleted.
# --------------------------------------------------------------------------
ANN_FILE = ".texpad-annotations.json"
ANN_LOCK = threading.Lock()
ANN_KINDS = ("decide", "info", "source", "check", "review")
ANN_CONTEXT = 40


class AnnError(Exception):
    """A comment request that cannot be honoured; the message is shown to the author."""


def _ann_load(strict=False):
    p = ROOT / ANN_FILE
    if not p.exists():
        return {}
    try:
        d = json.loads(p.read_text(encoding="utf-8"))
        if isinstance(d, dict):
            return d
    except Exception:                                           # noqa: BLE001
        pass
    if strict:
        raise AnnError(f"{ANN_FILE} exists but is not a JSON object; texpad will not overwrite it")
    return {}


def _ann_save(data):
    p = ROOT / ANN_FILE
    tmp = p.with_name(p.name + ".tmp")
    tmp.write_text(json.dumps(data, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
    os.replace(tmp, p)


def _ann_list(data, rel):
    lst = data.get(rel)
    return [a for a in lst if isinstance(a, dict)] if isinstance(lst, list) else []


def _ann_ids(lst):
    """Give every comment a unique id (a0001, a0002, ...) in place; existing ids are kept."""
    used = {a["id"] for a in lst if isinstance(a.get("id"), str) and a["id"]}
    n = max((int(m.group(1)) for i in used for m in [re.fullmatch(r"a(\d+)", i)] if m), default=0)
    seen = set()
    for a in lst:
        if not isinstance(a.get("id"), str) or not a["id"] or a["id"] in seen:
            n += 1
            while f"a{n:04d}" in used:
                n += 1
            a["id"] = f"a{n:04d}"
            used.add(a["id"])
        seen.add(a["id"])
    return lst


def _ann_int(v, default=0):
    try:
        return int(v)
    except (TypeError, ValueError):
        return default


def _ann_conv(text):
    """(to_cp, to_u16) for this text: the file stores UTF-16 offsets, Python slices by code point."""
    u = _xr_u16(text)
    if u is None:
        return (lambda x: x), (lambda x: x)
    return (lambda x: bisect.bisect_right(u, x) - 1), (lambda x: u[min(max(x, 0), len(u) - 1)])


def ann_locate(text, start, end, quote, prefix, suffix, strict=False):
    """Where a comment's anchor is in `text` (code points): ('ok', s, e) when start/end still hold the quote,
    ('moved', s, e) when the quote was found elsewhere, ('detached', start, end) when it was not. strict is for a
    comment texpad itself knows lost its text (a merge or the editor removed it): it may come back only where its
    whole context (prefix + quote + suffix) is found again, never by a bare word that happens to occur elsewhere."""
    if not quote:
        return ("ok", start, end) if 0 <= start < end <= len(text) else ("detached", start, end)
    if 0 <= start <= end <= len(text) and text[start:end] == quote:
        return "ok", start, end

    def nearest(needle):
        best, i = None, text.find(needle)
        while i >= 0:
            if best is None or abs(i - start) < abs(best - start):
                best = i
            i = text.find(needle, i + 1)
        return best

    for pre, suf in (((prefix, suffix),) if strict and (prefix or suffix)
                     else () if strict else ((prefix, suffix), (prefix, ""), ("", suffix), ("", ""))):
        i = nearest(pre + quote + suf)
        if i is not None:
            return "moved", i + len(pre), i + len(pre) + len(quote)
    return "detached", start, end


def ann_view(rel, text=None, data=None):
    """The comments of a file as the page shows them: copies with `_anchor` ('ok', 'moved', 'detached'), the
    corrected start/end for moved ones, and `_line` / `_line_end` (1-based) for the ones that are anchored."""
    if text is None:
        text = safe(rel).read_text(encoding="utf-8")
    lst = _ann_ids(_ann_list(data if data is not None else _ann_load(), rel))
    to_cp, to_u = _ann_conv(text)
    out = []
    for a in lst:
        v = json.loads(json.dumps(a))
        s, e = _ann_int(a.get("start")), _ann_int(a.get("end"))
        state, cs, ce = ann_locate(text, to_cp(s), to_cp(e), str(a.get("quote") or ""),
                                   str(a.get("prefix") or ""), str(a.get("suffix") or ""), strict=bool(a.get("detached")))
        v["_anchor"] = state
        if state != "detached":
            v["start"], v["end"] = to_u(cs), to_u(ce)
            v["_line"] = text.count("\n", 0, cs) + 1
            v["_line_end"] = text.count("\n", 0, max(cs, ce - 1)) + 1
        out.append(v)
    return out


def ann_counts(view):
    c = {"open": 0, "resolved": 0, "detached": 0, "kinds": {k: 0 for k in ANN_KINDS}}
    for a in view:
        done = a.get("status") == "resolved"
        c["resolved" if done else "open"] += 1
        c["detached"] += a["_anchor"] == "detached"
        if not done and a.get("kind") in c["kinds"]:
            c["kinds"][a["kind"]] += 1
    return c


def ann_adjust(items, old_t, new_t):
    """Carry anchors through one edit, in place, with exactly the mapping the marks get (xr_adjust_marks).
    items: dicts with code-point start/end. An anchor whose text was replaced entirely collapses; it is
    flagged `collapsed` (and stops moving) rather than dropped, so its comment survives as detached."""
    live = [it for it in items if not it.get("collapsed")]
    moved = {m["color"]: m for m in xr_adjust_marks(
        [{"start": it["start"], "end": it["end"], "color": str(i)} for i, it in enumerate(live)], old_t, new_t)}
    for i, it in enumerate(live):
        m = moved.get(str(i))
        if m:
            it["start"], it["end"] = m["start"], m["end"]
        else:
            it["collapsed"] = True


def ann_refresh(a, text, cs, ce):
    """Store the anchor's offsets (UTF-16) and re-read quote/prefix/suffix from the text it now sits on."""
    _, to_u = _ann_conv(text)
    a["start"], a["end"] = to_u(cs), to_u(ce)
    a["quote"] = text[cs:ce]
    a["prefix"] = text[max(0, cs - ANN_CONTEXT):cs]
    a["suffix"] = text[ce:ce + ANN_CONTEXT]


def ann_carry(lst, base, edits):
    """The comments `lst` (stored for the text `base`) after the hunks `edits` were applied: anchors move with
    the same mapping, in the same order, as the marks. -> (new list, {carried, detached})"""
    out = json.loads(json.dumps(lst))
    to_cp, _ = _ann_conv(base)
    items, lost = [], 0
    for a in out:
        state, cs, ce = ann_locate(base, to_cp(_ann_int(a.get("start"))), to_cp(_ann_int(a.get("end"))),
                                   str(a.get("quote") or ""), str(a.get("prefix") or ""), str(a.get("suffix") or ""))
        if state == "detached":
            lost += 1
        else:
            items.append({"a": a, "start": cs, "end": ce})
    text = base
    for b0, b1, new in sorted(edits, key=lambda e: (e[0], e[1]), reverse=True):
        nt = text[:b0] + new + text[b1:]
        ann_adjust(items, text, nt)
        text = nt
    for it in items:
        if it.get("collapsed"):
            lost += 1                       # its text was removed: marked, so it shows as detached (and is not
            it["a"]["detached"] = True      # re-anchored to the same word somewhere else)
        else:
            it["a"].pop("detached", None)
            ann_refresh(it["a"], text, it["start"], it["end"])
    return out, {"carried": len(items) - sum(1 for it in items if it.get("collapsed")), "detached": lost}


def ann_carry_apply(src_rel, dest_rel, base, edits):
    """Cross-review Apply: carry the open file's comments through the merge, into the same file or into the new copy."""
    try:
        with ANN_LOCK:
            data = _ann_load(strict=True)
            lst = _ann_list(data, src_rel)
            if not lst:
                return {"carried": 0, "detached": 0}
            new, stats = ann_carry(lst, base, edits)
            if dest_rel == src_rel and not edits:
                return stats
            data[dest_rel] = new
            _ann_save(data)
            return stats
    except (AnnError, OSError) as exc:
        return {"carried": 0, "detached": 0, "error": str(exc)}


def _ann_text(rel, body):
    """The text the offsets refer to: the editor's current text when the page sends it as `doc`, else the file."""
    return body["doc"] if isinstance(body.get("doc"), str) else safe(rel).read_text(encoding="utf-8")


def ann_op(body):
    """One change to the comments of a file: add, edit, reply, resolve, reopen, delete, or sync (anchor
    positions after typing). Reads the file's comments fresh, changes only what the op names (unknown fields
    stay), and writes the sidecar atomically. Returns the file's comments as ann_view shows them."""
    rel, op = body.get("file", ""), body.get("op")
    try:
        safe(rel)
    except ValueError as exc:
        raise AnnError(str(exc))
    now = time.strftime("%Y-%m-%dT%H:%M:%S")
    text = _ann_text(rel, body)
    with ANN_LOCK:
        data = _ann_load(strict=True)
        lst = _ann_list(data, rel)
        _ann_ids(lst)
        get = lambda: next((a for a in lst if a["id"] == body.get("id")), None)
        made = None
        if op == "add":
            to_cp, _ = _ann_conv(text)
            cs, ce = to_cp(_ann_int(body.get("start"), -1)), to_cp(_ann_int(body.get("end"), -1))
            kind, msg = body.get("kind", "info"), str(body.get("text") or "").strip()
            if not 0 <= cs < ce <= len(text):
                raise AnnError("select some text to comment on")
            if kind not in ANN_KINDS:
                raise AnnError(f"kind must be one of {', '.join(ANN_KINDS)}")
            if not msg:
                raise AnnError("the comment is empty")
            made = {"id": None, "start": 0, "end": 0, "quote": "", "prefix": "", "suffix": "", "kind": kind,
                    "status": "open", "author": str(body.get("author") or settings_author())[:60], "created": now, "text": msg[:20000],
                    "replies": []}
            ann_refresh(made, text, cs, ce)
            lst.append(made)
            _ann_ids(lst)
        elif op == "sync":
            n = 0
            for r in body.get("anchors") or []:
                a = next((x for x in lst if x["id"] == r.get("id")), None)
                if a is None or not isinstance(r, dict):
                    continue
                s, e = _ann_int(r.get("start"), -1), _ann_int(r.get("end"), -1)
                if 0 <= s <= e:
                    a["start"], a["end"] = s, e
                    a.pop("detached", None)
                    for f in ("quote", "prefix", "suffix"):
                        if isinstance(r.get(f), str):
                            a[f] = r[f]
                    n += 1
            for i in body.get("detached") or []:       # the editor removed the anchored text: remember it
                a = next((x for x in lst if x["id"] == i), None)
                if a is not None:
                    a["detached"] = True
            data[rel] = lst
            _ann_save(data)
            return {"ok": True, "synced": n}
        else:
            a = get()
            if a is None:
                raise AnnError(f"no comment {body.get('id')!r}")
            if op == "edit":
                if "kind" in body:
                    if body["kind"] not in ANN_KINDS:
                        raise AnnError(f"kind must be one of {', '.join(ANN_KINDS)}")
                    a["kind"] = body["kind"]
                if "text" in body:
                    if not str(body["text"]).strip():
                        raise AnnError("the comment is empty")
                    a["text"] = str(body["text"]).strip()[:20000]
            elif op == "reply":
                msg = str(body.get("text") or "").strip()
                if not msg:
                    raise AnnError("the reply is empty")
                if not isinstance(a.get("replies"), list):
                    a["replies"] = []
                a["replies"].append({"author": str(body.get("author") or settings_author())[:60], "text": msg[:20000], "created": now})
            elif op in ("resolve", "reopen"):
                a["status"] = "resolved" if op == "resolve" else "open"
            elif op == "share":                       # show this comment to the reviewer in the next review copy
                if body.get("value"):
                    a["share"] = True
                else:
                    a.pop("share", None)
            elif op == "delete":
                lst.remove(a)
            else:
                raise AnnError(f"unknown op {op!r}")
        data[rel] = lst
        _ann_save(data)
    view = ann_view(rel, text, data)
    return {"annotations": view, "counts": ann_counts(view), "id": made["id"] if made else body.get("id")}


def ann_export(rel, text=None):
    """The open comments of a file as plain Markdown, for reading or printing: kind, line, quote, text, replies."""
    view = ann_view(rel, text)
    opened = [a for a in view if a.get("status") != "resolved"]
    anchored = sorted((a for a in opened if a["_anchor"] != "detached"), key=lambda a: _ann_int(a.get("start")))
    lost = [a for a in opened if a["_anchor"] == "detached"]
    c = ann_counts(view)
    kinds = ", ".join(f"{n} {k}" for k, n in c["kinds"].items() if n)
    out = [f"# Open comments: {rel}", "",
           f"{len(opened)} open" + (f" ({kinds})" if kinds else "") + f", {c['resolved']} resolved (not listed)."
           + (f" {len(lost)} could not be found in the text any more (listed last)." if lost else ""), ""]

    def block(n, a, where):
        quote = re.sub(r"\s+", " ", str(a.get("quote") or "")).strip()
        quote = quote if len(quote) <= 300 else quote[:299] + "…"
        out.extend([f"## {n}. [{a.get('kind', 'info')}] {where} — {a.get('author', '?')}, {str(a.get('created', ''))[:16].replace('T', ' ')}",
                    "", f"> {quote}" if quote else "> (no quoted text)", "", str(a.get("text", "")).strip(), ""])
        for r in a.get("replies") if isinstance(a.get("replies"), list) else []:
            if isinstance(r, dict):
                out.append(f"- **{r.get('author', '?')}**, {str(r.get('created', ''))[:16].replace('T', ' ')}: {str(r.get('text', '')).strip()}")
        if a.get("replies"):
            out.append("")

    for n, a in enumerate(anchored, 1):
        block(n, a, f"line {a['_line']}" + (f"–{a['_line_end']}" if a["_line_end"] > a["_line"] else ""))
    if lost:
        out += ["## Detached (the anchored text was not found)", ""]
        for n, a in enumerate(lost, len(anchored) + 1):
            block(n, a, "line unknown")
    return "\n".join(out).rstrip() + "\n"


# --------------------------------------------------------------------------
#  Review copies -- send the chapter to somebody who reads it in a browser and leaves comments.
#  texpad writes ONE self-contained HTML file (inline CSS and JS, no request of any kind); the reader
#  downloads their comments as a small JSON file; the author imports it and the comments become
#  ordinary comments anchored in the .tex source. For that to work the reading view is rendered from the
#  LaTeX by the converter below, which keeps a map from every rendered character back to its source
#  offsets. Nothing here calls a model, an API or a CLI; it never writes or rewrites thesis text.
# --------------------------------------------------------------------------
RV_FORMAT = "texpad-review-comments"
RV_PDF_MAX = 15 * 1024 * 1024

RV_GREEK = {"alpha": "α", "beta": "β", "gamma": "γ", "delta": "δ", "epsilon": "ε", "varepsilon": "ε", "zeta": "ζ",
            "eta": "η", "theta": "θ", "vartheta": "ϑ", "iota": "ι", "kappa": "κ", "lambda": "λ", "mu": "μ", "nu": "ν",
            "xi": "ξ", "pi": "π", "rho": "ρ", "sigma": "σ", "tau": "τ", "upsilon": "υ", "phi": "φ", "varphi": "φ",
            "chi": "χ", "psi": "ψ", "omega": "ω", "Gamma": "Γ", "Delta": "Δ", "Theta": "Θ", "Lambda": "Λ", "Xi": "Ξ",
            "Pi": "Π", "Sigma": "Σ", "Phi": "Φ", "Psi": "Ψ", "Omega": "Ω"}
RV_SYMBOLS = dict(RV_GREEK, approx="≈", pm="±", mp="∓", times="×", div="÷", leq="≤", le="≤", geq="≥", ge="≥", neq="≠",
                  ne="≠", rightarrow="→", to="→", leftarrow="←", Rightarrow="⇒", leftrightarrow="↔", cdot="·",
                  ldots="…", dots="…", cdots="…", textdegree="°", degree="°", S="§", P="¶", copyright="©", infty="∞",
                  sim="∼", ll="≪", gg="≫", propto="∝", **{"in": "∈"}, cap="∩", cup="∪", sum="∑", partial="∂", nabla="∇",
                  circ="∘", bullet="•", ss="ß", o="ø", O="Ø", ae="æ", AE="Æ", aa="å", AA="Å", l="ł", i="ı",
                  textbackslash="\\", textasciitilde="~", textquotesingle="'", euro="€", pounds="£", checkmark="✓",
                  textbullet="•", textendash="–", textemdash="—", percent="%", ldq="“", rdq="”", textellipsis="…",
                  top="⊤", mid="|", ell="ℓ", hbar="ℏ", dagger="†", ddagger="‡", angle="∠", forall="∀", exists="∃",
                  neg="¬", land="∧", lor="∨", subset="⊂", supset="⊃", equiv="≡", cong="≅", prime="′", ast="∗", star="⋆")
RV_UNITS = {"degree": "°", "hertz": "Hz", "metre": "m", "meter": "m", "second": "s", "percent": "%", "pixel": "px",
            "gram": "g", "watt": "W", "volt": "V", "ampere": "A", "kelvin": "K", "byte": "B", "bit": "bit",
            "degreeCelsius": "°C", "celsius": "°C", "minute": "min", "hour": "h", "day": "d", "litre": "l",
            "milli": "m", "centi": "c", "micro": "µ", "kilo": "k", "mega": "M", "giga": "G", "nano": "n", "deci": "d",
            "per": "/", "squared": "²", "cubed": "³", "radian": "rad", "decibel": "dB", "lux": "lx", "newton": "N",
            "joule": "J", "pascal": "Pa", "arcminute": "′", "arcsecond": "″", "textdegree": "°"}
RV_ACCENTS = {'"': "\u0308", "'": "\u0301", "`": "\u0300", "^": "\u0302", "~": "\u0303", "c": "\u0327", "v": "\u030c",
              "u": "\u0306", "H": "\u030b", "=": "\u0304", ".": "\u0307", "k": "\u0328", "r": "\u030a"}
RV_WRAP = {"emph": "em", "textit": "em", "textsl": "em", "textbf": "strong", "mathbf": "strong", "texttt": "code",
           "textsc": "span class='sc'", "underline": "u", "textsf": "span", "textrm": "span", "textnormal": "span",
           "mbox": "span", "hbox": "span", "fbox": "span", "text": "span", "mathrm": "span", "mathit": "em",
           "textup": "span", "textmd": "span", "mathsf": "span", "mathtt": "code", "textsuperscript": "sup",
           "textsubscript": "sub", "uline": "u", "makebox": "span", "emphasize": "em"}
RV_DROP = {"label": (0, 1), "todo": (1, 1), "vspace": (0, 1), "hspace": (0, 1), "setlength": (0, 2), "setcounter": (0, 2),
           "addcontentsline": (0, 3), "thispagestyle": (0, 1), "pagestyle": (0, 1), "rule": (1, 2), "lipsum": (1, 0),
           "index": (0, 1), "nocite": (0, 1), "bibliography": (0, 1), "printbibliography": (1, 0), "input": (0, 1),
           "include": (0, 1), "includegraphics": (1, 1), "pagebreak": (1, 0), "twocolumn": (1, 0), "color": (0, 1),
           "phantom": (0, 1), "hypersetup": (0, 1), "bibliographystyle": (0, 1), "fontsize": (0, 2), "linespread": (0, 1),
           "addtocounter": (0, 2), "newpage": (0, 0), "clearpage": (0, 0), "tableofcontents": (0, 0), "maketitle": (0, 0),
           "onecolumn": (0, 0), "vfill": (0, 0), "bigskip": (0, 0), "medskip": (0, 0), "smallskip": (0, 0),
           "centering": (0, 0), "raggedright": (0, 0), "raggedleft": (0, 0), "small": (0, 0), "footnotesize": (0, 0),
           "scriptsize": (0, 0), "large": (0, 0), "Large": (0, 0), "LARGE": (0, 0), "huge": (0, 0), "Huge": (0, 0),
           "normalsize": (0, 0), "tiny": (0, 0), "sffamily": (0, 0), "rmfamily": (0, 0), "ttfamily": (0, 0),
           "bfseries": (0, 0), "itshape": (0, 0), "mdseries": (0, 0), "upshape": (0, 0), "slshape": (0, 0),
           "scshape": (0, 0), "normalfont": (0, 0), "noindent": (0, 0), "indent": (0, 0), "hline": (0, 0),
           "toprule": (0, 0), "midrule": (0, 0), "bottomrule": (0, 0), "cmidrule": (1, 1), "relax": (0, 0),
           "ignorespaces": (0, 0), "linebreak": (1, 0), "nolinebreak": (1, 0), "nopagebreak": (1, 0), "appendix": (0, 0),
           "protect": (0, 0), "newline": (0, 0), "hfill": (0, 0), "sloppy": (0, 0), "fussy": (0, 0), "raggedbottom": (0, 0),
           "frenchspacing": (0, 0), "tableofcontents*": (0, 0), "FloatBarrier": (0, 0), "parskip": (0, 0),
           "textwidth": (0, 0), "columnwidth": (0, 0), "linewidth": (0, 0), "cm": (0, 0), "mm": (0, 0), "pt": (0, 0),
           "bf": (0, 0), "it": (0, 0), "tt": (0, 0), "sc": (0, 0), "em": (0, 0), "rm": (0, 0), "sf": (0, 0),
           "selectlanguage": (0, 1), "foreignlanguage": (0, 1), "hyphenation": (0, 1), "leavevmode": (0, 0),
           "strut": (0, 0), "null": (0, 0), "nobreak": (0, 0), "allowbreak": (0, 0), "nonumber": (0, 0), "notag": (0, 0)}
RV_SPACES = {"quad": "\u2003", "qquad": "\u2003\u2003", "enspace": "\u2002", "thinspace": "\u2009", "space": " ",
             "enskip": "\u2002", "hspace*": " "}
RV_CITES = {"cite", "citep", "citet", "parencite", "textcite", "autocite", "Parencite", "Textcite", "citeauthor",
            "citeyear", "citealp", "citealt", "footcite", "smartcite", "Autocite", "Citeauthor", "citeyearpar"}
RV_CITES_MULTI = {"cites": "parencite", "Cites": "Parencite", "parencites": "parencite", "Parencites": "Parencite", "textcites": "textcite",
                  "Textcites": "Textcite", "autocites": "autocite", "Autocites": "Autocite", "footcites": "footcite", "smartcites": "smartcite"}
RV_REFS = {"ref", "autoref", "cref", "Cref", "eqref", "pageref", "nameref", "vref", "Vref"}
RV_ENV_DROP_ARGS = {"minipage": 1, "multicols": 1, "tabularx": 2, "tabular": 1, "tabulary": 2, "longtable": 1,
                    "tabular*": 2, "wrapfigure": 2, "adjustbox": 1}
RV_MATH_ENVS = {"equation", "equation*", "align", "align*", "displaymath", "eqnarray", "eqnarray*", "gather", "gather*",
                "multline", "multline*", "math", "split", "flalign", "flalign*"}
RV_NAME = re.compile(r"[A-Za-z]+\*?")
RV_PLAIN = re.compile(r"[^\\{}$%~&\s\-`'\[\]]+")


def rv_clean(v):
    """A bib/LaTeX value as plain text: braces and accent commands resolved."""
    v = re.sub(r"\\([\"'`^~=.cvuHkr])\s*\{?([A-Za-z])\}?",
               lambda m: unicodedata.normalize("NFC", m.group(2) + RV_ACCENTS.get(m.group(1), "")), v)
    v = re.sub(r"\\([A-Za-z]+)\s*", lambda m: RV_SYMBOLS.get(m.group(1), ""), v)
    v = (v.replace("\\&", "&").replace("\\%", "%").replace("\\_", "_").replace("\\#", "#").replace("--", "–")
         .replace("``", "“").replace("''", "”"))
    return re.sub(r"\s+", " ", v.replace("{", "").replace("}", "").replace("~", " ")).strip()


def rv_parse_bib(text):
    """{key: {type, fields, names, others}} -- enough of BibTeX/BibLaTeX to print author-year citations."""
    out = {}
    for m in re.finditer(r"^\s*@(\w+)\s*\{\s*([^,\s]+)\s*,", text, re.M):
        typ, key = m.group(1).lower(), m.group(2)
        if typ in ("comment", "string", "preamble"):
            continue
        depth, j = 1, m.end()
        while j < len(text) and depth:
            depth += (text[j] == "{") - (text[j] == "}")
            j += 1
        body, fields, k = text[m.end():j - 1], {}, 0
        for f in re.finditer(r"(\w+)\s*=\s*", body):
            if f.start() < k:
                continue
            k = f.end()
            if k < len(body) and body[k] == "{":
                d, e = 1, k + 1
                while e < len(body) and d:
                    d += (body[e] == "{") - (body[e] == "}")
                    e += 1
                fields[f.group(1).lower()] = body[k + 1:e - 1]
                k = e
            elif k < len(body) and body[k] == '"':
                e = body.find('"', k + 1)
                e = len(body) if e < 0 else e
                fields[f.group(1).lower()] = body[k + 1:e]
                k = e + 1
            else:
                e = re.search(r"[,\n]", body[k:])
                e = len(body) if not e else k + e.start()
                fields[f.group(1).lower()] = body[k:e].strip()
                k = e
        names, others, depth, cur, raw = [], False, 0, "", fields.get("author") or fields.get("editor") or ""
        parts, buf = [], ""
        for tok in re.split(r"(\{|\}|\s+and\s+)", raw):
            if tok == "{":
                depth += 1
            elif tok == "}":
                depth -= 1
            if re.fullmatch(r"\s+and\s+", tok or "") and depth == 0:
                parts.append(buf)
                buf = ""
            else:
                buf += tok
        parts.append(buf)
        for p in (x.strip() for x in parts if x.strip()):
            if p == "others":
                others = True
            elif p.startswith("{") and p.endswith("}"):
                names.append(rv_clean(p))
            elif "," in p:
                names.append(rv_clean(p.split(",")[0]))
            else:
                names.append(rv_clean(p.split()[-1]))
        out[key] = {"type": typ, "fields": {k2: rv_clean(v) for k2, v in fields.items()}, "names": names, "others": others}
    return out


def rv_author_label(e, paren=True):
    names = e["names"]
    if not names:
        return e["fields"].get("title", "")[:40] or "?"
    if e["others"] or len(names) >= 3:
        return names[0] + " et al."
    return names[0] if len(names) == 1 else names[0] + (" & " if paren else " and ") + names[1]


def rv_year(e):
    y = e["fields"].get("year") or e["fields"].get("date", "")[:4]
    return y or "n.d."


def rv_cite_text(keys, kind, bib, post="", pre=""):
    parts = []
    for k in keys:
        e = bib.get(k)
        if e is None:
            parts.append(k)
        elif kind in ("textcite", "Textcite", "citet", "citealt"):
            parts.append(f"{rv_author_label(e, False)} ({rv_year(e)})")
        elif kind in ("citeauthor", "Citeauthor"):
            parts.append(rv_author_label(e, False))
        elif kind in ("citeyear", "citeyearpar"):
            parts.append(rv_year(e))
        else:
            parts.append(f"{rv_author_label(e)}, {rv_year(e)}")
    if kind in ("textcite", "Textcite", "citet", "citealt"):
        return ", ".join(parts) + (f" ({post})" if post else "")
    if kind in ("citeauthor", "Citeauthor", "citeyear"):
        return ", ".join(parts)
    body = (f"{pre} " if pre.strip() else "") + "; ".join(parts) + (f", {post}" if post else "")
    return body if kind in ("citealp",) else f"({body})"


def rv_ref_entry(key, e):
    f = e["fields"]
    who = ", ".join(e["names"][:6]) + (" et al." if e["others"] or len(e["names"]) > 6 else "") if e["names"] else ""
    where = f.get("journal") or f.get("booktitle") or f.get("publisher") or ""
    vol = f.get("volume", "") + (f"({f['number']})" if f.get("number") else "") if f.get("volume") else ""
    bits = [b for b in (f"{who} ({rv_year(e)}).".strip(), f.get("title", "") + ".", (where + (", " + vol if vol else "")
            + (", " + f["pages"] if f.get("pages") else "")).strip(", ") + "." if where else "",
            ("doi:" + f["doi"]) if f.get("doi") else "") if b.strip(" .")]
    return " ".join(bits)


class RvCtx:
    """What the whole project knows: numbering (from main.tex's \\input order), labels, macros, bibliography."""

    def __init__(self, root, main_rel):
        self.root, self.main = root, main_rel
        self.order, self.start, self.labels, self.macros, self.bib, self.title = [], {}, {}, {}, {}, ""
        mp = root / main_rel
        main = mp.read_text(encoding="utf-8", errors="replace") if mp.exists() else ""
        mtext = re.sub(r"(?<!\\)%.*", "", main)
        for m in re.finditer(r"\\(?:input|include)\{([^}]+)\}", mtext):
            rel = m.group(1) if m.group(1).endswith(".tex") else m.group(1) + ".tex"
            if (root / rel).exists():
                self.order.append(rel)
        for rel in self.order:                       # macros: config files first (metadata, preamble)
            if rel.startswith("config/"):
                self._macros((root / rel).read_text(encoding="utf-8", errors="replace"))
        for p in sorted((root / "config").glob("*.tex")) if (root / "config").is_dir() else []:
            self._macros(p.read_text(encoding="utf-8", errors="replace"))
        self._macros(main)
        self._count()
        bibs = re.findall(r"\\addbibresource\{([^}]+)\}", mtext) or [p.name for p in sorted(root.glob("*.bib"))]
        for b in bibs:
            if (root / b).exists():
                self.bib.update(rv_parse_bib((root / b).read_text(encoding="utf-8", errors="replace")))
        t = self.macros.get("ThesisTitle")
        if t:
            sub = self.macros.get("ThesisSubtitle", ("", 0))[0]
            self.title = rv_clean(t[0]) + (": " + rv_clean(sub) if sub.strip() else "")

    def _macros(self, text):
        text = re.sub(r"(?<!\\)%.*", "", text)
        for m in re.finditer(r"\\(?:re)?newcommand\*?\s*\{?\\([A-Za-z]+)\}?\s*(?:\[(\d)\])?\s*(?:\[[^\]]*\])?\s*\{", text):
            depth, j = 1, m.end()
            while j < len(text) and depth:
                depth += (text[j] == "{") - (text[j] == "}") if text[j - 1] != "\\" else 0
                j += 1
            self.macros[m.group(1)] = (text[m.end():j - 1], int(m.group(2) or 0))

    def _count(self):
        sec = sub = subsub = tab = fig = 0
        appendix = False
        ev = re.compile(r"\\(section|subsection|subsubsection)(\*?)\s*(?:\[[^\]]*\])?\s*\{|\\(appendix)\b|\\begin\{(table\*?|figure\*?)\}"
                        r"|\\(caption)\b|\\label\{([^}]*)\}|\\end\{(table\*?|figure\*?)\}")
        cur, float_kind, float_num, early = "", None, "", []
        for rel in self.order:
            self.start[rel] = (sec, sub, subsub, tab, fig, appendix)
            text = re.sub(r"(?<!\\)%.*", "", (self.root / rel).read_text(encoding="utf-8", errors="replace"))
            for m in ev.finditer(text):
                if m.group(1):
                    if m.group(2):
                        continue
                    if m.group(1) == "section":
                        sec, sub, subsub = sec + 1, 0, 0
                        cur = (chr(64 + sec) if appendix else str(sec))
                    elif m.group(1) == "subsection":
                        sub, subsub = sub + 1, 0
                        cur = f"{chr(64 + sec) if appendix else sec}.{sub}"
                    else:
                        subsub += 1
                        cur = f"{chr(64 + sec) if appendix else sec}.{sub}.{subsub}"
                elif m.group(3):
                    appendix, sec, sub, subsub = True, 0, 0, 0
                elif m.group(4):
                    float_kind = "table" if m.group(4).startswith("table") else "figure"
                    float_num, early = "", []
                elif m.group(5) and float_kind:
                    if float_kind == "table":
                        tab += 1
                        float_num = str(tab)
                    else:
                        fig += 1
                        float_num = str(fig)
                    for lab in early:
                        self.labels[lab] = (float_kind, float_num)
                    early = []
                elif m.group(6) is not None:
                    if float_kind and float_num:
                        self.labels[m.group(6)] = (float_kind, float_num)
                    elif float_kind:
                        early.append(m.group(6))
                    elif cur:
                        self.labels[m.group(6)] = ("appendix" if appendix else "section", cur)
                elif m.group(7):
                    float_kind = None


class RvDoc:
    def __init__(self):
        self.html = self.text = ""
        self.map = []                 # per rendered character: (file index, source start, source end)
        self.regions, self.sections, self.blocks, self.cites, self.unresolved = [], [], [], [], set()
        self.refs_html = ""
        self.warnings = []

    def span(self, a, b):
        """Source span (file index, start, end) behind the rendered characters a..b (b exclusive)."""
        ch = [self.map[k] for k in range(max(a, 0), min(b, len(self.map)))]
        ch = [c for c in ch if c[2] > c[1]] or ch
        if not ch:
            return None
        return ch[0][0], ch[0][1], ch[-1][2]

    def to_rendered(self, fi, s, e):
        """Rendered range (a, b) whose characters come from source span s..e of file fi, or None."""
        ks = [k for k, (f, a, b) in enumerate(self.map) if f == fi and b > a and a < e and b > s]
        return (ks[0], ks[-1] + 1) if ks else None


class RvRender:
    def __init__(self, ctx):
        self.ctx = ctx
        self.h, self.t, self.map = [], [], []
        self.doc = RvDoc()
        self.src, self.fi = "", 0
        self.par_open = False
        self.inline_depth = 0
        self.pending = None
        self.override = None
        self.notes = []
        self.counters = [0, 0, 0, 0, 0, False]
        self.float = None
        self.macro_depth = 0

    # ---- output ------------------------------------------------------------------------------------------
    def _put(self, s, s0, e0, exact):
        if not s:
            return
        if self.override:
            s0, e0, exact = self.override[0], self.override[1], False
        self.t.append(s)
        self.h.append(html.escape(s, quote=False))
        if exact and len(s) == e0 - s0:
            self.map.extend((self.fi, s0 + k, s0 + k + 1) for k in range(len(s)))
        else:
            self.map.extend([(self.fi, s0, e0)] * len(s))

    def tag(self, s):
        self.h.append(s)

    def text(self, s, s0, e0, exact=False):
        if not self.par_open and self.inline_depth == 0:
            self.open_par(s0)
        if self.pending and (self.par_open or self.inline_depth):
            p, self.pending = self.pending, None
            self._put(" ", p[0], p[1], False)
        self.pending = None
        self._put(s, s0, e0, exact)

    def space(self, s0, e0):
        if self.par_open or self.inline_depth:
            self.pending = (self.pending[0] if self.pending else s0, e0)

    def block_start(self):
        self.doc.blocks.append(len(self.map))

    def open_par(self, pos):
        self.tag("<p>")
        self.block_start()
        self.par_open = True

    def close_par(self, pos):
        if self.par_open:
            self.pending = None
            self.tag("</p>")
            self._put("\n", pos, pos, False)
            self.par_open = False

    def sep(self, pos):
        self._put("\n", pos, pos, False)

    # ---- scanning helpers ------------------------------------------------------------------------------------
    def group_end(self, i):
        """Index of the } matching the { at i."""
        s, depth, n = self.src, 0, len(self.src)
        while i < n:
            c = s[i]
            if c == "\\":
                i += 2
                continue
            if c == "%":
                j = s.find("\n", i)
                i = n if j < 0 else j + 1
                continue
            if c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
                if depth == 0:
                    return i
            i += 1
        return n - 1

    def skip_ws(self, i, end):
        s = self.src
        while i < end and s[i] in " \t\r\n":
            i += 1
        return i

    def opt(self, i, end):
        """Optional [..] argument at i (after spaces): (inner start, inner end, next index) or None."""
        j = self.skip_ws(i, end)
        if j < end and self.src[j] == "[":
            d, k = 0, j
            while k < end:
                if self.src[k] == "{":
                    k = self.group_end(k)
                elif self.src[k] == "[":
                    d += 1
                elif self.src[k] == "]":
                    d -= 1
                    if d == 0:
                        return j + 1, k, k + 1
                k += 1
        return None

    def arg(self, i, end):
        """Required argument at i: (inner start, inner end, next index, start-of-argument)."""
        j = self.skip_ws(i, end)
        if j >= end:
            return end, end, end, end
        if self.src[j] == "{":
            e = self.group_end(j)
            return j + 1, e, e + 1, j
        if self.src[j] == "\\":
            m = RV_NAME.match(self.src, j + 1)
            e = m.end() if m else j + 2
            return j, e, e, j
        return j, j + 1, j + 1, j

    def find_env_end(self, name, i):
        """Start of the \\end{name} that closes the environment whose body begins at i."""
        pat = re.compile(r"\\(begin|end)\{" + re.escape(name) + r"\}")
        depth = 1
        for m in pat.finditer(self.src, i):
            depth += 1 if m.group(1) == "begin" else -1
            if depth == 0:
                return m.start(), m.end()
        return len(self.src), len(self.src)

    # ---- the renderer ---------------------------------------------------------------------------------------
    def run(self, i, end, until=()):
        s = self.src
        while i < end:
            c = s[i]
            if c in " \t\r\n":
                j = self.skip_ws(i, end)
                if self.inline_depth == 0 and s.count("\n", i, j) >= 2:
                    self.close_par(i)
                else:
                    self.space(i, j)
                i = j
            elif c == "%":
                j = s.find("\n", i, end)
                i = end if j < 0 else j + 1
                while i < end and s[i] in " \t":
                    i += 1
            elif c == "\\":
                i, stop = self.command(i, end, until)
                if stop:
                    return i
            elif c == "{":
                e = min(self.group_end(i), end)
                self.run(i + 1, e)
                i = e + 1
            elif c == "}":
                i += 1
            elif c == "$":
                i = self.math(i, end)
            elif c == "~":
                self.text("\u00a0", i, i + 1, True)
                i += 1
            elif c == "&":
                if "&" in until:
                    return i
                self.text("&", i, i + 1, True)
                i += 1
            elif c == "-":
                j = i
                while j < end and s[j] == "-" and j - i < 3:
                    j += 1
                self.text({1: "-", 2: "–", 3: "—"}[j - i], i, j, j - i == 1)
                i = j
            elif c == "`":
                j = i + 2 if s.startswith("``", i) else i + 1
                self.text("“" if j - i == 2 else "‘", i, j)
                i = j
            elif c == "'":
                j = i + 2 if s.startswith("''", i) else i + 1
                self.text("”" if j - i == 2 else "'", i, j, j - i == 1)
                i = j
            elif c in "[]":
                self.text(c, i, i + 1, True)
                i += 1
            else:
                m = RV_PLAIN.match(s, i)
                j = min(m.end(), end)
                self.text(s[i:j], i, j, True)
                i = j
        return i

    def command(self, i, end, until):
        """Handle the backslash at i; returns (next index, stop) -- stop when the command ends the caller's body."""
        s = self.src
        if i + 1 >= end:
            return end, False
        c = s[i + 1]
        if not c.isalpha():
            return self.control(i, end, until)
        m = RV_NAME.match(s, i + 1)
        raw = m.group(0)
        name, k = raw.rstrip("*"), m.end()
        if name in until or (name == "end" and "end" in until) or (name == "\\" and "\\\\" in until):
            return i, True
        if name in self.ctx.macros and self.macro_depth < 6:
            return self.macro(name, i, k, end), False
        k2 = self.skip_ws(k, end)
        if s.count("\n", k, k2) < 2:
            kk = k2                                  # TeX skips the spaces after a control word
        else:
            kk = k
        # ---- environments
        if name == "begin":
            return self.begin(i, k, end), False
        if name == "end":
            a, b, nxt, _ = self.arg(k, end)
            self.close_par(i)
            return nxt, False
        # ---- structure
        if name in ("section", "subsection", "subsubsection", "paragraph", "subparagraph", "chapter"):
            return self.heading(name, raw.endswith("*"), i, kk, end), False
        if name == "par":
            self.close_par(i)
            return kk, False
        if name == "item":
            return i, True
        if name == "caption":
            return self.caption(i, kk, end), False
        # ---- text styling and quotes
        if name in RV_WRAP:
            a, b, nxt, _ = self.arg(kk, end)
            tg = RV_WRAP[name]
            self.tag("<" + tg + ">")
            self.inline_depth += 1
            self.run(a, b)
            self.inline_depth -= 1
            self.tag("</" + tg.split()[0] + ">")
            return nxt, False
        if name == "enquote":
            a, b, nxt, g0 = self.arg(kk, end)
            self.text("“", i, g0 + 1)
            self.inline_depth += 1
            self.run(a, b)
            self.inline_depth -= 1
            self.text("”", b, nxt)
            return nxt, False
        if name in ("url", "path"):
            a, b, nxt, _ = self.arg(kk, end)
            self.text(s[a:b], a, b, True)
            return nxt, False
        if name == "href":
            a, b, nxt, _ = self.arg(kk, end)
            a2, b2, nxt2, _ = self.arg(nxt, end)
            self.inline_depth += 1
            self.run(a2, b2)
            self.inline_depth -= 1
            return nxt2, False
        if name == "textcolor" or name == "colorbox":
            a, b, nxt, _ = self.arg(kk, end)
            a2, b2, nxt2, _ = self.arg(nxt, end)
            self.inline_depth += 1
            self.run(a2, b2)
            self.inline_depth -= 1
            return nxt2, False
        if name == "verb":
            d = s[k]
            e = s.find(d, k + 1)
            e = end if e < 0 else e
            self.tag("<code>")
            self.text(s[k + 1:e], k + 1, e, True)
            self.tag("</code>")
            return e + 1, False
        if name == "footnote":
            return self.footnote(i, kk, end), False
        if name in RV_CITES:
            return self.cite(name, i, k, end), False
        if name in RV_CITES_MULTI:
            return self.cites(name, i, k, end), False
        if name in RV_REFS:
            return self.ref(name, i, k, end), False
        if name in ("SI", "SIrange", "SIlist", "si", "num", "ang", "numrange", "qty", "unit"):
            return self.siunitx(name, i, kk, end), False
        if name == "today":
            self.text("(date)", i, k)
            return kk, False
        if name == "textcite":
            return k, False
        if name in RV_SPACES:
            self.text(RV_SPACES[name], i, k)
            return kk if name == "space" else k2 if False else kk, False
        if name in RV_SYMBOLS:
            self.text(RV_SYMBOLS[name], i, k)
            return kk, False
        if name == "item":
            return i, True
        if name in RV_DROP:
            n_opt, n_req = RV_DROP[name]
            j = k
            for _ in range(n_opt):
                o = self.opt(j, end)
                if o:
                    j = o[2]
            for _ in range(n_req):
                j = self.arg(j, end)[2]
            return (j if (n_opt or n_req) else kk), False
        if name == "multirow":
            j = self.arg(self.arg(self.arg(kk, end)[2], end)[2], end)
            self.inline_depth += 1
            self.run(j[0], j[1])
            self.inline_depth -= 1
            return j[2], False
        if name in ("frac", "dfrac", "tfrac"):
            a, b, nxt, _ = self.arg(kk, end)
            a2, b2, nxt2, _ = self.arg(nxt, end)
            self.run(a, b)
            self.text("/", i, k)
            self.run(a2, b2)
            return nxt2, False
        if name in ("textquotedblleft", "textquotedblright"):
            self.text("“" if name.endswith("left") else "”", i, k)
            return kk, False
        # unknown command: drop the name; a following {group} is rendered as ordinary text
        o = self.opt(k, end) if k < end and s[k:k + 1] == "[" else None
        return (o[2] if o else kk), False

    def control(self, i, end, until):
        s = self.src
        c = s[i + 1]
        if c == "\\":
            if "\\\\" in until:
                return i, True
            j = i + 2
            if j < end and s[j] == "*":
                j += 1
            o = self.opt(j, end) if self.skip_ws(j, end) < end and s[self.skip_ws(j, end)] == "[" else None
            if self.inline_depth == 0 and self.par_open or self.inline_depth:
                self.tag("<br>")
                self.space(i, i + 2)
            return (o[2] if o else j), False
        if c in "%&_#${}":
            self.text(c, i, i + 2)
            return i + 2, False
        if c in ",;:! /@-":
            if c in ",;:":
                self.text("\u2009", i, i + 2)
            elif c == " ":
                self.space(i, i + 2)
            return i + 2, False
        if c in RV_ACCENTS and c != "c" and c != "v" and c != "u" and c != "H" and c != "k" and c != "r":
            j = i + 2
            if j < end and s[j] == "{":
                e = min(self.group_end(j), end)
                base = s[j + 1:e][:1]
                nxt = e + 1
            else:
                base, nxt = s[j:j + 1], j + 1
            self.text(unicodedata.normalize("NFC", base + RV_ACCENTS[c]) if base else "", i, nxt)
            return nxt, False
        if c in "()[]":
            if c in "[(":
                e = s.find("\\]" if c == "[" else "\\)", i + 2)
                e = end if e < 0 else e
                self.display_math(i + 2, e) if c == "[" else self.math_inline(i + 2, e)
                return e + 2, False
            return i + 2, False
        return i + 2, False

    def macro(self, name, i, k, end):
        body, nargs = self.ctx.macros[name]
        j, args = k, []
        for _ in range(nargs):
            a, b, j, _ = self.arg(j, end)
            args.append(self.src[a:b])
        text = body
        for n, a in enumerate(args, 1):
            text = text.replace(f"#{n}", a)
        saved = (self.src, self.override)
        self.src, self.override = text, (i, j)
        self.macro_depth += 1
        try:
            self.run(0, len(text))
        finally:
            self.macro_depth -= 1
            self.src, self.override = saved
        return self.skip_ws(j, end) if nargs == 0 and self.src.count("\n", j, self.skip_ws(j, end)) < 2 else j

    def heading(self, name, star, i, k, end):
        s = self.src
        self.close_par(i)
        o = self.opt(k, end)
        a, b, nxt, _ = self.arg(o[2] if o else k, end)
        level = {"chapter": 1, "section": 2, "subsection": 3, "subsubsection": 4}.get(name, 0)
        c = self.counters
        num = ""
        if level and not star:
            app = c[5]
            if level <= 2:
                c[0], c[1], c[2] = c[0] + 1, 0, 0
                num = chr(64 + c[0]) if app else str(c[0])
            elif level == 3:
                c[1], c[2] = c[1] + 1, 0
                num = f"{chr(64 + c[0]) if app else c[0]}.{c[1]}"
            else:
                c[2] += 1
                num = f"{chr(64 + c[0]) if app else c[0]}.{c[1]}.{c[2]}"
        start = len(self.map)
        if level:
            self.tag(f"<h{level}" + (f" data-n='{num}'" if num else "") + ">")
            self.block_start()
        else:
            self.open_par(i)
            self.tag("<strong class='run'>")
        self.inline_depth += 1
        self.run(a, b)
        self.inline_depth -= 1
        title = "".join(self.t)[start:] if False else "".join(self.t)
        self.pending = None
        if level:
            self.tag(f"</h{level}>")
            self._put("\n", nxt, nxt, False)
            self.doc.sections.append({"start": start, "end": len(self.map) - 1, "label": num, "title_len": len(self.map) - 1 - start})
        else:
            self.tag("</strong>")
            self.pending = (nxt, nxt)
        return nxt

    def footnote(self, i, k, end):
        a, b, nxt, _ = self.arg(k, end)
        self.notes.append((len(self.notes) + 1, a, b))
        self.tag(f"<sup class='fn' data-n='{len(self.notes)}'></sup>")
        return nxt

    def flush_notes(self, pos):
        notes, self.notes = self.notes, []
        if not notes:
            return
        self.close_par(pos)
        self.tag("<div class='notes'>")
        for n, a, b in notes:
            self.tag(f"<p class='note' data-n='{n}'>")
            self.block_start()
            self.inline_depth += 1
            self.run(a, b)
            self.inline_depth -= 1
            self.pending = None
            self.tag("</p>")
            self._put("\n", b, b, False)
        self.tag("</div>")

    def cite(self, name, i, k, end):
        pre = post = ""
        j = k
        o1 = self.opt(j, end)
        if o1:
            j = o1[2]
            o2 = self.opt(j, end)
            if o2:
                pre, post, j = self.src[o1[0]:o1[1]], self.src[o2[0]:o2[1]], o2[2]
            else:
                post = self.src[o1[0]:o1[1]]
        a, b, nxt, _ = self.arg(j, end)
        keys = [x.strip() for x in self.src[a:b].split(",") if x.strip()]
        for key in keys:
            if key not in self.doc.cites:
                self.doc.cites.append(key)
            if key not in self.ctx.bib:
                self.doc.unresolved.add(key)
        label = rv_cite_text(keys, name, self.ctx.bib, rv_clean(post), rv_clean(pre))
        self.tag("<span class='cite'>")
        self.text(label, i, nxt)
        self.tag("</span>")
        return nxt

    def cites(self, name, i, k, end):
        """\\parencites[pre][post]{key}[pre][post]{key}... : one label for the whole list (the arguments are adjacent)."""
        base, s, j, groups = RV_CITES_MULTI[name], self.src, k, []
        while j < end and s[j] == "(":                            # the optional (pre)(post) lists of the whole list: not shown
            e = s.find(")", j, end)
            if e < 0:
                break
            j = e + 1
        while j < end and s[j] in "[{":
            j0, opts = j, []
            while j < end and s[j] == "[":
                o = self.opt(j, end)
                if not o:
                    break
                opts.append(s[o[0]:o[1]])
                j = o[2]
            if j >= end or s[j] != "{":
                j = j0
                break
            a, b, nxt, _ = self.arg(j, end)
            keys = [x.strip() for x in s[a:b].split(",") if x.strip()]
            groups.append((keys, opts[0] if len(opts) == 2 else "", opts[-1] if opts else ""))
            j = nxt
        if not groups:
            return k
        parts = []
        for keys, pre, post in groups:
            for key in keys:
                if key not in self.doc.cites:
                    self.doc.cites.append(key)
                if key not in self.ctx.bib:
                    self.doc.unresolved.add(key)
            if base in ("textcite", "Textcite"):
                parts.append(rv_cite_text(keys, base, self.ctx.bib, rv_clean(post)))
            else:
                parts.append(rv_cite_text(keys, "citealp", self.ctx.bib, rv_clean(post), rv_clean(pre)))
        label = ", ".join(parts) if base in ("textcite", "Textcite") else "(" + "; ".join(parts) + ")"
        self.tag("<span class='cite'>")
        self.text(label, i, j)
        self.tag("</span>")
        return j

    def ref(self, name, i, k, end):
        o = self.opt(k, end)
        a, b, nxt, _ = self.arg(o[2] if o else k, end)
        out = []
        for lab in (x.strip() for x in self.src[a:b].split(",") if x.strip()):
            kind, num = self.ctx.labels.get(lab, ("", "??"))
            if name in ("cref", "Cref", "autoref", "vref", "Vref") and kind:
                word = {"section": "Section", "appendix": "Appendix", "table": "Table", "figure": "Figure"}[kind]
                out.append(f"{word} {num}")
            elif name == "eqref":
                out.append(f"({num})")
            else:
                out.append(num)
            if num == "??":
                self.doc.unresolved.add("ref:" + lab)
        self.text(", ".join(out), i, nxt)
        return nxt

    def siunitx(self, name, i, k, end):
        s = self.src
        o = self.opt(k, end)
        j = o[2] if o else k

        def unit(raw):
            u = re.sub(r"\\([A-Za-z]+)", lambda m: RV_UNITS.get(m.group(1), m.group(1)), raw)
            u = re.sub(r"[{}]", "", u).replace("~", " ").replace(".", "").replace("^2", "²").replace("^3", "³")
            return re.sub(r"\s+", "", u) if not re.search(r"[A-Za-z]{2,}\s[A-Za-z]", u) else u

        def number(raw):
            return rv_clean(re.sub(r"[{}]", "", raw)).replace("-", "−")

        if name in ("SI", "qty"):
            a, b, j2, _ = self.arg(j, end)
            a2, b2, j3, _ = self.arg(j2, end)
            u = unit(s[a2:b2])
            txt = number(s[a:b]) + ("" if u.startswith(("°", "%")) and not u.startswith("°C") else "\u00a0") + u
        elif name in ("SIrange", "numrange"):
            a, b, j2, _ = self.arg(j, end)
            a1, b1, j3, _ = self.arg(j2, end)
            if name == "SIrange":
                a2, b2, j3, _ = self.arg(j3, end)
                u = unit(s[a2:b2])
            else:
                u = ""
            sp = "" if u.startswith(("°", "%")) and not u.startswith("°C") else "\u00a0"
            txt = number(s[a:b]) + "–" + number(s[a1:b1]) + (sp + u if u else "")
            j3 = j3
            j2 = j3
            j3 = j2
        elif name in ("si", "unit"):
            a, b, j3, _ = self.arg(j, end)
            txt = unit(s[a:b])
        elif name == "SIlist":
            a, b, j2, _ = self.arg(j, end)
            a2, b2, j3, _ = self.arg(j2, end)
            txt = number(s[a:b]).replace(";", ", ") + " " + unit(s[a2:b2])
        else:                                          # num, ang
            a, b, j3, _ = self.arg(j, end)
            txt = number(s[a:b])
        if name == "SI" or name == "qty":
            j3 = j3
        self.text(txt, i, j3)
        return j3

    # ---- math --------------------------------------------------------------------------------------------------
    def math(self, i, end):
        s = self.src
        if s.startswith("$$", i):
            e = s.find("$$", i + 2, end)
            e = end if e < 0 else e
            self.display_math(i + 2, e)
            return min(e + 2, end)
        j = i + 1
        while j < end and (s[j] != "$" or s[j - 1] == "\\"):
            j += 1
        self.math_inline(i + 1, j)
        return min(j + 1, end)

    def math_inline(self, a, b):
        self.inline_depth += 1
        self.math_run(a, b)
        self.inline_depth -= 1

    def display_math(self, a, b):
        self.close_par(a)
        self.tag("<div class='math'>")
        self.block_start()
        self.inline_depth += 1
        self.math_run(a, b)
        self.inline_depth -= 1
        self.pending = None
        self.tag("</div>")
        self._put("\n", b, b, False)

    def math_run(self, a, b):
        s = self.src
        i = a
        while i < b:
            c = s[i]
            if c in " \t\r\n":
                j = self.skip_ws(i, b)
                self.space(i, j)
                i = j
            elif c == "\\":
                m = RV_NAME.match(s, i + 1)
                if not m:
                    nxt = i + 2
                    if i + 1 < b and s[i + 1] in ",;:":
                        self.text("\u2009", i, nxt)
                    elif i + 1 < b and s[i + 1] in "%&_#${}":
                        self.text(s[i + 1], i, nxt)
                    i = nxt
                    continue
                name, k = m.group(0).rstrip("*"), m.end()
                if name in RV_SYMBOLS:
                    self.text(RV_SYMBOLS[name], i, k)
                    i = self.skip_ws(k, b) if k < b and s[k] == " " else k
                elif name in ("frac", "dfrac", "tfrac"):
                    a1, b1, n1, _ = self.arg(k, b)
                    a2, b2, n2, _ = self.arg(n1, b)
                    self.math_run(a1, b1)
                    self.text("/", i, k)
                    self.math_run(a2, b2)
                    i = n2
                elif name == "sqrt":
                    a1, b1, n1, _ = self.arg(k, b)
                    self.text("√", i, k)
                    self.math_run(a1, b1)
                    i = n1
                elif name in RV_WRAP or name in ("operatorname", "mathcal", "mathbb", "boldsymbol", "bm", "vec", "hat", "bar", "tilde", "overline", "underline"):
                    a1, b1, n1, _ = self.arg(k, b)
                    self.math_run(a1, b1)
                    i = n1
                elif name in ("left", "right", "big", "Big", "bigg", "Bigg", "bigl", "bigr", "displaystyle", "limits", "nolimits"):
                    i = k
                    if name in ("left", "right") and i < b and s[i] in "()[]|.":
                        if s[i] != ".":
                            self.text(s[i], i, i + 1, True)
                        i += 1
                elif name == "text" or name == "mbox":
                    a1, b1, n1, _ = self.arg(k, b)
                    self.text(s[a1:b1], a1, b1, True)
                    i = n1
                else:
                    i = k
            elif c in "^_":
                a1, b1, n1, _ = self.arg(i + 1, b)
                tg = "sup" if c == "^" else "sub"
                self.tag(f"<{tg}>")
                self.math_run(a1, b1)
                self.tag(f"</{tg}>")
                i = n1
            elif c in "{}":
                i += 1
            elif c == "-":
                self.text("−", i, i + 1)
                i += 1
            else:
                self.text(c, i, i + 1, True)
                i += 1

    # ---- environments ------------------------------------------------------------------------------------------
    def begin(self, i, k, end):
        s = self.src
        a, b, nxt, _ = self.arg(k, end)
        env = s[a:b].strip()
        bstart = nxt
        if env in RV_ENV_DROP_ARGS and env not in ("tabular", "tabularx", "tabulary", "longtable", "tabular*"):
            for _ in range(RV_ENV_DROP_ARGS[env]):
                bstart = self.arg(bstart, end)[2]
            return bstart
        eb, ee = self.find_env_end(env, nxt)
        eb, ee = min(eb, end), min(ee, end)
        if env in ("itemize", "enumerate", "description"):
            return self.list_env(env, bstart, eb, ee, i)
        if env in ("table", "table*", "figure", "figure*", "wrapfigure", "sidewaystable", "sidewaysfigure"):
            return self.float_env(env, bstart, eb, ee, i)
        if env in ("tabular", "tabularx", "tabulary", "longtable", "tabular*"):
            j = bstart
            o = self.opt(j, eb)
            j = o[2] if o else j
            for _ in range(RV_ENV_DROP_ARGS[env]):
                j = self.arg(j, eb)[2]
            self.table(j, eb)
            return ee
        if env in RV_MATH_ENVS:
            self.display_math(bstart, eb)
            return ee
        if env in ("verbatim", "lstlisting", "minted"):
            self.close_par(i)
            self.tag("<pre>")
            self.block_start()
            self.text(s[bstart:eb].strip("\n"), bstart, eb)
            self.tag("</pre>")
            self.sep(eb)
            return ee
        wrap = {"quote": "blockquote", "quotation": "blockquote", "center": "div class='center'", "abstract": "div class='abstract'",
                "flushleft": "div", "flushright": "div"}.get(env)
        if wrap:
            self.close_par(i)
            self.tag("<" + wrap + ">")
            self.run(bstart, eb)
            self.close_par(eb)
            self.tag("</" + wrap.split()[0] + ">")
            return ee
        return bstart                                  # unknown environment: transparent

    def list_env(self, env, bstart, eb, ee, i):
        s = self.src
        self.close_par(i)
        tag = {"itemize": "ul", "enumerate": "ol", "description": "dl"}[env]
        self.tag(f"<{tag}>")
        j = bstart
        # text before the first \item is ignored
        m = re.compile(r"\\item\b").search(s, j, eb)
        while m:
            k = m.end()
            label = self.opt(k, eb)
            k2 = label[2] if label else k
            nxt = re.compile(r"\\item\b").search(s, k2, eb)
            stop = nxt.start() if nxt else eb
            # find the next \item that is not inside a nested environment: run() returns at a top-level \item
            if env == "description":
                self.tag("<dt>")
                self.block_start()
                self.inline_depth += 1
                if label:
                    self.run(label[0], label[1])
                self.inline_depth -= 1
                self.pending = None
                self.tag("</dt><dd>")
            else:
                self.tag("<li>")
                self.block_start()
            self.inline_depth += 1
            j = self.run(k2, eb, until=("item",))
            self.inline_depth -= 1
            self.pending = None
            self.tag("</dd>" if env == "description" else "</li>")
            self._put("\n", j, j, False)
            m = re.compile(r"\\item\b").match(s, j) if j < eb else None
        self.tag(f"</{tag}>")
        self._put("\n", eb, eb, False)
        return ee

    def float_env(self, env, bstart, eb, ee, i):
        self.close_par(i)
        kind = "table" if "table" in env else "figure"
        o = self.opt(bstart, eb)
        j = o[2] if o else bstart
        c = self.counters
        saved = self.float
        self.float = kind
        self.tag(f"<figure class='float {kind}'>")
        self.run(j, eb)
        self.close_par(eb)
        self.tag("</figure>")
        self._put("\n", eb, eb, False)
        self.float = saved
        return ee

    def caption(self, i, k, end):
        o = self.opt(k, end)
        a, b, nxt, _ = self.arg(o[2] if o else k, end)
        kind = self.float or "table"
        c = self.counters
        idx = 3 if kind == "table" else 4
        c[idx] += 1
        self.close_par(i)
        self.tag(f"<figcaption data-n='{'Table' if kind == 'table' else 'Figure'} {c[idx]}'>")
        self.block_start()
        self.inline_depth += 1
        self.run(a, b)
        self.inline_depth -= 1
        self.pending = None
        self.tag("</figcaption>")
        self._put("\n", nxt, nxt, False)
        return nxt

    def table(self, a, b):
        s = self.src
        self.close_par(a)
        self.tag("<table><tbody>")
        i, rule = a, ""
        stops = ("&", "\\\\", "toprule", "midrule", "bottomrule", "hline", "cmidrule", "end")
        while i < b:
            i = self.skip_ws(i, b)
            if i >= b:
                break
            # rule commands before a row
            m = re.compile(r"\\(toprule|midrule|bottomrule|hline|cmidrule)\*?").match(s, i)
            if m:
                rule = " class='rule'"
                i = m.end()
                if m.group(1) == "cmidrule":
                    o = self.opt(i, b)
                    i = o[2] if o else i
                    i = self.arg(i, b)[2]
                continue
            self.tag(f"<tr{rule}>")
            rule = ""
            cells = 0
            while True:
                i = self.skip_ws(i, b)
                span, mc = 1, None
                if s.startswith("\\multicolumn", i):
                    n1 = self.arg(i + len("\\multicolumn"), b)
                    n2 = self.arg(n1[2], b)
                    n3 = self.arg(n2[2], b)
                    try:
                        span = int(s[n1[0]:n1[1]])
                    except ValueError:
                        span = 1
                    mc = (n3[0], n3[1])
                    i = n3[2]
                self.tag("<td" + (f" colspan='{span}'" if span > 1 else "") + ">")
                self.block_start()
                self.inline_depth += 1
                if mc:
                    self.run(mc[0], mc[1])
                j = self.run(i, b, until=stops)
                self.inline_depth -= 1
                self.pending = None
                self.tag("</td>")
                cells += 1
                i = j
                if i < b and s[i] == "&":
                    i += 1
                    continue
                break
            self.tag("</tr>")
            if i < b and s.startswith("\\\\", i):
                i += 2
                o = self.opt(i, b) if self.skip_ws(i, b) < b and s[self.skip_ws(i, b)] == "[" else None
                i = o[2] if o else i
            elif i < b and s.startswith("\\end", i):
                break
        self.tag("</tbody></table>")
        self._put("\n", b, b, False)

    # ---- whole files -------------------------------------------------------------------------------------------
    def file(self, fi, rel, text):
        self.fi, self.src = fi, text
        self.counters = list(self.ctx.start.get(rel, (0, 0, 0, 0, 0, False)))
        start = len(self.map)
        self.run(0, len(text))
        self.close_par(len(text))
        self.flush_notes(len(text))
        self.doc.regions.append({"rel": rel, "fi": fi, "start": start, "end": len(self.map),
                                 "hash": hashlib.sha256(text.encode("utf-8")).hexdigest()})


def rv_render(root, rels, main_rel="main.tex"):
    """Render project files (relative paths, in the order given) into one reading view with its source map."""
    ctx = RvCtx(root, main_rel)
    rr = RvRender(ctx)
    for fi, rel in enumerate(rels):
        rr.file(fi, rel, (root / rel).read_text(encoding="utf-8", errors="replace"))
    d = rr.doc
    d.html, d.text, d.map = "".join(rr.h), "".join(rr.t), rr.map
    assert len(d.map) == len(d.text), (len(d.map), len(d.text))
    d.title = ctx.title
    entries = sorted(((k, ctx.bib[k]) for k in d.cites if k in ctx.bib), key=lambda kv: (rv_author_label(kv[1]).lower(), rv_year(kv[1])))
    d.refs_html = "".join("<p class='ref'>" + html.escape(rv_ref_entry(k, e), quote=False) + "</p>" for k, e in entries)
    d.n_refs = len(entries)
    return d


# -- settings (who the author is) ---------------------------------------------------------------------------
SET_FILE = ".texpad-settings.json"
SET_LOCK = threading.Lock()


def settings_load():
    p = ROOT / SET_FILE
    try:
        d = json.loads(p.read_text(encoding="utf-8")) if p.exists() else {}
        return d if isinstance(d, dict) else {}
    except Exception:                                           # noqa: BLE001
        return {}


def settings_author():
    return str(settings_load().get("author") or "").strip()[:60] or "you"


def settings_save(update):
    with SET_LOCK:
        p = ROOT / SET_FILE
        if p.exists():
            try:
                if not isinstance(json.loads(p.read_text(encoding="utf-8")), dict):
                    raise ValueError
            except Exception:                                   # noqa: BLE001
                raise AnnError(f"{SET_FILE} exists but is not a JSON object; texpad will not overwrite it")
        d = settings_load()
        if "author" in update:
            d["author"] = str(update["author"]).strip()[:60] or "you"
        tmp = p.with_name(p.name + ".tmp")
        tmp.write_text(json.dumps(d, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
        os.replace(tmp, p)
        return d


# -- the review file --------------------------------------------------------------------------------------------
RV_PAGE = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>__TITLE__</title>
<style>
  :root{--bg:#fff;--ink:#1c1f23;--muted:#66707a;--line:#dde1e6;--panel:#f6f7f9;--accent:#2563eb;--bad:#b42318;
        --mine:rgba(255,205,0,.40);--theirs:rgba(37,99,235,.17);--done:rgba(120,130,140,.18)}
  @media (prefers-color-scheme: dark){
    :root{--bg:#15181b;--ink:#e6e9ec;--muted:#9aa4af;--line:#2b3138;--panel:#1c2024;--accent:#6aa5ff;
          --mine:rgba(255,205,0,.30);--theirs:rgba(106,165,255,.24);--done:rgba(150,160,170,.20)}}
  *{box-sizing:border-box} html,body{margin:0}
  body{background:var(--bg);color:var(--ink);font:15px/1.5 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif}
  button{font:inherit;padding:5px 12px;border-radius:6px;border:1px solid var(--line);background:var(--bg);color:var(--ink);cursor:pointer}
  button:hover{border-color:var(--accent)} button.primary{background:var(--accent);color:#fff;border-color:var(--accent)}
  button.small{padding:1px 8px;font-size:12px}
  input[type=text],textarea{font:inherit;border:1px solid var(--line);border-radius:6px;background:var(--bg);color:var(--ink);padding:5px 8px;width:100%}
  .hint{color:var(--muted);font-size:13px}
  #top{padding:16px 24px;border-bottom:1px solid var(--line);background:var(--panel)}
  #top h1{font:600 21px/1.3 Georgia,"Times New Roman",serif;margin:0 0 4px}
  #top .note{margin:6px 0;color:var(--muted);font-size:13.5px}
  #top .msg{margin:10px 0;padding:10px 12px;border-left:4px solid var(--accent);background:var(--bg);white-space:pre-wrap;border-radius:4px}
  #top ol{margin:8px 0 10px;padding-left:20px;font-size:14px} #top .bar{display:flex;gap:8px;flex-wrap:wrap;align-items:center;margin-top:8px}
  #wrap{display:flex;align-items:flex-start}
  #page{flex:1 1 auto;min-width:0;padding:22px 30px 90px;max-width:860px;margin:0 auto}
  #doc{font:18px/1.72 Georgia,"Times New Roman",serif}
  #doc p{margin:0 0 .9em} #doc h2{font:600 1.5em/1.3 Georgia,serif;margin:1.6em 0 .5em} #doc h3{font:600 1.25em/1.3 Georgia,serif;margin:1.4em 0 .4em}
  #doc h4{font:600 1.05em/1.3 Georgia,serif;margin:1.2em 0 .3em}
  #doc h2[data-n]::before,#doc h3[data-n]::before,#doc h4[data-n]::before{content:attr(data-n) "  ";color:var(--muted);font-weight:400}
  #doc .fn::after{content:attr(data-n);vertical-align:super;font-size:.7em;color:var(--accent);margin:0 1px}
  #doc .notes{border-top:1px solid var(--line);margin-top:1.4em;padding-top:.6em;font-size:.88em;color:var(--muted)}
  #doc .note::before{content:attr(data-n) ". ";font-weight:600}
  #doc .sc{font-variant:small-caps} #doc code{font:.88em ui-monospace,Menlo,monospace} #doc .math{text-align:center;margin:.8em 0}
  #doc blockquote{margin:1em 1.5em;color:var(--muted)} #doc .cite{white-space:normal}
  #doc ul,#doc ol,#doc dl{margin:0 0 1em} #doc li{margin:0 0 .3em} #doc dt{font-weight:600}
  #doc figure.float{margin:1.4em 0;padding:0;overflow-x:auto} #doc figcaption{font-size:.88em;margin:0 0 .5em}
  #doc figcaption::before{content:attr(data-n) ": ";font-weight:700;font-style:normal}
  #doc table{border-collapse:collapse;font:.84em/1.4 -apple-system,"Segoe UI",sans-serif;width:100%}
  #doc td{padding:3px 8px;vertical-align:top} #doc tr.rule td{border-top:1.5px solid var(--ink)} #doc tr:last-child td{border-bottom:1.5px solid var(--ink)}
  #refs{border-top:1px solid var(--line);margin-top:2.5em;padding-top:1em;font:14px/1.5 Georgia,serif;color:var(--muted)}
  #refs h3{font:600 16px -apple-system,sans-serif;color:var(--ink)} #refs .ref{margin:0 0 .5em;padding-left:1.4em;text-indent:-1.4em}
  span.cm{border-bottom:2px solid rgba(217,119,6,.75);background:var(--mine);cursor:pointer}
  span.cm.theirs{border-bottom-color:rgba(37,99,235,.8);background:var(--theirs)}
  span.cm.done{border-bottom:1px dotted var(--muted);background:var(--done)}
  span.cm.on{outline:2px solid var(--accent);border-radius:2px}
  span.cm.flash{animation:fl 1.4s ease-out} @keyframes fl{0%{background:rgba(255,196,0,.95)}100%{background:rgba(255,196,0,0)}}
  #panel{flex:0 0 370px;position:sticky;top:0;height:100vh;overflow:auto;border-left:1px solid var(--line);background:var(--panel);padding:0 0 30px}
  #panel .ph{display:flex;align-items:center;gap:8px;padding:10px 12px;border-bottom:1px solid var(--line);position:sticky;top:0;background:var(--panel);z-index:2;flex-wrap:wrap}
  #newbox{padding:10px 12px;border-bottom:1px solid var(--line);background:var(--bg)} #newbox[hidden]{display:none}
  #list{padding:8px 10px}
  .card{border:1px solid var(--line);border-radius:8px;padding:8px 10px;margin:0 0 9px;background:var(--bg);font-size:13.5px;cursor:pointer}
  .card.on{border-color:var(--accent);box-shadow:0 0 0 1px var(--accent)} .card.done{opacity:.6}
  .card .meta{display:flex;gap:6px;align-items:baseline;flex-wrap:wrap} .card .q{color:var(--muted);font-style:italic;margin:3px 0;border-left:3px solid var(--line);padding-left:6px;overflow-wrap:anywhere}
  .card .t{white-space:pre-wrap;overflow-wrap:anywhere;margin:3px 0} .card .r{border-top:1px dashed var(--line);margin-top:5px;padding-top:4px;white-space:pre-wrap;overflow-wrap:anywhere}
  .card .act{display:flex;gap:6px;margin-top:6px;flex-wrap:wrap}
  .badge{font-size:11px;padding:0 7px;border-radius:99px;color:#fff;line-height:17px;background:#6b7280}
  .badge.decide{background:#2563eb}.badge.source{background:#7c3aed}.badge.check{background:#d97706}.badge.review{background:#0d9488}.badge.me{background:#b45309}
  .ro{font-size:11px;color:var(--muted)}
  #fab{position:fixed;z-index:20;display:none} #modal{position:fixed;inset:0;background:rgba(0,0,0,.4);display:flex;align-items:center;justify-content:center;z-index:50}
  #modal[hidden]{display:none} #modal .box{background:var(--bg);border-radius:10px;padding:18px 20px;width:min(420px,92vw)}
  #printview{display:none}
  @media (max-width:900px){#wrap{display:block}#panel{position:static;height:auto;border-left:0;border-top:1px solid var(--line)}}
  @media print{
    body.pc #top,body.pc #wrap,body.pc #fab,body.pc #modal{display:none!important} body.pc #printview{display:block}
    #printview h1{font:600 20px Georgia,serif} #printview .pc{break-inside:avoid;border-bottom:1px solid #999;padding:6px 0;font:13px/1.45 Georgia,serif}
    #printview .q{font-style:italic;color:#444}
  }
</style></head><body>
<div id="top">
  <h1>__TITLE__</h1>
  <div class="note" id="who"></div>
  __MESSAGE__
  <div class="note">This is a <b>reading copy</b>: the page is rendered from the LaTeX source and is not the typeset document. <b>The typeset PDF is the reference</b> for layout, numbering and anything that looks different here.</div>
  <ol>
    <li>Select the text you want to comment on, then click <b>Comment</b>.</li>
    <li>Your comments are kept in this browser while you work: closing the tab loses nothing.</li>
    <li>When you are done click <b>Download my comments</b> and email the downloaded file back.</li>
  </ol>
  <div class="bar">
    <button id="b-comment" class="primary">Comment</button>
    <button id="b-down">Download my comments</button>
    <button id="b-print">Print comments</button>
    <button id="b-pdf" hidden>Open typeset PDF</button>
    <button id="b-name" class="small">Your name</button>
    <span class="hint" id="saved"></span>
  </div>
</div>
<div id="wrap">
  <main id="page"><div id="doc">__DOC__</div><section id="refs"><h3>References</h3>__REFS__</section></main>
  <aside id="panel">
    <div class="ph"><b>Comments</b> <span class="hint" id="count"></span><span style="flex:1"></span>
      <select id="filter"><option value="open">open</option><option value="resolved">resolved</option><option value="all">all</option></select></div>
    <div id="newbox" hidden><div class="hint" id="newq"></div><textarea id="newtext" rows="4" placeholder="Your comment"></textarea>
      <div class="act" style="display:flex;gap:6px;margin-top:6px"><button id="newadd" class="primary">Add comment</button><button id="newcancel">Cancel</button></div></div>
    <div id="list"></div>
  </aside>
</div>
<button id="fab" class="primary">Comment</button>
<div id="printview"></div>
<div id="modal" hidden><div class="box"><b>Your name</b><p class="hint">It is written on your comments, so the author knows who wrote them. It stays in this browser.</p>
  <input type="text" id="nameinp" placeholder="Name"><div style="display:flex;gap:6px;margin-top:10px"><button id="nameok" class="primary">OK</button><button id="namecancel">Cancel</button></div></div></div>
<script type="application/json" id="rv-data">__DATA__</script>
<script type="text/plain" id="rv-pdf">__PDF__</script>
<script>
(function(){
"use strict";
var D = JSON.parse(document.getElementById("rv-data").textContent);
var doc = document.getElementById("doc"), TEXT = doc.textContent;
var KEY = "texpad-review:" + D.hash;
function $(s){ return document.querySelector(s); }
function esc(s){ return String(s == null ? "" : s).replace(/[&<>"]/g, function(c){ return {"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;"}[c]; }); }
var st = {name:"", mine:[], filter:"open"}, theirs = D.comments || [], active = null, flashId = null, pending = null, editing = null;

function load(){
  try{
    var j = JSON.parse(localStorage.getItem(KEY) || "null");
    if(j){ st.name = j.name || ""; st.mine = Array.isArray(j.mine) ? j.mine : []; }
    if(!st.name) st.name = localStorage.getItem("texpad-review-name") || "";
  }catch(e){}
  if(!st.name) st.name = D.reviewer || "";       // the author named the reader: they can still change it ("Your name")
}
function save(){
  try{
    localStorage.setItem(KEY, JSON.stringify({name:st.name, mine:st.mine}));
    if(st.name) localStorage.setItem("texpad-review-name", st.name);
    $("#saved").textContent = "saved in this browser";
  }catch(e){ $("#saved").textContent = "this browser would not store your progress: download your comments before you close the tab"; }
}
function offsetOf(node, off){
  var r = document.createRange(); r.setStart(doc, 0); r.setEnd(node, off); return r.toString().length;
}
function curSel(){
  var s = window.getSelection(); if(!s || !s.rangeCount || s.isCollapsed) return null;
  var r = s.getRangeAt(0);
  if(!doc.contains(r.startContainer) || !doc.contains(r.endContainer)) return null;
  var a = offsetOf(r.startContainer, r.startOffset), b = offsetOf(r.endContainer, r.endOffset);
  while(a < b && /\s/.test(TEXT[a])) a++;
  while(b > a && /\s/.test(TEXT[b - 1])) b--;
  return b > a ? {start:a, end:b} : null;
}
function secLabel(a){
  var out = "";
  for(var i = 0; i < D.sections.length; i++){ if(D.sections[i].start <= a) out = D.sections[i].label; else break; }
  return out;
}
function paraIdx(a){ var n = 0; for(var i = 0; i < D.blocks.length; i++){ if(D.blocks[i] <= a) n = i + 1; else break; } return n; }
function fileOf(a){ for(var i = 0; i < D.regions.length; i++){ if(a >= D.regions[i].start && a < D.regions[i].end) return D.regions[i].rel; } return D.file; }

/* ---- highlights: spans around the commented text; they add elements, never characters ---- */
function unwrap(){
  var sp = doc.querySelectorAll("span.cm");
  for(var i = 0; i < sp.length; i++){ var p = sp[i].parentNode; while(sp[i].firstChild) p.insertBefore(sp[i].firstChild, sp[i]); p.removeChild(sp[i]); }
  doc.normalize();
}
function textNodes(){
  var out = [], w = document.createTreeWalker(doc, NodeFilter.SHOW_TEXT), n, pos = 0;
  while((n = w.nextNode())){ out.push({n:n, s:pos, e:pos + n.data.length}); pos += n.data.length; }
  return out;
}
function items(){
  var out = [];
  theirs.forEach(function(c){ if(c.rs != null && c.rs >= 0 && c.re > c.rs) out.push({id:c.id, s:c.rs, e:c.re, k:"theirs", open:c.status !== "resolved"}); });
  st.mine.forEach(function(c){ out.push({id:c.id, s:c.start, e:c.end, k:"mine", open:c.status !== "resolved"}); });
  return out;
}
function highlight(){
  unwrap();
  var its = items(), cuts = {};
  its.forEach(function(i){ cuts[i.s] = 1; cuts[i.e] = 1; });
  var pts = Object.keys(cuts).map(Number).sort(function(a, b){ return b - a; });
  textNodes().forEach(function(t){
    var node = t.n;
    pts.forEach(function(c){ if(c > t.s && c < t.e){ var cut = c - t.s; if(cut < node.data.length) node.splitText(cut); } });
  });
  textNodes().forEach(function(t){
    var cov = its.filter(function(i){ return i.s <= t.s && i.e >= t.e; });
    if(!cov.length) return;
    var live = cov.filter(function(i){ return i.open; }), mine = live.some(function(i){ return i.k === "mine"; });
    var sp = document.createElement("span");
    sp.className = "cm " + (!live.length ? "done" : mine ? "mine" : "theirs") +
      (cov.some(function(i){ return i.id === active; }) ? " on" : "") + (cov.some(function(i){ return i.id === flashId; }) ? " flash" : "");
    sp.setAttribute("data-ids", cov.map(function(i){ return i.id; }).join(" "));
    t.n.parentNode.insertBefore(sp, t.n); sp.appendChild(t.n);
  });
}

/* ---- panel ---- */
function all(){
  var a = theirs.map(function(c){ return {c:c, me:false, pos:c.rs == null ? -1 : c.rs}; })
    .concat(st.mine.map(function(c){ return {c:c, me:true, pos:c.start}; }));
  return a.sort(function(x, y){ return x.pos - y.pos; });
}
function dateOf(s){                       // the reader's own times are UTC (...Z): show them in the reader's local time, like the author's
  s = String(s || "");
  if(/Z$/.test(s)){ var d = new Date(s); if(!isNaN(d)) return d.getFullYear() + "-" + pad(d.getMonth() + 1) + "-" + pad(d.getDate()) + " " + pad(d.getHours()) + ":" + pad(d.getMinutes()); }
  return s.replace("T", " ").slice(0, 16);
}
function card(o){
  var c = o.c, done = c.status === "resolved";
  var who = o.me ? (st.name || "you") : (c.author || "the author");
  var reps = (c.replies || []).map(function(r){ return "<div class='r'><b>" + esc(r.author) + "</b> <span class='hint'>" + esc(dateOf(r.created)) + "</span><br>" + esc(r.text) + "</div>"; }).join("");
  var body;
  if(editing && editing.id === c.id && editing.mode === "edit"){
    body = "<textarea class='ft' rows='3'>" + esc(c.text) + "</textarea><div class='act'><button class='small primary' data-a='saveedit'>Save</button><button class='small' data-a='cancel'>Cancel</button></div>";
  } else {
    body = "<div class='t'>" + esc(c.text) + "</div>" + reps;
    if(o.me){
      if(editing && editing.id === c.id && editing.mode === "reply")
        body += "<textarea class='ft' rows='2' placeholder='Reply'></textarea><div class='act'><button class='small primary' data-a='send'>Reply</button><button class='small' data-a='cancel'>Cancel</button></div>";
      else body += "<div class='act'><button class='small' data-a='reply'>Reply</button><button class='small' data-a='toggle'>" + (done ? "Reopen" : "Resolve") +
        "</button><button class='small' data-a='edit'>Edit</button><button class='small' data-a='del'>Delete</button></div>";
    } else body += "<div class='ro'>from the author, read-only</div>";
  }
  var q = o.me ? c.quote : (c.rs != null && c.rs >= 0 ? TEXT.slice(c.rs, c.re) : "");
  return "<div class='card" + (done ? " done" : "") + (c.id === active ? " on" : "") + "' data-id='" + esc(c.id) + "' data-me='" + (o.me ? 1 : 0) + "'>" +
    "<div class='meta'><span class='badge " + (o.me ? "me" : esc(c.kind || "info")) + "'>" + (o.me ? "you" : esc(c.kind || "note")) + "</span> <b>" + esc(who) +
    "</b> <span class='hint'>" + esc(dateOf(c.created)) + (done ? " · resolved" : "") + "</span></div>" +
    (q ? "<div class='q'>“" + esc(q.length > 160 ? q.slice(0, 160) + "…" : q) + "”</div>" : "") + body + "</div>";
}
function render(){
  var list = all().filter(function(o){ var d = o.c.status === "resolved"; return st.filter === "all" || (st.filter === "open") === !d; });
  $("#list").innerHTML = list.map(card).join("") || "<p class='hint'>" + (all().length ? "Nothing matches the filter." : "No comments yet. Select text and click Comment.") + "</p>";
  var open = all().filter(function(o){ return o.c.status !== "resolved"; }).length;
  $("#count").textContent = open + " open · " + (all().length - open) + " resolved · " + st.mine.length + " yours";
  $("#who").textContent = st.name ? "Commenting as " + st.name : "";
  highlight();
}
function askName(then){
  $("#nameinp").value = st.name; $("#modal").hidden = false; $("#nameinp").focus();
  function ok(){ var v = $("#nameinp").value.trim(); if(!v) return; st.name = v; save(); $("#modal").hidden = true; cleanup(); render(); if(then) then(); }
  function cancel(){ $("#modal").hidden = true; cleanup(); }
  function key(e){ if(e.key === "Enter") ok(); else if(e.key === "Escape") cancel(); }
  function cleanup(){ $("#nameok").removeEventListener("click", ok); $("#namecancel").removeEventListener("click", cancel); $("#nameinp").removeEventListener("keydown", key); }
  $("#nameok").addEventListener("click", ok); $("#namecancel").addEventListener("click", cancel); $("#nameinp").addEventListener("keydown", key);
}
function startAdd(){
  var s = curSel() || pending;
  if(!s){ $("#saved").textContent = "Select the text you want to comment on first."; return; }
  if(s.end - s.start > 1500){ $("#saved").textContent = "Please select a shorter passage (at most 1500 characters)."; return; }
  var go = function(){ pending = s; $("#newq").textContent = "Comment on “" + (TEXT.slice(s.start, s.end).length > 120 ? TEXT.slice(s.start, s.start + 120) + "…" : TEXT.slice(s.start, s.end)) + "”";
    $("#newtext").value = ""; $("#newbox").hidden = false; $("#newtext").focus(); $("#fab").style.display = "none"; };
  if(!st.name) askName(go); else go();
}
function addComment(a, b, text){
  var c = {id:"r-" + Date.now().toString(36) + Math.random().toString(36).slice(2, 6), start:a, end:b, quote:TEXT.slice(a, b),
    prefix:TEXT.slice(Math.max(0, a - 40), a), suffix:TEXT.slice(b, b + 40), section:secLabel(a), para:paraIdx(a), file:fileOf(a),
    text:text, created:new Date().toISOString(), status:"open", replies:[]};
  st.mine.push(c); active = c.id; flashId = c.id; save(); render();
  setTimeout(function(){ flashId = null; highlight(); }, 1500);
  return c;
}
function submitNew(){
  var t = $("#newtext").value.trim();
  if(!t || !pending) return;
  addComment(pending.start, pending.end, t);
  pending = null; $("#newbox").hidden = true;
}
function find(id){ for(var i = 0; i < st.mine.length; i++) if(st.mine[i].id === id) return st.mine[i]; return null; }
function jump(id){
  active = id; flashId = id; render();
  var el = doc.querySelector("span.cm[data-ids~='" + id + "']");
  if(el) el.scrollIntoView({block:"center", behavior:"smooth"});
  setTimeout(function(){ flashId = null; highlight(); }, 1500);
}
$("#list").addEventListener("click", function(ev){
  var cd = ev.target.closest(".card"); if(!cd) return;
  var id = cd.getAttribute("data-id"), c = find(id), btn = ev.target.closest("button");
  if(!btn){ if(!ev.target.closest("textarea")) jump(id); return; }
  var a = btn.getAttribute("data-a"), ta = cd.querySelector(".ft"), val = ta ? ta.value.trim() : "";
  if(!c) return;
  if(a === "reply" || a === "edit"){ editing = {id:id, mode:a}; render(); var f = document.querySelector(".card[data-id='" + id + "'] .ft"); if(f) f.focus(); }
  else if(a === "cancel"){ editing = null; render(); }
  else if(a === "send"){ if(val){ c.replies.push({author:st.name || "reviewer", text:val, created:new Date().toISOString()}); editing = null; save(); render(); } }
  else if(a === "saveedit"){ if(val){ c.text = val; editing = null; save(); render(); } }
  else if(a === "toggle"){ c.status = c.status === "resolved" ? "open" : "resolved"; save(); render(); }
  else if(a === "del"){ if(confirm("Delete this comment?")){ st.mine = st.mine.filter(function(x){ return x.id !== id; }); save(); render(); } }
});
doc.addEventListener("click", function(ev){
  var sp = ev.target.closest("span.cm"); if(!sp) return;
  var id = sp.getAttribute("data-ids").split(" ")[0]; active = id; render();
  var cd = document.querySelector(".card[data-id='" + id + "']"); if(cd) cd.scrollIntoView({block:"nearest"});
});
/* ---- floating Comment button next to a selection ---- */
function fab(){
  var s = curSel(), f = $("#fab");
  if(!s || !$("#newbox").hidden){ f.style.display = "none"; return; }
  var r = window.getSelection().getRangeAt(0).getBoundingClientRect();
  f.style.display = "block"; f.style.top = Math.max(8, r.bottom + 6) + "px"; f.style.left = Math.min(window.innerWidth - 100, Math.max(8, r.left)) + "px";
}
document.addEventListener("mouseup", function(){ setTimeout(fab, 0); });
document.addEventListener("keyup", function(){ setTimeout(fab, 0); });
$("#fab").addEventListener("mousedown", function(e){ e.preventDefault(); });
$("#fab").addEventListener("click", startAdd);
$("#b-comment").addEventListener("mousedown", function(e){ e.preventDefault(); });
$("#b-comment").addEventListener("click", startAdd);
$("#newadd").addEventListener("click", submitNew);
$("#newcancel").addEventListener("click", function(){ pending = null; $("#newbox").hidden = true; });
$("#newtext").addEventListener("keydown", function(e){ if((e.metaKey || e.ctrlKey) && e.key === "Enter"){ e.preventDefault(); submitNew(); } });
$("#filter").addEventListener("change", function(e){ st.filter = e.target.value; render(); });
$("#b-name").addEventListener("click", function(){ askName(null); });

/* ---- download, print, typeset PDF ---- */
function pad(n){ return (n < 10 ? "0" : "") + n; }
function ymd(d){ return d.getFullYear() + pad(d.getMonth() + 1) + pad(d.getDate()); }
function exportJSON(){
  return {format:"texpad-review-comments", version:1, project:D.project, file:D.file, source_hash:D.source_hash, reviewer:st.name,
    exported:new Date().toISOString(),
    comments:st.mine.map(function(c){ return {id:c.id, quote:c.quote, prefix:c.prefix, suffix:c.suffix, section:c.section, para:c.para, file:c.file,
      text:c.text, created:c.created, status:c.status, replies:c.replies}; })};
}
function download(){
  var go = function(){
    var blob = new Blob([JSON.stringify(exportJSON(), null, 1)], {type:"application/json"});
    var a = document.createElement("a"), nm = (st.name || "reviewer").toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/^-|-$/g, "") || "reviewer";
    a.href = URL.createObjectURL(blob); a.download = "comments-" + nm + "-" + ymd(new Date()) + ".json";
    document.body.appendChild(a); a.click(); a.remove();
    $("#saved").textContent = st.mine.length + " comment(s) downloaded: please email the file back";
  };
  if(!st.name) askName(go); else go();
}
$("#b-down").addEventListener("click", download);
$("#b-print").addEventListener("click", function(){
  var pv = $("#printview");
  pv.innerHTML = "<h1>Comments on " + esc(D.title) + "</h1><p>" + esc(st.name ? "Reviewer: " + st.name : "") + "</p>" +
    all().map(function(o){ var c = o.c, q = o.me ? c.quote : (c.rs >= 0 ? TEXT.slice(c.rs, c.re) : "");
      return "<div class='pc'><b>" + esc(o.me ? (st.name || "you") : (c.author || "author")) + "</b> " + esc(dateOf(c.created)) + (c.status === "resolved" ? " (resolved)" : "") +
        (o.me && c.section ? " · section " + esc(c.section) : "") + (q ? "<div class='q'>“" + esc(q) + "”</div>" : "") + "<div>" + esc(c.text) + "</div>" +
        (c.replies || []).map(function(r){ return "<div>↳ <b>" + esc(r.author) + "</b>: " + esc(r.text) + "</div>"; }).join("") + "</div>"; }).join("");
  document.body.classList.add("pc");
  var done = function(){ document.body.classList.remove("pc"); window.removeEventListener("afterprint", done); };
  window.addEventListener("afterprint", done); window.print(); setTimeout(done, 2000);
});
var pdfText = document.getElementById("rv-pdf").textContent.trim();
if(pdfText){
  $("#b-pdf").hidden = false;
  $("#b-pdf").addEventListener("click", function(){
    var bin = atob(pdfText), arr = new Uint8Array(bin.length);
    for(var i = 0; i < bin.length; i++) arr[i] = bin.charCodeAt(i);
    var url = URL.createObjectURL(new Blob([arr], {type:"application/pdf"}));
    if(!window.open(url, "_blank")){ var a = document.createElement("a"); a.href = url; a.download = "typeset.pdf"; document.body.appendChild(a); a.click(); a.remove(); }
  });
}
load(); render();
window.__rv = {D:D, TEXT:TEXT, st:st, addComment:addComment, exportJSON:exportJSON, curSel:curSel, offsetOf:offsetOf};
})();
</script></body></html>"""


def rv_slug(s, default="project"):
    return re.sub(r"[^A-Za-z0-9]+", "-", str(s)).strip("-").lower()[:40] or default


def rv_tex_files():
    out = []
    for p in sorted(ROOT.rglob("*.tex")):
        rel = p.relative_to(ROOT)
        if BUILD_DIR in rel.parts or any(x.startswith(".") for x in rel.parts):
            continue
        out.append(str(rel))
    return out


def rv_pdf_path():
    return ROOT / BUILD_DIR / (Path(MAIN).stem + ".pdf")


def rv_info(rel):
    """What the Share dialog needs to know: files, PDF size, how many comments could be shown."""
    try:
        view = ann_view(rel) if rel else []
    except (ValueError, OSError):
        view = []
    pdf = rv_pdf_path()
    ctx_title = ""
    try:
        ctx_title = RvCtx(ROOT, MAIN).title
    except OSError:
        pass
    opened = [a for a in view if a.get("status") != "resolved" and a.get("kind") != "review"]
    return {"files": rv_tex_files(), "current": rel, "pdf": pdf.stat().st_size if pdf.exists() else None, "pdf_max": RV_PDF_MAX,
            "title": ctx_title or ROOT.name, "project": ROOT.name,
            "comments": {"open": len(opened), "ticked": sum(1 for a in view if a.get("share") and a.get("kind") != "review")}}


def rv_pick_comments(doc, rels, mode):
    """The author's comments to show the reader (read-only), with their place in the rendered text."""
    out = []
    if mode not in ("ticked", "all"):
        return out
    for fi, rel in enumerate(rels):
        text = (ROOT / rel).read_text(encoding="utf-8", errors="replace")
        to_cp, _ = _ann_conv(text)
        for a in ann_view(rel, text):
            if a.get("kind") == "review":                       # a reviewer's comment is not the author's: never shown to the next reader
                continue
            if mode == "ticked" and not a.get("share"):
                continue
            if mode == "all" and a.get("status") == "resolved":
                continue
            r = doc.to_rendered(fi, to_cp(_ann_int(a.get("start"))), to_cp(_ann_int(a.get("end")))) if a["_anchor"] != "detached" else None
            out.append({"id": str(a["id"]), "author": str(a.get("author") or "the author")[:60], "kind": str(a.get("kind") or "info"),
                        "status": str(a.get("status") or "open"), "text": str(a.get("text") or ""), "created": str(a.get("created") or ""),
                        "replies": [{"author": str(r_.get("author", "")), "text": str(r_.get("text", "")), "created": str(r_.get("created", ""))}
                                    for r_ in (a.get("replies") if isinstance(a.get("replies"), list) else []) if isinstance(r_, dict)],
                        "rs": r[0] if r else -1, "re": r[1] if r else -1})
    return out


def rv_page(doc, rels, title, message, comments, pdf_b64, reviewer=""):
    secs = [{"start": s["start"], "label": ((s["label"] + " ") if s["label"] else "") + doc.text[s["start"]:s["start"] + max(s["title_len"], 0)].strip()}
            for s in doc.sections]
    data = {"title": title, "project": ROOT.name, "file": rels[0], "files": rels, "source_hash": doc.regions[0]["hash"] if doc.regions else "",
            "source_hashes": {r["rel"]: r["hash"] for r in doc.regions}, "hash": hashlib.sha256(doc.text.encode("utf-8")).hexdigest()[:16],
            "generated": time.strftime("%Y-%m-%dT%H:%M:%S"), "regions": [{"rel": r["rel"], "start": r["start"], "end": r["end"]} for r in doc.regions],
            "sections": secs, "blocks": doc.blocks, "comments": comments, "reviewer": reviewer}
    msg = ("<div class='msg'>" + html.escape(message.strip(), quote=False) + "</div>") if message.strip() else ""
    who = (f"<div class='note'>Review copy for {html.escape(reviewer, quote=False)}</div>") if reviewer.strip() else ""
    vals = {"TITLE": html.escape(title, quote=False), "MESSAGE": who + msg, "DOC": doc.html,
            "REFS": doc.refs_html if doc.refs_html else "<p class='hint'>No references were cited in the text shown.</p>",
            "DATA": json.dumps(data, ensure_ascii=False).replace("<", "\\u003c"), "PDF": pdf_b64}   # < only occurs inside strings: no </script> or <!--<script> can end the block
    return re.sub(r"__(TITLE|MESSAGE|DOC|REFS|DATA|PDF)__", lambda m: vals[m.group(1)], RV_PAGE)


def rv_share(body):
    """Write ONE self-contained HTML review copy of the chapter to build/review/ (no request of any kind)."""
    files = [f for f in (body.get("files") or []) if isinstance(f, str) and f]
    if not files:
        files = [body.get("file") or MAIN]
    for f in files:
        try:
            if safe(f).suffix.lower() != ".tex":
                raise ValueError("only .tex files can be shared")
        except ValueError as exc:
            raise AnnError(str(exc))
        if not (ROOT / f).exists():
            raise AnnError(f"{f} does not exist")
    mode = body.get("include", "none")
    if mode not in ("none", "ticked", "all"):
        raise AnnError("include must be none, ticked or all")
    doc = rv_render(ROOT, files, MAIN)
    comments = rv_pick_comments(doc, files, mode)
    warnings, pdf_b64 = [], ""
    if body.get("pdf"):
        pdf = rv_pdf_path()
        if not pdf.exists():
            warnings.append("No typeset PDF in build/ yet (compile first): the file was made without it.")
        elif pdf.stat().st_size > RV_PDF_MAX:
            warnings.append(f"The PDF is {pdf.stat().st_size / 1048576:.1f} MB, over the {RV_PDF_MAX // 1048576} MB limit: the file was made without it.")
        else:
            pdf_b64 = base64.b64encode(pdf.read_bytes()).decode("ascii")
    title = (doc.title or ROOT.name)
    page = rv_page(doc, files, title, str(body.get("message") or "")[:4000], comments, pdf_b64, str(body.get("reviewer") or "")[:60])
    name = f"review-{rv_slug(ROOT.name)}-{time.strftime('%Y%m%d')}.html"
    out = ROOT / BUILD_DIR / "review"
    out.mkdir(parents=True, exist_ok=True)
    replaced = (out / name).exists()
    tmp = out / (name + ".tmp")
    tmp.write_text(page, encoding="utf-8")
    os.replace(tmp, out / name)
    if doc.unresolved:
        warnings.append(f"{len(doc.unresolved)} citation key(s) or reference(s) could not be resolved and show as the key or '??': "
                        + ", ".join(sorted(doc.unresolved)[:6]))
    leaks = len(re.findall(r"[\\{}]", doc.text))
    if leaks:
        warnings.append(f"{leaks} stray backslash/brace character(s) remain in the reading text (unusual LaTeX the converter did not understand).")
    return {"ok": True, "name": name, "path": f"{BUILD_DIR}/review/{name}", "abs": str(out / name), "bytes": len(page.encode("utf-8")),
            "chars": len(doc.text), "files": files, "comments": len(comments), "pdf": bool(pdf_b64), "replaced": replaced,
            "references": doc.n_refs, "warnings": warnings}


# -- importing what the reader wrote ----------------------------------------------------------------------------
def rv_parse_review(text):
    """The first JSON object in `text` that is a texpad review-comments file (text around it is ignored)."""
    dec, i = json.JSONDecoder(), 0
    while i < len(text):
        j = text.find("{", i)
        if j < 0:
            break
        try:
            obj, end = dec.raw_decode(text, j)
        except ValueError:
            i = j + 1
            continue
        if isinstance(obj, dict) and obj.get("format") == RV_FORMAT:
            return obj
        i = j + 1
    raise AnnError(f"this is not a texpad review-comments file (no JSON with \"format\": \"{RV_FORMAT}\")")


def rv_locate(doc, quote, prefix, suffix, para=None):
    """Where the reader's quote is in this rendering: prefix+quote+suffix, then each half, then the quote alone.
    With several hits the one in the reader's paragraph wins. -> (start, end) rendered, or None."""
    if not quote:
        return None
    T = doc.text
    for pre, suf in ((prefix, suffix), (prefix, ""), ("", suffix), ("", "")):
        needle = pre + quote + suf
        hits, i = [], T.find(needle)
        while i >= 0:
            hits.append(i)
            i = T.find(needle, i + 1)
        if hits:
            if len(hits) > 1 and isinstance(para, int):
                same = [h for h in hits if bisect.bisect_right(doc.blocks, h + len(pre)) == para]
                hits = same or hits
            a = hits[0] + len(pre)
            return a, a + len(quote)
    return None


def rv_import(body):
    """Turn the reader's comment files into ordinary comments (kind 'review') in .texpad-annotations.json."""
    texts = [t for t in (body.get("texts") or []) if isinstance(t, str) and t.strip()]
    if not texts:
        raise AnnError("nothing to import: choose a comments file or paste its contents")
    default_rel = body.get("file") or ""
    summary = {"imported": 0, "detached": 0, "skipped": 0, "problems": [], "details": [], "files": {}}
    docs, now = {}, time.strftime("%Y-%m-%dT%H:%M:%S")
    with ANN_LOCK:
        data = _ann_load(strict=True)
        for text in texts:
            try:
                review = rv_parse_review(text)
            except AnnError as exc:
                summary["problems"].append(str(exc))
                continue
            reviewer = str(review.get("reviewer") or "reviewer").strip()[:60] or "reviewer"
            for c in review.get("comments") or []:
                if not isinstance(c, dict) or not str(c.get("text") or "").strip():
                    summary["skipped"] += 1
                    summary["problems"].append("a comment without text was skipped")
                    continue
                rel = str(c.get("file") or review.get("file") or default_rel)
                try:
                    safe(rel)
                    src = (ROOT / rel).read_text(encoding="utf-8", errors="replace")
                except (ValueError, OSError):
                    summary["skipped"] += 1
                    summary["problems"].append(f"{rel or '(no file)'}: not a file of this project")
                    continue
                lst = _ann_list(data, rel)
                quote, prefix, suffix = str(c.get("quote") or ""), str(c.get("prefix") or ""), str(c.get("suffix") or "")
                created = str(c.get("created") or now)
                if any(isinstance(x.get("review"), dict) and x.get("author") == reviewer and x.get("created") == created
                       and x["review"].get("quote") == quote for x in lst):
                    summary["skipped"] += 1
                    summary["details"].append(f"duplicate from {reviewer} ({created[:16]}): skipped")
                    continue
                if rel not in docs:
                    docs[rel] = rv_render(ROOT, [rel], MAIN)
                doc = docs[rel]
                para = c.get("para") if isinstance(c.get("para"), int) else None
                hit = rv_locate(doc, quote, prefix, suffix, para)
                sp = doc.span(*hit) if hit else None
                replies = [{"author": str(r.get("author") or reviewer)[:60], "text": str(r.get("text") or ""), "created": str(r.get("created") or "")}
                           for r in (c.get("replies") if isinstance(c.get("replies"), list) else []) if isinstance(r, dict) and str(r.get("text") or "").strip()]
                cid = str(c.get("id") or "")
                used = {str(x.get("id")) for x in lst}
                if not re.fullmatch(r"r-[A-Za-z0-9_-]{3,40}", cid) or cid in used:
                    cid = "r-" + hashlib.sha1(f"{reviewer}|{created}|{quote}".encode("utf-8")).hexdigest()[:8]
                    while cid in used:
                        cid += "x"
                a = {"id": cid, "start": 0, "end": 0, "quote": quote, "prefix": prefix, "suffix": suffix, "kind": "review",
                     "status": "resolved" if c.get("status") == "resolved" else "open", "author": reviewer, "created": created,
                     "text": str(c.get("text")).strip()[:20000], "replies": replies,
                     "review": {"quote": quote, "section": str(c.get("section") or ""), "para": para, "file": rel,
                                "source_hash": str(review.get("source_hash") or ""), "imported": now}}
                if sp:
                    ann_refresh(a, src, sp[1], sp[2])
                else:
                    a["detached"] = True                  # its text was not found: kept, with the reader's quote
                    a["review"]["unmatched"] = True
                    summary["detached"] += 1
                lst.append(a)
                data[rel] = lst
                summary["imported"] += 1
                summary["files"][rel] = summary["files"].get(rel, 0) + 1
                if review.get("source_hash") and doc.regions and review["source_hash"] != doc.regions[0]["hash"]:
                    summary["details"].append(f"{rel} changed since the review copy was made: comments are placed by their quoted text")
                if not sp:
                    summary["details"].append(f"not found in {rel}: “{quote[:50]}{'…' if len(quote) > 50 else ''}” ({reviewer}) is kept as detached")
        if summary["imported"]:
            _ann_save(data)
    summary["details"] = list(dict.fromkeys(summary["details"]))
    return summary


# --------------------------------------------------------------------------
#  Cross-review -- compare two candidate versions of ONE file against a common
#  baseline and merge them hunk by hunk. It only SELECTS between versions that
#  already exist on disk: it never writes or rewrites thesis text, and it calls
#  no model, API or CLI of any kind (the only subprocess is a read-only
#  `git show`). Hand-off to a reviewer is files and the clipboard.
#
#  Diffing, colour classification and the green check are a port of the
#  duel-test judge (judge_green.py): word-level hunks against the baseline,
#  each classified by the colour of the baseline text it touches.
# --------------------------------------------------------------------------
XR_TOKEN = re.compile(r"\s+|\w+|[^\w\s]", re.UNICODE)
XR_CITE = re.compile(r"\\[a-zA-Z]*cite[a-zA-Z]*\*?(?:\[[^\]]*\]){0,2}\{([^}]*)\}")
XR_ASTRAL = re.compile("[\U00010000-\U0010ffff]")
XR_REF = re.compile(r"^[A-Za-z0-9_][A-Za-z0-9._/@^~-]*$")
# Colours of the marks: g green = done and frozen, b blue = the author must decide here (not frozen),
# r red = to do, y yellow = revise (and, after a merge, "changed by a tool, waiting for review").
XR_COLOURS = ("g", "b", "y", "r", "-", "edge")
XR_RANK = {"g": 6, "b": 5, "r": 4, "y": 3, "edge": 2, "-": 1}

XR_PROMPT = """You and another model were given the same editing task, each in its own separate
copy of this LaTeX project. The other model's edits are in `_peer/changes.diff`
(a unified diff against the common starting point). `_peer/` is a read-only
reference: do not edit anything in it.

File under review: __FILE__
Candidates: __CANDIDATES__

The author colour-codes the text in `.texpad-marks.json`
({"<file>": [{"start": ..., "end": ..., "color": ...}]}, character offsets into
the baseline file):
  green    = done and frozen. Never change green text: not a typo, not a comma, not
             a line break. This holds for your own edits and for what you recommend.
  yellow   = to revise.     red = to do.     unmarked = free to edit.

Round 2 task: review the other model's changes. Do NOT edit any thesis file in
this round, and do not write replacement prose: the author writes the thesis and
only chooses between versions that already exist. Report, per hunk, with file
and line:

1. Colour: is the changed text green, yellow, red or unmarked? If a hunk (yours
   or theirs) changes green text, say so first.
2. Meaning: does the edit change the claim, a number, a hedge, or a citation key
   (\\cite{...})? Quote the before/after.
3. LaTeX: anything that would break compilation or change formatting.
4. Compared with your own edit to the same passage: which is better, and why in
   one sentence. If theirs is better, say so plainly.
5. Anything you changed that they did not, or the reverse.
6. References: if your review or either edit suggests a reference (a \\todo{...} asking
   for one, or a \\cite key that is not yet in `references.bib`), go and find a real
   one that fits that specific claim. The other model is asked to do the same, so do
   not assume it will. Check `references.bib` first. If it is not there, search by
   title and author names only, never pasting thesis text into a search. Before you
   propose it: confirm the paper exists (a DOI or the publisher's page), confirm that
   its abstract or text supports the specific claim and not just the topic, and give
   the BibTeX entry. If you cannot verify one of these, say so plainly. Never invent a
   reference and never complete one from memory.

Finish with ONE JSON array (text before it is fine, text inside it is not). Use
BASELINE line numbers: the L numbers in the hunk lists that follow as separate
messages, about 40 hunks each. One object per passage or per hunk; a passage-level
entry applies to every hunk inside its line range. Answer each hunk-list message
with its own array:

[{"from_line": 45, "to_line": 46, "pick": "a", "why": "one sentence", "flag": "none"}]

  pick   "a" or "b" = take that candidate's version; "baseline" = keep the baseline;
         "merge" = a mix of both (say which parts in why; do not write new wording);
         "check" = the author has to decide.
  flag   one of: meaning | citation | voice | layout | unverified | none

A hunk that changes green text is always "baseline" unless the author explicitly
overrides it.
"""


class XRError(Exception):
    """A cross-review request that cannot be honoured; the message is shown to the author."""


def _xr_offsets(chunks):
    out, pos = [], 0
    for c in chunks:
        out.append(pos)
        pos += len(c)
    out.append(pos)
    return out


def xr_diff_blocks(base, new):
    """Changed blocks as (base_start, base_end, old_text, new_text); start == end is an insertion.
    Line diff first, then a word/punctuation/whitespace diff inside each changed run of lines."""
    bl, nl = base.splitlines(keepends=True), new.splitlines(keepends=True)
    boff = _xr_offsets(bl)
    out = []
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, bl, nl, autojunk=False).get_opcodes():
        if tag == "equal":
            continue
        bt = XR_TOKEN.findall("".join(bl[i1:i2]))
        nt = XR_TOKEN.findall("".join(nl[j1:j2]))
        bpos = _xr_offsets(bt)
        for t2, a1, a2, c1, c2 in difflib.SequenceMatcher(None, bt, nt, autojunk=False).get_opcodes():
            if t2 != "equal":
                out.append((boff[i1] + bpos[a1], boff[i1] + bpos[a2], "".join(bt[a1:a2]), "".join(nt[c1:c2])))
    return out


def xr_colour_map(n, marks):
    """Per-character colour of the baseline: g, r, y or '-' (green wins over red over yellow)."""
    prio = {"g": 4, "b": 3, "r": 2, "y": 1}                # green always wins, then blue
    col = ["-"] * n
    for m in marks:
        c = m["color"]
        for i in range(max(int(m["start"]), 0), min(int(m["end"]), n)):
            if col[i] == "-" or prio.get(c, 0) > prio.get(col[i], 0):
                col[i] = c
    return col


def xr_classify(col, b0, b1):
    """Colour of the baseline text a hunk touches. An insertion (b0 == b1) takes the colour
    around it, or 'edge' when it lands on the boundary between two colours."""
    n = len(col)
    if b0 == b1:
        left = col[b0 - 1] if b0 > 0 else "-"
        right = col[b0] if b0 < n else "-"
        return left if left == right else "edge"
    seen = set(col[b0:b1])
    for c in ("g", "b", "r", "y"):
        if c in seen:
            return c
    return "-"


def xr_cites(text):
    c = collections.Counter()
    for m in XR_CITE.finditer(text):
        for k in m.group(1).split(","):
            c[k.strip()] += 1
    return c


def xr_hunks(side, base, new, col, col_live=None):
    out = []
    for b0, b1, old, nw in xr_diff_blocks(base, new):
        c = xr_classify(col, b0, b1)
        out.append({"side": side, "b0": b0, "b1": b1, "old": old, "new": nw, "colour": c,
                    "live": xr_classify(col_live, b0, b1) if col_live is not None else c,
                    "ws": old.split() == nw.split()})
    return out


def xr_summary(base, new, marks, hunks):
    """Per-candidate numbers, same definitions as the judge: green spans hit by a content
    change are violated, by whitespace only are 'ws_only'; hunks counted per colour."""
    greens = [(int(m["start"]), int(m["end"])) for m in marks if m["color"] == "g"]
    violated = ws_only = 0
    for s, e in greens:
        hits = [h for h in hunks if (h["b0"] == h["b1"] and s < h["b0"] < e)
                or (h["b0"] != h["b1"] and h["b0"] < e and h["b1"] > s)]
        if not hits:
            continue
        if all(h["ws"] for h in hits):
            ws_only += 1
        else:
            violated += 1
    by = {c: 0 for c in XR_COLOURS}
    for h in hunks:
        by[h["colour"]] += 1
    cb, cn = xr_cites(base), xr_cites(new)
    if not hunks:
        verdict = "NO EDITS"
    elif violated == 0:
        verdict = "GREEN KEPT"
    else:
        verdict = f"GREEN VIOLATED in {violated} span(s)"
    return {"hunks": len(hunks), "by_colour": by, "green_total": len(greens),
            "green_kept": len(greens) - violated, "green_violated": violated,
            "green_ws_only": ws_only, "verdict": verdict,
            "cites_added": dict(cn - cb), "cites_removed": dict(cb - cn)}


# -- marks across a merge ----------------------------------------------------
# texpad keeps marks valid across an edit in the browser (adjustMarks in the page
# script below): diff old text against new by common prefix and common suffix,
# then move each endpoint through that one edit. xr_adjust_marks is the same rule
# in Python, and a merge applies its hunks one at a time through it, last hunk
# first, so every mark goes through exactly the mapping typing the same edit
# would have given it.
def _xr_prefix(a, b, limit):
    lo, hi = 0, limit
    while lo < hi:                      # prefix equality is monotone: binary search on slices
        mid = (lo + hi + 1) // 2
        if a[:mid] == b[:mid]:
            lo = mid
        else:
            hi = mid - 1
    return lo


def _xr_suffix(a, b, limit):
    lo, hi = 0, limit
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if a[len(a) - mid:] == b[len(b) - mid:]:
            lo = mid
        else:
            hi = mid - 1
    return lo


def xr_adjust_marks(marks, old_t, new_t):
    if not marks or old_t == new_t:
        return marks
    common = min(len(old_t), len(new_t))
    pre = _xr_prefix(old_t, new_t, common)
    suf = _xr_suffix(old_t, new_t, common - pre)
    old_mid_end, new_mid_end, delta = len(old_t) - suf, len(new_t) - suf, len(new_t) - len(old_t)

    def mp(p, is_start):
        if p <= pre:
            return p
        if p >= old_mid_end:
            return p + delta
        return new_mid_end if is_start else pre

    out = [{"start": mp(m["start"], True), "end": mp(m["end"], False), "color": m["color"]} for m in marks]
    return [m for m in out if m["end"] > m["start"]]


def _xr_u16(text):
    """Cumulative UTF-16 offsets per code point, or None for BMP-only text. The page counts
    characters in UTF-16 units (that is what the marks file stores), Python in code points."""
    if not XR_ASTRAL.search(text):
        return None
    u = [0]
    for ch in text:
        u.append(u[-1] + (2 if ord(ch) > 0xFFFF else 1))
    return u


def xr_marks_in(text, marks):
    """Stored marks -> code-point offsets, sorted; malformed entries are dropped."""
    u = _xr_u16(text)
    out = []
    for m in marks or []:
        try:
            s, e, c = int(m["start"]), int(m["end"]), str(m["color"])
        except Exception:                                       # noqa: BLE001
            continue
        if u is not None:
            s, e = bisect.bisect_right(u, s) - 1, bisect.bisect_right(u, e) - 1
        out.append({"start": s, "end": e, "color": c})
    return sorted(out, key=lambda m: m["start"])


def xr_marks_out(text, marks):
    u = _xr_u16(text)
    if u is None:
        return marks
    return [{"start": u[m["start"]], "end": u[m["end"]], "color": m["color"]} for m in marks]


def xr_marks_problems(text, marks, overlap=True):
    """Why these marks would not be valid for text ([] = consistent)."""
    bad, prev_end = [], 0
    for i, m in enumerate(marks):
        if not 0 <= m["start"] < m["end"] <= len(text):
            bad.append(f"mark {i} [{m['start']},{m['end']}) is outside 0..{len(text)}")
        elif overlap and m["start"] < prev_end:
            bad.append(f"mark {i} overlaps the one before it")
        prev_end = max(prev_end, m["end"])
    return bad


# -- sources -----------------------------------------------------------------
def _xr_dir(s):
    s = (s or "").strip()
    if not s:
        return None
    p = Path(s).expanduser()
    p = (p if p.is_absolute() else ROOT / p).resolve()
    if not p.is_dir():
        raise XRError(f"not a folder: {s}")
    return p


def _xr_git_show(folder, ref, path):
    """Text of path at ref in folder's repository, or None. Read-only."""
    if not XR_REF.match(ref):
        raise XRError(f"not a usable git ref: {ref!r}")
    try:
        r = subprocess.run(["git", "-C", str(folder), "show", f"{ref}:{path}"],
                           capture_output=True, timeout=20, text=True, encoding="utf-8")
    except Exception as exc:                                    # noqa: BLE001
        raise XRError(f"git failed in {folder}: {exc}")
    return r.stdout if r.returncode == 0 else None


def xr_load_baseline(spec, rel):
    spec = spec or {}
    if spec.get("mode") == "current":
        return {"text": safe(rel).read_text(encoding="utf-8"), "marks": marks_for(rel),
                "label": "current file", "note": ""}
    folder = _xr_dir(spec.get("folder")) or ROOT
    ref = (spec.get("ref") or "baseline").strip()
    text = _xr_git_show(folder, ref, rel)
    if text is None:
        raise XRError(f"{rel} not found at git ref '{ref}' in {folder}")
    raw, note, marks = _xr_git_show(folder, ref, MARKS_FILE), "", []
    if raw is None:
        note = f"no {MARKS_FILE} at '{ref}': every hunk shows as unmarked"
    else:
        try:
            marks = json.loads(raw).get(rel, [])
        except Exception:                                       # noqa: BLE001
            note = f"{MARKS_FILE} at '{ref}' is unreadable: every hunk shows as unmarked"
    return {"text": text, "marks": marks, "label": f"git '{ref}' in {folder}", "note": note}


def xr_load_candidate(folder, rel):
    p = (folder / rel).resolve()
    if folder not in p.parents or not p.is_file():
        raise XRError(f"{rel} not found in {folder}")
    return p.read_text(encoding="utf-8")


def _xr_best(colours):
    return max(colours, key=lambda c: XR_RANK[c]) if colours else None


def _xr_render(base, c0, c1, hunks):
    """base[c0:c1] with the hunks (all inside that range) applied."""
    out, pos = [], c0
    for h in sorted(hunks, key=lambda h: (h["b0"], h["b1"])):
        out += [base[pos:h["b0"]], h["new"]]
        pos = h["b1"]
    out.append(base[pos:c1])
    return "".join(out)


def _xr_bal(t):
    """(net braces, net \\begin minus \\end) with comments and escaped braces ignored. Word-level
    hunks can be coupled -- `\\todo{` in one, its `}` in another -- and LaTeX stops on either."""
    br = env = 0
    for line in t.split("\n"):
        line = re.sub(r"(?<!\\)%.*", "", line)
        br += len(re.findall(r"(?<!\\)\{", line)) - len(re.findall(r"(?<!\\)\}", line))
        env += len(re.findall(r"\\begin\{", line)) - len(re.findall(r"\\end\{", line))
    return br, env


# -- recommendations -----------------------------------------------------------
# Two sources, always shown side by side, labelled, and never merged silently:
#   rules   deterministic checks built into texpad (no model): flags per candidate and, only where
#           the flags make it clear, a suggested pick with the reason. "clear" picks are the ones
#           Apply suggestions may use; "lean" picks only when the author asks for them.
#   import  what a reviewer the author ran in their own session answered (a JSON array, or a
#           Markdown passage table), mapped onto hunks by BASELINE line numbers.
# A suggestion only ever pre-selects between versions that already exist; it never writes text.
XR_INFLATED = re.compile(r"\b(pivotal|crucial(?:ly)?|landscape|tapestry|underscor(?:e|es|ed|ing)|delv(?:e|es|ed|ing)"
                         r"|foster(?:s|ed|ing)?|leverag(?:e|es|ed|ing)|robust(?:ness)?|multifaceted)\b", re.I)
XR_INTENSIFIER = re.compile(r"\b(fundamental(?:ly)?|inherent(?:ly)?|critical(?:ly)?|most)\b", re.I)
XR_NOT_JUST = re.compile(r"\bnot just\b[^.]{0,80}?\bbut\b", re.I)
XR_HIGHLIGHTING = re.compile(r",\s+highlighting\b", re.I)
XR_STRIP = re.compile(r"\\(?:[a-zA-Z]*cite[a-zA-Z]*\*?|ref|eqref|cref|Cref|label|autoref|input|include|includegraphics)"
                      r"(?:\[[^\]]*\]){0,2}\{[^}]*\}|\\todo(?:\[[^\]]*\])?\{[^{}]*\}")
XR_NUMBER = re.compile(r"\\(?:SIrange|SI|num|qty|ang|si)\w*(?:\[[^\]]*\])?\{[^}]*\}(?:\{[^}]*\})*|\d+(?:[.,]\d+)?")
XR_SEV_NEG = ("block", "avoid", "style", "verify")     # flags that count against a candidate
XR_SEV_FIRM = ("block", "avoid")                       # ... and the ones that make a pick "clear"
XR_NAMES = {"g": "green", "b": "blue", "y": "yellow", "r": "red", "-": "unmarked", "edge": "edge"}


def xr_bib_keys(root=None):
    """Keys defined in a project's top-level .bib files (default: this project), or None when there is none."""
    keys, found = set(), False
    for p in sorted((root or ROOT).glob("*.bib")):
        try:
            keys |= set(re.findall(r"^\s*@\w+\s*\{\s*([^,\s]+)\s*,", p.read_text(encoding="utf-8", errors="replace"), re.M))
            found = True
        except OSError:
            pass
    return keys if found else None


def _xr_numbers(t):
    return collections.Counter(re.sub(r"\s+", "", x) for x in XR_NUMBER.findall(XR_STRIP.sub(" ", t)))


def _xr_list(items, limit=4):
    items = [str(i) for i in items]
    return ", ".join(items[:limit]) + (f" (+{len(items) - limit} more)" if len(items) > limit else "")


def xr_flags(ro, rn, k, s, bib, file_keys, bib_c=None):
    """Deterministic flags for what candidate k does to the lines it touches. ro = those lines in
    the baseline, rn = the same lines with only this candidate's hunks applied. bib = keys of this
    project's .bib files, bib_c = keys of the candidate's own .bib files. Each flag is {id, sev, text};
    sev decides how much the flag counts (see XR_SEV_NEG / XR_SEV_FIRM)."""
    out = []

    def add(fid, sev, text):
        out.append({"id": fid, "sev": sev, "text": text})

    if s["blocked_" + k]:
        add("green", "block", "touches green text (frozen)")
    if any(h["colour"] == "b" for h in s["hunks"] if h["side"] == k):
        add("decide", "note", "touches blue text: you marked this to decide yourself")
    if all(h["ws"] for h in s["hunks"] if h["side"] == k):
        add("whitespace", "low", "whitespace-only change: nothing to review")
    cb, cn = xr_cites(ro), xr_cites(rn)
    new = sorted(cn - cb)
    missing = [x for x in new if bib is not None and x not in bib]
    own = [x for x in missing if bib_c and x in bib_c]           # only in the candidate's own .bib
    undefined = [x for x in missing if x not in own]
    fresh = [x for x in new if x not in missing and x not in file_keys]
    gone = sorted(cb - cn)
    if undefined:
        add("undefined_cite", "avoid", f"adds citation key {_xr_list(undefined)}, which is not in references.bib (undefined)")
    if own:
        add("own_bib_cite", "verify", f"cites {_xr_list(own)}, which exists only in {k.upper()}'s own references.bib: "
            "that bib entry has to come along, and the paper has to support the claim")
    if fresh:
        add("new_cite", "verify", f"cites {_xr_list(fresh)}, which this file never cited before: check the paper supports the claim")
    if gone:
        add("removed_cite", "verify", f"removes citation key {_xr_list(gone)}")
    no, nn = _xr_numbers(ro), _xr_numbers(rn)
    if no != nn:
        parts = [p for p in (("removes " + _xr_list(sorted((no - nn).elements()))) if no - nn else "",
                             ("adds " + _xr_list(sorted((nn - no).elements()))) if nn - no else "") if p]
        add("number", "verify", f"changes a number or unit ({'; '.join(parts)}): verify against the source")
    t0, t1 = len(re.findall(r"\\todo\b", ro)), len(re.findall(r"\\todo\b", rn))
    if t1 > t0:
        add("todo_added", "note", "adds a \\todo: an open question the author has to resolve")
    elif t1 < t0:
        add("todo_removed", "verify", "removes a \\todo: an open question disappears")
    words = lambda t: collections.Counter(w.lower() for w in XR_INFLATED.findall(t) + XR_INTENSIFIER.findall(t))
    inflated = sorted(set((words(rn) - words(ro)).elements()))
    if len(XR_NOT_JUST.findall(rn)) > len(XR_NOT_JUST.findall(ro)):
        inflated.append("not just ... but")
    if len(XR_HIGHLIGHTING.findall(rn)) > len(XR_HIGHLIGHTING.findall(ro)):
        inflated.append(", highlighting ...")
    if inflated:
        add("inflated", "style", f"adds wording the baseline lacked that reads inflated: {_xr_list(inflated)}")
    if s[k + "_bal"] and s[k + "_bal"] != [0, 0]:
        add("unbalanced", "pair", "adds or removes a brace or \\begin/\\end without its partner hunk: take it together with that partner")
    return out


def xr_rule_suggest(s):
    """Rule-based suggestion for one site: {pick, strength, why, rule}. pick is 'a', 'b', 'baseline'
    or None; strength is 'clear', 'lean' or 'none'. Never guesses quality: when the rules cannot tell
    it says so."""
    sides = [k for k in "ab" if s[k + "_n"]]
    fl = {k: s["flags_" + k] for k in sides}
    neg = {k: [f for f in fl[k] if f["sev"] in XR_SEV_NEG] for k in sides}
    firm = {k: [f for f in fl[k] if f["sev"] in XR_SEV_FIRM] for k in sides}
    pair = {k: [f for f in fl[k] if f["sev"] == "pair"] for k in sides}
    why = lambda fs: "; ".join(f["text"] for f in fs)

    def out(pick, strength, text, rule):
        return {"pick": pick, "strength": strength, "why": text, "rule": rule, "judgement": pick is None}

    if all(any(f["id"] == "green" for f in fl[k]) for k in sides):
        return out("baseline", "clear", "touches green text, which is frozen: keep baseline", "green")
    if any(f["id"] == "decide" for k in sides for f in fl[k]):
        return out(None, "none", "touches blue text: you marked this to decide yourself, so no pick is suggested", "decide")
    if s["ws"]:
        return out("baseline", "clear", "whitespace-only: nothing to review, and taking it only adds yellow marks", "whitespace")
    if len(sides) == 2 and s["agree"] in ("same", "same_ws"):
        if firm["a"] and firm["b"]:
            return out("baseline", "clear", "A and B agree, but " + why(firm["a"]), "flag")
        issues = neg["a"] + neg["b"] + pair["a"] + pair["b"]
        if issues:
            return out(None, "none", "A and B made the identical change, but " + why(issues[:2]), "agreement")
        return out("a", "clear", "A and B made the identical change (agreement) and the rules found nothing to flag", "agreement")
    if len(sides) == 1:
        k = sides[0]
        if firm[k]:
            return out("baseline", "clear", f"only {k.upper()} changed this: {why(firm[k])}. Do not take it", "flag")
        if pair[k]:
            return out(None, "none", f"only {k.upper()} changed this: {why(pair[k])}", "pair")
        if neg[k]:
            return out("baseline", "lean", f"only {k.upper()} changed this and it is flagged ({why(neg[k])}): keep baseline until you have checked", "flag")
        return out(k, "lean", f"only {k.upper()} changed this and the rules found nothing to flag (they cannot judge the wording)", "single")
    if pair["a"] or pair["b"]:
        return out(None, "none", "one side adds or removes a brace or environment without its partner: take it together with the partner hunk", "pair")
    if firm["a"] and firm["b"]:
        return out("baseline", "clear", f"both are flagged: A: {why(firm['a'])}; B: {why(firm['b'])}", "flag")
    for k, o in (("a", "b"), ("b", "a")):
        if neg[k] and not neg[o]:
            return out(o, "clear" if firm[k] else "lean",
                       f"{k.upper()} is flagged ({why(neg[k])}); {o.upper()} has no flags", "flag")
    if neg["a"] and neg["b"]:
        return out(None, "none", f"both are flagged, so the rules cannot separate them: A: {why(neg['a'])}; B: {why(neg['b'])}", "flag")
    return out(None, "none", "no rule-based suggestion: needs your judgement", "none")


# -- imported recommendations --------------------------------------------------
def _xr_cands_label(label, cands):
    """'claude' -> 'a' when candidate A's folder is called claude. cands = {side: folder path}."""
    t = re.sub(r"[^a-z0-9]+", "", str(label).lower())
    if t in ("a", "b") and t in cands:
        return t
    names = {k: re.sub(r"[^a-z0-9]+", "", Path(v).name.lower()) for k, v in cands.items()}
    hit = [k for k, n in names.items() if n == t] or [k for k, n in names.items() if t and t in n]
    return hit[0] if len(hit) == 1 else None


def _xr_pick(raw, cands):
    """A reviewer's pick (JSON field or table words) -> a | b | baseline | merge | check | None."""
    t = re.sub(r"[^a-z0-9]+", " ", str(raw).lower()).strip()
    if t in ("a", "b") and t in cands:
        return t
    if t in ("baseline", "base", "keep", "keep baseline", "keep base", "original", "keep original"):
        return "baseline"
    if t in ("merge", "mix", "combine"):
        return "merge"
    if t in ("check", "needs author check", "needs check", "author check", "unsure"):
        return "check"
    m = re.match(r"(?:take|use|prefer|keep|candidate)(?: candidate)? (\w+)$", t) or re.match(r"(\w+)$", t)
    return _xr_cands_label(m.group(1), cands) if m else None


def _xr_int(v):
    m = re.search(r"\d+", str(v))
    return int(m.group()) if m else None


def _xr_json_recs(text, cands):
    """Records in a JSON array (or loose objects) anywhere in text; text around them is ignored."""
    dec = json.JSONDecoder()
    for src in (text, re.sub(r",(\s*[\]}])", r"\1", text.replace("\u201c", '"').replace("\u201d", '"'))):
        raw, i = [], 0
        while i < len(src):
            if src[i] in "[{":
                try:
                    obj, end = dec.raw_decode(src, i)
                except ValueError:
                    i += 1
                    continue
                items = [x for x in (obj if isinstance(obj, list) else [obj]) if isinstance(x, dict) and "from_line" in x]
                if items:
                    raw += items
                    i = end
                    continue
            i += 1
        if raw:
            break
    recs, problems = [], []
    for n, r in enumerate(raw):
        lo, hi = _xr_int(r.get("from_line")), _xr_int(r.get("to_line", r.get("from_line")))
        pick = _xr_pick(r.get("pick", ""), cands)
        if lo is None or hi is None or pick is None:
            problems.append(f"entry {n + 1}: unusable from_line/to_line/pick ({r.get('from_line')}, {r.get('to_line')}, {r.get('pick')!r})")
            continue
        flag = r.get("flag", "none")
        recs.append({"passage": f"json {n + 1}", "lo": min(lo, hi), "hi": max(lo, hi), "pick": pick, "qualified": False,
                     "why": str(r.get("why", "")).strip()[:320], "flag": ",".join(map(str, flag)) if isinstance(flag, list) else str(flag)})
    return recs, problems


def _xr_cells(line):
    parts = re.split(r"(?<!\\)\|", line.strip())
    return [c.strip() for c in parts[1:-1]] if line.strip().endswith("|") else [c.strip() for c in parts[1:]]


def _xr_ranges(cell):
    """Baseline line ranges in a location cell: 'Chapter opening, L4–14 (red)' -> [(4, 14)];
    'L422–423, 443–444' -> [(422, 423), (443, 444)]."""
    m = re.search(r"\bL\d", cell)
    if not m:
        return []
    out = []
    for tok in re.split(r"[,;]|\band\b", cell[m.start():].split("(")[0]):
        t = re.match(r"\s*L?(\d+)(?:\s*[\u2013\u2014\u2212-]\s*L?(\d+))?\s*$", tok)
        if t:
            lo = int(t.group(1))
            out.append((lo, int(t.group(2) or lo)))
    return out


_XR_FLAG_WORDS = (("citation", "citation"), ("meaning", "meaning"), ("voice", "voice"), ("layout", "layout"), ("unverified", "unverified"))


def _xr_md_recs(text, cands):
    """Passage rows of Markdown tables with a location column (baseline line range) and a
    recommendation column (TAKE <label>, KEEP BASELINE, MERGE, NEEDS AUTHOR CHECK)."""
    recs, problems, lines, i = [], [], text.splitlines(), 0
    clean = lambda t: re.sub(r"\s+", " ", re.sub(r"[*`]", "", t)).strip()
    while i < len(lines) - 1:
        if not (lines[i].lstrip().startswith("|") and re.match(r"^\s*\|[\s:|-]+\|?\s*$", lines[i + 1])):
            i += 1
            continue
        head = [c.lower() for c in _xr_cells(lines[i])]
        col = lambda pat: next((n for n, c in enumerate(head) if re.search(pat, c)), None)
        c_loc, c_rec = col(r"location|passage|lines?\b|where"), col(r"recommend|verdict|decision")
        c_why, c_flag, c_id = col(r"assess|why|reason|rationale"), col(r"flag"), col(r"^(#|no\.?|id)$")
        j = i + 2
        while j < len(lines) and lines[j].lstrip().startswith("|"):
            if c_loc is not None and c_rec is not None:
                cells = _xr_cells(lines[j])
                if len(cells) > max(c_loc, c_rec):
                    pid = f"#{clean(cells[c_id])}" if c_id is not None and c_id < len(cells) else f"row {j + 1}"
                    pid += " " + clean(cells[c_loc]).split(",")[0][:40]
                    rng = _xr_ranges(clean(cells[c_loc]))
                    t = re.sub(r"^[\s*`_]+", "", cells[c_rec])
                    m = re.match(r"(?i)(?:(take|keep|use|prefer)\s+(\w+)|(merge)\b|(needs?\s+author\s+check|check)\b)", t)
                    pick = rest = None
                    if m:
                        rest = t[m.end():]
                        if m.group(3):
                            pick = "merge"
                        elif m.group(4):
                            pick = "check"
                        else:
                            pick = "baseline" if m.group(2).lower() == "baseline" else _xr_cands_label(m.group(2), cands)
                    if not rng:
                        problems.append(f"{pid}: no baseline line range (L<n>-<m>) in the location cell")
                    elif pick is None:
                        problems.append(f"{pid}: recommendation {clean(t)[:40]!r} not understood (labels must match a candidate folder name)")
                    else:
                        caveat = clean(rest.lstrip(" .,;:-\u2013\u2014")) if rest else ""
                        qualified = pick in ("a", "b", "baseline") and bool(re.sub(r"[\W_]+", "", caveat))
                        assess = clean(cells[c_why]) if c_why is not None and c_why < len(cells) else ""
                        fl = clean(cells[c_flag]).lower() if c_flag is not None and c_flag < len(cells) else "none"
                        flag = ",".join(v for w, v in _XR_FLAG_WORDS if w in fl) or "none"
                        for lo, hi in rng:
                            recs.append({"passage": pid, "lo": min(lo, hi), "hi": max(lo, hi), "pick": pick, "qualified": qualified,
                                         "why": ((caveat + " \u2014 ") if caveat else "") + assess[:300], "flag": flag})
            j += 1
        i = j
    return recs, problems


def xr_parse_import(text, cands):
    """All recommendations in a pasted reviewer reply -> (records, problems)."""
    r1, p1 = _xr_json_recs(text, cands)
    r2, p2 = _xr_md_recs(text, cands)
    return r1 + r2, p1 + p2


def xr_import(text, name, sites, cands):
    """Attach imported recommendations to the sites whose baseline lines they cover. Returns a
    report. A passage-level 'take A' at a hunk A did not change means A's version = baseline there."""
    recs, problems = xr_parse_import(text, cands)
    found, passages = set(), {}
    for r in recs:
        passages.setdefault(r["passage"], []).append(r)
        for s in sites:
            if r["lo"] <= s["line_end"] and r["hi"] >= s["line"]:
                eff = r["pick"] if r["pick"] not in ("a", "b") or s[r["pick"] + "_n"] else "baseline"
                s["imports"].append({"name": name, "pick": eff, "raw_pick": r["pick"], "clear": eff in ("a", "b", "baseline") and not r["qualified"],
                                     "caveat": r["qualified"], "why": r["why"], "flag": r["flag"], "lines": f"L{r['lo']}-{r['hi']}",
                                     "passage": r["passage"]})
                found.add(r["passage"])
    missing = [{"passage": p, "lines": ", ".join(f"L{r['lo']}-{r['hi']}" for r in rs)} for p, rs in passages.items() if p not in found]
    return {"name": name, "records": len(recs), "passages": len(passages), "found": len(found), "unmatched": missing,
            "problems": problems, "sites": sum(1 for s in sites if s["imports"])}


def xr_combine(s, include_lean):
    """One verdict from the two sources for a site: a pick only when the sources that have a pick agree.
    Disagreement is reported as 'conflict' and nothing is chosen; it is never averaged away."""
    rule, votes, soft = s["rule"], [], False
    if rule["rule"] == "decide":              # blue = the author decides here: nothing is pre-selected, from any source
        return {"pick": None, "status": "decide"}
    if rule["pick"]:
        if rule["strength"] == "clear" or include_lean:
            votes.append(("rules", rule["pick"]))
        else:
            soft = True
    for i in s["imports"]:
        if i["pick"] in ("a", "b", "baseline"):
            if i["clear"] or include_lean:
                votes.append(("import", i["pick"]))
            else:
                soft = True
    picks = {p for _, p in votes}
    if len(picks) == 1:
        srcs = {v[0] for v in votes}
        return {"pick": picks.pop(), "status": "agree" if len(srcs) > 1 else srcs.pop()}
    if len(picks) > 1:
        return {"pick": None, "status": "conflict"}
    if soft:
        return {"pick": None, "status": "lean"}
    if rule["judgement"] or any(i["pick"] in ("merge", "check") for i in s["imports"]):
        return {"pick": None, "status": "judgement"}
    return {"pick": None, "status": "none"}


def xr_sugg_counts(sites, key):
    c = {"a": 0, "b": 0, "baseline": 0, "judgement": 0, "conflict": 0, "lean": 0, "none": 0, "decide": 0}
    for s in sites:
        p = s[key]
        c[p["pick"] or p["status"]] += 1
    c["suggested"] = c["a"] + c["b"] + c["baseline"]
    return c


def xr_plan(req):
    """Apply suggestions: the choices to set. Never touches a hunk the author chose themselves, never
    selects a green-blocked side without that hunk's override, never decides between sources that
    disagree. Returns {choices: {id: 'a'|'b'|'base'}, applied, skipped}."""
    m = xr_build(req)
    lean = bool(req.get("include_lean"))
    user = {int(x) for x in req.get("user") or []}
    overrides = {int(x) for x in req.get("overrides") or []}
    choices, applied = {}, {"a": 0, "b": 0, "baseline": 0}
    skipped = {"user": 0, "green": 0, "conflict": 0, "judgement": 0, "lean": 0, "none": 0, "decide": 0}
    for s in m["sites"]:
        if s["id"] in user:
            skipped["user"] += 1
            continue
        p = s["plan_lean" if lean else "plan_clear"]
        if p["pick"] is None:
            skipped[p["status"]] += 1
        elif p["pick"] in ("a", "b") and s["blocked_" + p["pick"]] and s["id"] not in overrides:
            skipped["green"] += 1
        else:
            choices[str(s["id"])] = "base" if p["pick"] == "baseline" else p["pick"]
            applied[p["pick"]] += 1
    return {"choices": choices, "applied": applied, "skipped": skipped, "sig": m["sig"]}


def _xr_clip(t, n=110):
    t = t.replace("\n", "\u21b5")
    return t if len(t) <= n else t[:n - 1] + "\u2026"


def xr_hunk_chunks(m, size=40):
    """The hunk list for a reviewer, in chunks of about `size` hunks, in baseline line numbers."""
    sites = m["sites"]
    names = ", ".join(f"{k.upper()} = {Path(c['folder']).name}" for k, c in sorted(m["cands"].items()))
    out = []
    for i in range(0, len(sites), size):
        part, lines = sites[i:i + size], []
        for s in part:
            span = f"L{s['line']}" + (f"-{s['line_end']}" if s["line_end"] > s["line"] else "")
            cols = " | ".join(f"{k.upper()} \u00ab{_xr_clip(s[k])}\u00bb" if s[k] is not None else f"{k.upper()} =" for k in "ab" if k in m["cands"])
            flags = "; ".join(f"{k.upper()}: {f['id']}" for k in "ab" for f in s["flags_" + k] if f["sev"] != "note")
            lines.append(f"#{s['id']} {span} [{XR_NAMES[s['colour']]}] base \u00ab{_xr_clip(s['base'])}\u00bb | {cols}" + (f" | flags {flags}" if flags else ""))
        head = (f"Hunks #{part[0]['id']}-#{part[-1]['id']} of {len(sites) - 1} in {m['rel']}. Candidates: {names}. "
                "Baseline line numbers (L). Answer in the JSON format from the review prompt, using these line numbers.")
        out.append({"from": part[0]["id"], "to": part[-1]["id"], "count": len(part), "text": head + "\n\n" + "\n".join(lines)})
    return out


def _xr_para_unbalanced(t):
    """Start lines of the paragraphs (blank-line separated) whose braces do not balance. A brace opened in
    one paragraph and closed in a later one stops LaTeX ('Paragraph ended before ... was complete')
    even when the whole file balances."""
    out, pos = [], 0
    for m in list(re.finditer(r"\n[ \t]*\n", t)) + [None]:
        end = m.start() if m else len(t)
        if _xr_bal(t[pos:end])[0] != 0:
            out.append(t.count("\n", 0, pos) + 1)
        pos = m.end() if m else len(t)
    return out


def xr_build(req):
    """Everything the panel shows, recomputed from disk on every call (nothing is cached)."""
    rel = req.get("file", "")
    try:
        p_open = safe(rel)
    except ValueError as exc:
        raise XRError(str(exc))
    bl = xr_load_baseline(req.get("baseline"), rel)
    base = bl["text"]
    marks = xr_marks_in(base, bl["marks"])
    col = xr_colour_map(len(base), marks)

    # The open file's own marks matter when it is the baseline text but its marks have moved
    # on since the ref: those are the marks a merge into it must carry, and green there is
    # protected too.
    same_as_open = p_open.exists() and p_open.read_text(encoding="utf-8") == base
    marks_open = xr_marks_in(base, marks_for(rel)) if same_as_open else None
    col_live = xr_colour_map(len(base), marks_open) if marks_open is not None and marks_open != marks else None

    cands, hunks = {}, []
    for side in ("a", "b"):
        folder = _xr_dir(req.get(side))
        if folder is None:
            continue
        new = xr_load_candidate(folder, rel)
        hs = xr_hunks(side, base, new, col, col_live)
        cands[side] = {"folder": str(folder), "text": new, "hunks": hs, "summary": xr_summary(base, new, marks, hs)}
        hunks += hs
    if not cands:
        raise XRError("give at least one candidate folder (A or B)")

    # A site is a run of hunks that overlap or touch in baseline coordinates; hunks from one
    # candidate never do, so a site is either one candidate's hunk or a place both edited.
    sites = []
    for h in sorted(hunks, key=lambda h: (h["b0"], h["b1"], h["side"])):
        if sites and h["b0"] <= sites[-1]["b1"]:
            sites[-1]["hunks"].append(h)
            sites[-1]["b1"] = max(sites[-1]["b1"], h["b1"])
        else:
            sites.append({"b0": h["b0"], "b1": h["b1"], "hunks": [h]})
    nl_pos = [i for i, ch in enumerate(base) if ch == "\n"]
    for i, s in enumerate(sites):
        s["id"] = i
        s["line"] = bisect.bisect_left(nl_pos, s["b0"]) + 1
        s["base"] = base[s["b0"]:s["b1"]]
        s["before"], s["after"] = base[max(0, s["b0"] - 40):s["b0"]], base[s["b1"]:s["b1"] + 40]
        ls = base.rfind("\n", 0, s["b0"]) + 1
        le = base.find("\n", s["b1"])
        le = len(base) if le < 0 else le
        for k in ("a", "b"):
            hs = [h for h in s["hunks"] if h["side"] == k]
            s[k] = _xr_render(base, s["b0"], s["b1"], hs) if hs else None
            # does taking this side here, alone, leave the touched lines' braces/environments balanced?
            o, nw = _xr_bal(base[ls:le]), _xr_bal(base[ls:s["b0"]] + (s[k] or "") + base[s["b1"]:le])
            s[k + "_bal"] = [nw[0] - o[0], nw[1] - o[1]] if hs else None
            s[k + "_n"] = len(hs)
            s[k + "_colour"] = _xr_best([h["colour"] for h in hs])
            s["blocked_" + k] = any("g" in (h["colour"], h["live"]) for h in hs)
        s["state"] = "both" if s["a"] is not None and s["b"] is not None else "a" if s["a"] is not None else "b"
        s["agree"] = (None if s["state"] != "both" else "same" if s["a"] == s["b"]
                      else "same_ws" if s["a"].split() == s["b"].split() else "differ")
        s["ws"] = all(h["ws"] for h in s["hunks"])
        s["colour"] = _xr_best([h["colour"] for h in s["hunks"]])

    # recommendations: flags and a rule-based suggestion per site, then whatever the author imported
    bib, file_keys = xr_bib_keys(), xr_cites(base)
    bib_c = {k: xr_bib_keys(Path(c["folder"])) for k, c in cands.items()}
    for s in sites:
        ls = base.rfind("\n", 0, s["b0"]) + 1
        le = base.find("\n", s["b1"])
        le = len(base) if le < 0 else le
        s["line_end"] = bisect.bisect_left(nl_pos, s["b1"] - 1 if s["b1"] > s["b0"] else s["b0"]) + 1
        for k in ("a", "b"):
            s["flags_" + k] = (xr_flags(base[ls:le], base[ls:s["b0"]] + s[k] + base[s["b1"]:le], k, s, bib, file_keys, bib_c.get(k))
                               if s[k + "_n"] else [])
        s["rule"] = xr_rule_suggest(s)
        s["imports"] = []
    imp_text = req.get("import_text") or ""
    imp = (xr_import(imp_text, (req.get("import_name") or "imported review").strip()[:40], sites,
                     {k: c["folder"] for k, c in cands.items()}) if imp_text.strip() else None)
    for s in sites:
        s["plan_clear"], s["plan_lean"] = xr_combine(s, False), xr_combine(s, True)

    sig = hashlib.sha1("\0".join([base, json.dumps(marks_open), json.dumps(marks)]
                                 + [cands[k]["text"] for k in sorted(cands)]).encode("utf-8")).hexdigest()[:16]
    return {"rel": rel, "base": base, "marks": marks, "marks_open": marks_open, "col_live": col_live,
            "bl": bl, "cands": cands, "sites": sites, "sig": sig, "import": imp}


def xr_public(m):
    keep = ("id", "line", "line_end", "b0", "b1", "base", "a", "b", "a_n", "b_n", "a_colour", "b_colour",
            "blocked_a", "blocked_b", "a_bal", "b_bal", "state", "agree", "ws", "colour", "before", "after",
            "flags_a", "flags_b", "rule", "imports", "plan_clear", "plan_lean")
    return {"file": m["rel"], "sig": m["sig"],
            "sugg": {"clear": xr_sugg_counts(m["sites"], "plan_clear"), "lean": xr_sugg_counts(m["sites"], "plan_lean")},
            "import": m["import"], "chunks": xr_hunk_chunks(m),
            "prompt": xr_prompt(m["rel"], {k: c["folder"] for k, c in m["cands"].items()}),
            "baseline": {"label": m["bl"]["label"], "note": m["bl"]["note"], "chars": len(m["base"]),
                         "marks": len(m["marks"]), "matches_open": m["marks_open"] is not None,
                         "live_marks_differ": m["col_live"] is not None},
            "candidates": {k: dict(c["summary"], folder=c["folder"]) for k, c in m["cands"].items()},
            "sites": [{k: s[k] for k in keep} for s in m["sites"]]}


def _xr_backup(rel):
    d = ROOT / BUILD_DIR / "crossreview-backup"
    d.mkdir(parents=True, exist_ok=True)
    dst = d / (time.strftime("%Y%m%d-%H%M%S-") + rel.replace("/", "__"))
    shutil.copy2(safe(rel), dst)
    dst.with_name(dst.name + ".marks.json").write_text(json.dumps(marks_for(rel)), encoding="utf-8")
    comments = _ann_list(_ann_load(), rel)
    if comments:
        dst.with_name(dst.name + ".annotations.json").write_text(json.dumps(comments, ensure_ascii=False, indent=1), encoding="utf-8")
    return str(dst.relative_to(ROOT))


def xr_yellow_ranges(edits):
    """Where the inserted text of (b0, b1, new) edits (baseline coordinates, not overlapping) ends
    up in the merged text, as [start, end) ranges; ranges that touch are merged."""
    out, shift = [], 0
    for b0, b1, new in sorted(edits, key=lambda e: (e[0], e[1])):
        if new:
            s = b0 + shift
            if out and out[-1][1] >= s:
                out[-1][1] = s + len(new)
            else:
                out.append([s, s + len(new)])
        shift += len(new) - (b1 - b0)
    return out


def xr_applied_ranges(edits, blue):
    """xr_yellow_ranges split by what the text is marked afterwards: the inserted text of the edits in
    `blue` (a set of (b0, b1, new)) keeps its blue mark, the rest turns yellow. Ranges of one kind that
    touch are merged. -> (yellow_ranges, blue_ranges)"""
    ys, bs, shift = [], [], 0
    for e in sorted(edits, key=lambda e: (e[0], e[1])):
        b0, b1, new = e
        if new:
            s, tgt = b0 + shift, (bs if e in blue else ys)
            if tgt and tgt[-1][1] >= s:
                tgt[-1][1] = s + len(new)
            else:
                tgt.append([s, s + len(new)])
        shift += len(new) - (b1 - b0)
    return ys, bs


def xr_touches_blue(cmap, edit):
    """Does this edit rewrite blue text (without touching green, which always wins)? An insertion counts
    when it lands strictly inside a blue span."""
    b0, b1, _ = edit
    if b1 > b0:
        seen = set(cmap[b0:b1])
        return "b" in seen and "g" not in seen
    return b0 > 0 and b0 < len(cmap) and cmap[b0 - 1] == cmap[b0] == "b"


def xr_mark_yellow(marks, ranges):
    return xr_paint(marks, ranges, "y")


def xr_paint(marks, ranges, colour):
    """Paint every range with `colour` -- yellow = 'changed by a tool, waiting for the author', blue = 'the
    decision here is still open': whatever mark was there (red, yellow, or green that the mark rule
    stretched over a boundary insertion) keeps only the part outside the ranges. The new span merges
    with marks of the same colour it touches."""
    out = []
    for m in marks:
        pieces = [(m["start"], m["end"])]
        for rs, re_ in ranges:
            pieces = [q for ps, pe in pieces for q in
                      (((ps, pe),) if pe <= rs or ps >= re_ else
                       (((ps, rs),) if ps < rs else ()) + (((re_, pe),) if pe > re_ else ()))]
        out += [{"start": ps, "end": pe, "color": m["color"]} for ps, pe in pieces]
    yel, keep = [list(r) for r in ranges], []
    for m in out:
        if m["color"] == colour and any(m["start"] <= r[1] and m["end"] >= r[0] for r in ranges):
            yel.append([m["start"], m["end"]])
        else:
            keep.append(m)
    merged = []
    for s, e in sorted(yel):
        if merged and s <= merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], e)
        else:
            merged.append([s, e])
    return sorted(keep + [{"start": s, "end": e, "color": colour} for s, e in merged], key=lambda m: m["start"])


def xr_apply(req):
    """Apply the chosen hunks to the open file or to a new copy and carry the marks through.
    Everything is recomputed from disk and checked before the first byte is written.
    Text that comes from an applied hunk is marked yellow (never green) unless req["mark_yellow"]
    is false; the author turns it green after reviewing it."""
    m = xr_build(req)
    if req.get("sig") != m["sig"]:
        raise XRError("A file changed on disk since this comparison - press Compare again.")
    sites, base = m["sites"], m["base"]
    overrides = {int(x) for x in req.get("overrides") or []}
    edits, blocked, used_override, n = [], [], False, {"a": 0, "b": 0}
    for key, pick in (req.get("choices") or {}).items():
        try:
            i = int(key)
            s = sites[i] if 0 <= i < len(sites) else None
        except (TypeError, ValueError):
            s = None
        if s is None:
            raise XRError(f"no hunk #{key}")
        if pick == "base":
            continue
        if pick not in ("a", "b"):
            raise XRError(f"hunk #{i}: unknown choice {pick!r}")
        if s[pick + "_n"] == 0:
            raise XRError(f"hunk #{i}: {pick.upper()} did not change this passage")
        if s["blocked_" + pick]:
            if i not in overrides:
                blocked.append(i)
                continue
            used_override = True
        edits += [(h["b0"], h["b1"], h["new"]) for h in s["hunks"] if h["side"] == pick]
        n[pick] += 1
    if blocked:
        raise XRError("Blocked: hunk(s) " + ", ".join(f"#{i}" for i in blocked) +
                      " change green text. Tick 'override' on each one you really want.")

    target = req.get("target")
    if target == "open":
        rel = dest = m["rel"]
        carry = m["marks_open"]
        if carry is None:
            raise XRError("The open file is not the baseline text, so baseline offsets cannot be "
                          "applied to it. Write a new copy, or use 'current file' as the baseline.")
    elif target == "copy":
        dest = (req.get("copy_path") or "").strip()
        try:
            p_dest = safe(dest)
        except ValueError as exc:
            raise XRError(f"new copy: {exc}")
        if p_dest.exists():
            raise XRError(f"{dest} already exists - a new copy never overwrites anything.")
        carry = m["marks"]
    else:
        raise XRError("target must be 'open' or 'copy'")

    text, marks = base, carry
    for b0, b1, new in sorted(edits, key=lambda e: (e[0], e[1]), reverse=True):
        nt = text[:b0] + new + text[b1:]
        marks = xr_adjust_marks(marks, text, nt)
        text = nt

    mark_yellow = bool(req.get("mark_yellow", True))
    cmap = xr_colour_map(len(base), carry)
    blue = {e for e in edits if xr_touches_blue(cmap, e)}      # text rewritten inside a blue span stays blue
    ranges, blue_ranges = xr_applied_ranges(edits, blue) if mark_yellow else ([], [])
    if mark_yellow:
        marks = xr_paint(xr_mark_yellow(marks, ranges), blue_ranges, "b")

    bad = xr_marks_problems(text, marks, overlap=not xr_marks_problems(base, carry))
    g0, g1 = [x for x in carry if x["color"] == "g"], [x for x in marks if x["color"] == "g"]
    if not used_override:
        # yellow painting trims a green span a boundary insertion stretched, so it is exact then
        same = (lambda a, b: base[a["start"]:a["end"]] == text[b["start"]:b["end"]]) if mark_yellow \
            else (lambda a, b: base[a["start"]:a["end"]] in text[b["start"]:b["end"]])
        if len(g0) != len(g1) or not all(same(a, b) for a, b in zip(g0, g1)):
            bad.append("a green span would not survive verbatim")
    if any(g["start"] < re_ and g["end"] > rs for g in g1 for rs, re_ in ranges + blue_ranges):
        bad.append("changed text would be marked green")
    if not all(any(y["color"] == "y" and y["start"] <= rs and y["end"] >= re_ for y in marks) for rs, re_ in ranges):
        bad.append("changed text would not be marked yellow")
    if not all(any(y["color"] == "b" and y["start"] <= rs and y["end"] >= re_ for y in marks) for rs, re_ in blue_ranges):
        bad.append("rewritten blue text would not stay blue")
    if bad:
        raise XRError("Nothing written - the marks would be inconsistent: " + "; ".join(bad[:3]))
    warnings = []
    (b0_, e0_), (b1_, e1_) = _xr_bal(base), _xr_bal(text)
    if b0_ != b1_:
        warnings.append(f"Braces: the merged file has {b1_ - b0_:+d} net '{{' minus '}}' compared with the baseline - "
                        "a hunk that adds or removes a brace was taken without its partner. LaTeX will likely stop.")
    if e0_ != e1_:
        warnings.append(f"Environments: {e1_ - e0_:+d} net \\begin minus \\end compared with the baseline - "
                        "a hunk was taken without its partner. LaTeX will likely stop.")
    pb, pt = _xr_para_unbalanced(base), _xr_para_unbalanced(text)
    if len(pt) > len(pb):
        warnings.append(f"Braces: {len(pt) - len(pb)} more paragraph(s) than in the baseline do not balance their braces "
                        f"(first at line {pt[0]} of the merged file) - a brace opened in one paragraph is closed in a later "
                        "one, so a hunk was taken without its partner. LaTeX will likely stop.")

    backup = None
    if target == "open":
        backup = _xr_backup(rel)
        safe(rel).write_text(text, encoding="utf-8")
    else:
        p_dest.parent.mkdir(parents=True, exist_ok=True)
        p_dest.write_text(text, encoding="utf-8")
    set_marks_for(dest, xr_marks_out(text, marks))
    comments = ann_carry_apply(m["rel"], dest, base, edits)       # comment anchors follow the edits like the marks
    return {"ok": True, "target": target, "path": dest, "backup": backup, "chars": len(text),
            "hunks": {"a": n["a"], "b": n["b"]}, "marks_before": len(carry), "marks_after": len(marks),
            "green_before": len(g0), "green_after": len(g1), "override": used_override,
            "yellow_spans": len(ranges), "yellow_chars": sum(e - s for s, e in ranges),
            "blue_spans": len(blue_ranges), "blue_chars": sum(e - s for s, e in blue_ranges),
            "comments": comments, "warnings": warnings}


def xr_prompt(rel, folders=None):
    """The review prompt. folders = {side: folder path} names the candidates (A = claude, ...)."""
    cands = (", ".join(f"{k.upper()} = {Path(v).name}" for k, v in sorted(folders.items()))
             if folders else "A and B, as named in the hunk lists that follow")
    return XR_PROMPT.replace("__FILE__", rel or MAIN).replace("__CANDIDATES__", cands)


# --------------------------------------------------------------------------
#  HTTP
# --------------------------------------------------------------------------
class Handler(http.server.BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, *a):                                  # quiet
        pass

    def _send(self, code, body, ctype="application/json", extra=None):
        if isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def _xr_guard(self, post=False):
        """The cross-review endpoints read other folders and can write project files, so refuse
        what a web page from another site could send to localhost: a foreign Host header (DNS
        rebinding), a foreign Origin, or a POST that is not JSON (browsers only send that
        cross-site after a CORS preflight, which texpad never grants)."""
        local = {"127.0.0.1", "localhost"}
        ok = self.headers.get("Host", "").rsplit(":", 1)[0] in local
        origin = self.headers.get("Origin")
        if origin:                                # same origin: local host AND the very host:port this request was sent to
            ok = ok and urllib.parse.urlparse(origin).hostname in local and urllib.parse.urlparse(origin).netloc.lower() == self.headers.get("Host", "").lower()
        if post:
            ok = ok and self.headers.get("Content-Type", "").split(";")[0].strip().lower() == "application/json"
        if not ok:
            self._send(403, json.dumps({"error": "refused: not a local request"}))
        return ok

    def do_GET(self):
        u = urllib.parse.urlparse(self.path)
        q = urllib.parse.parse_qs(u.query)

        if u.path == "/":
            return self._send(200, PAGE.replace("__MAIN__", MAIN)
                              .replace("__PROJECT__", ROOT.name),
                              "text/html; charset=utf-8")

        if u.path == "/api/state":
            tc = {k: bool(v) for k, v in toolchain().items()}
            with LOCK:
                s = dict(STATE)
            s["tools"] = tc
            s["files"] = file_list()
            s["problems"] = problems(s.pop("log", ""))
            s["git"] = is_git_repo()
            return self._send(200, json.dumps(s))

        if u.path == "/api/file":
            rel = q.get("path", [""])[0]
            try:
                p = safe(rel)
                text = p.read_text(encoding="utf-8")
            except Exception as exc:                            # noqa: BLE001
                return self._send(400, json.dumps({"error": str(exc)}))
            return self._send(200, json.dumps(
                {"text": text, "outline": outline(text), "marks": marks_for(rel)}))

        if u.path == "/api/sync":
            try:
                rel = q.get("file", [""])[0]
                safe(rel)                       # same allow-list as the editor
                r = sync_forward(rel, int(q.get("line", ["1"])[0]))
            except Exception:                                   # noqa: BLE001
                r = None
            return self._send(200, json.dumps(r or {}))

        if u.path in ("/api/settings", "/api/review/info", "/api/review/download"):
            if not self._xr_guard():
                return
            try:
                if u.path == "/api/settings":
                    return self._send(200, json.dumps({"author": settings_author()}))
                if u.path == "/api/review/info":
                    rel = q.get("file", [""])[0]
                    if rel:
                        safe(rel)
                    return self._send(200, json.dumps(rv_info(rel)))
                name = q.get("name", [""])[0]
                p = ROOT / BUILD_DIR / "review" / name
                if (not re.fullmatch(r"review-[A-Za-z0-9._-]+\.html", name) or not p.is_file()
                        or p.resolve().parent != (ROOT / BUILD_DIR / "review").resolve()):      # a symlink out of the folder is not served
                    return self._send(404, json.dumps({"error": "no such review file"}))
                return self._send(200, p.read_bytes(), "text/html; charset=utf-8",
                                  {"Content-Disposition": 'attachment; filename="' + name + '"'})
            except (AnnError, ValueError, OSError) as exc:
                return self._send(400, json.dumps({"error": str(exc)}))

        if u.path in ("/api/ann", "/api/ann/export"):
            if not self._xr_guard():
                return
            rel = q.get("file", [""])[0]
            try:
                safe(rel)                       # same allow-list as the editor
                if u.path.endswith("export"):
                    return self._send(200, ann_export(rel), "text/markdown; charset=utf-8")
                view = ann_view(rel)
                return self._send(200, json.dumps({"annotations": view, "counts": ann_counts(view)}))
            except (AnnError, ValueError, OSError) as exc:
                return self._send(400, json.dumps({"error": str(exc)}))

        if u.path == "/api/xr/prompt":
            if not self._xr_guard():
                return
            return self._send(200, json.dumps({"text": xr_prompt(q.get("file", [""])[0])}))

        if u.path == "/pdf":
            pdf = ROOT / BUILD_DIR / (Path(MAIN).stem + ".pdf")
            if not pdf.exists():
                return self._send(404, b"no pdf yet", "text/plain")
            return self._send(200, pdf.read_bytes(), "application/pdf",
                              {"Content-Disposition": 'inline; filename="main.pdf"'})

        if u.path == "/page":
            tc = toolchain()
            n = q.get("n", ["1"])[0]
            pdf = ROOT / BUILD_DIR / (Path(MAIN).stem + ".pdf")
            if not (tc["pdftoppm"] and pdf.exists()):
                return self._send(404, b"", "text/plain")
            png = ROOT / BUILD_DIR / f"page-{n}.png"
            try:
                with RENDER_SEM:
                    subprocess.run(low_prio([tc["pdftoppm"], "-r", "110", "-png", "-f", n, "-l", n,
                                             "-singlefile", str(pdf), str(png.with_suffix(""))]),
                                   check=True, timeout=60, env=tex_env(),
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                                   **LOW_PRIO_KW)
                    data = png.read_bytes()
                return self._send(200, data, "image/png")
            except Exception:                                   # noqa: BLE001
                return self._send(404, b"", "text/plain")

        return self._send(404, b"not found", "text/plain")

    def do_POST(self):
        u = urllib.parse.urlparse(self.path)
        n = int(self.headers.get("Content-Length", 0))
        body = json.loads(self.rfile.read(n) or b"{}")

        if u.path == "/api/save":
            try:
                p = safe(body["path"])
                p.write_text(body["text"], encoding="utf-8")
                if "marks" in body:
                    set_marks_for(body["path"], body["marks"])
            except Exception as exc:                            # noqa: BLE001
                return self._send(400, json.dumps({"error": str(exc)}))
            return self._send(200, json.dumps({"ok": True}))

        if u.path in ("/api/settings", "/api/review/share", "/api/review/import"):
            if not self._xr_guard(post=True):
                return
            try:
                if u.path == "/api/settings":
                    return self._send(200, json.dumps({"author": settings_save(body).get("author") or "you"}))
                return self._send(200, json.dumps(rv_share(body) if u.path.endswith("share") else rv_import(body)))
            except (AnnError, ValueError, OSError) as exc:
                return self._send(400, json.dumps({"error": str(exc)}))

        if u.path == "/api/ann":
            if not self._xr_guard(post=True):
                return
            try:
                return self._send(200, json.dumps(ann_op(body)))
            except (AnnError, ValueError, OSError) as exc:
                return self._send(400, json.dumps({"error": str(exc)}))

        if u.path in ("/api/xr/compare", "/api/xr/apply", "/api/xr/plan"):
            if not self._xr_guard(post=True):
                return
            try:
                out = (xr_public(xr_build(body)) if u.path.endswith("compare")
                       else xr_plan(body) if u.path.endswith("plan") else xr_apply(body))
            except (XRError, ValueError, OSError) as exc:
                return self._send(400, json.dumps({"error": str(exc)}))
            return self._send(200, json.dumps(out))

        if u.path == "/api/pull":
            ok, out = git_pull()
            return self._send(200, json.dumps({"ok": ok, "output": out}))

        if u.path == "/api/push":
            ok, out = git_push_all(body.get("message") or "Edit from texpad")
            return self._send(200, json.dumps({"ok": ok, "output": out}))

        if u.path == "/api/revsync":
            try:
                r = sync_reverse(int(body["page"]), float(body["x"]), float(body["y"]))
            except Exception:                                   # noqa: BLE001
                r = None
            return self._send(200, json.dumps(r or {}))

        if u.path == "/api/compile":
            with LOCK:
                if STATE["busy"]:
                    return self._send(200, json.dumps({"busy": True}))
                STATE["busy"] = True
            try:
                haspdf, log = compile_project()
                pdf = ROOT / BUILD_DIR / (Path(MAIN).stem + ".pdf")
                probs = problems(log)
                nerr = sum(1 for x in probs if x["sev"] == "error")
                with LOCK:
                    STATE.update(ok=(haspdf and not nerr), log=log, at=time.time(),
                                 busy=False, pages=page_count(pdf) if haspdf else 0)
                return self._send(200, json.dumps(
                    {"ok": haspdf and not nerr, "haspdf": haspdf, "errors": nerr,
                     "problems": probs, "pages": STATE["pages"], "at": STATE["at"]}))
            except Exception as exc:                            # noqa: BLE001
                with LOCK:
                    STATE["busy"] = False
                return self._send(500, json.dumps({"error": str(exc)}))

        return self._send(404, json.dumps({"error": "not found"}))


class Server(socketserver.ThreadingTCPServer):
    allow_reuse_address = True
    daemon_threads = True


# --------------------------------------------------------------------------
#  UI  (single page, no CDN, works offline)
# --------------------------------------------------------------------------
PAGE = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<title>__PROJECT__ - texpad</title>
<style>
  :root{
    --bg:#ffffff; --panel:#f6f7f8; --line:#dfe3e6; --ink:#15181c;
    --muted:#6b7280; --accent:#0065bd; --bad:#b42318; --good:#067647;
  }
  @media (prefers-color-scheme: dark){
    :root{ --bg:#14171a; --panel:#1b1f23; --line:#2b3138; --ink:#e6e9ec;
           --muted:#9aa4af; --accent:#4d9de0; }
  }
  *{box-sizing:border-box}
  html,body{height:100%;margin:0}
  body{font:14px/1.45 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;
       color:var(--ink);background:var(--bg);display:flex;flex-direction:column}
  header{display:flex;align-items:center;gap:12px;padding:8px 12px;
         border-bottom:1px solid var(--line);background:var(--panel);flex:0 0 auto}
  header b{font-weight:600}
  .pill{font-size:12px;padding:2px 8px;border-radius:99px;border:1px solid var(--line);
        color:var(--muted);white-space:nowrap}
  .pill.ok{color:var(--good);border-color:var(--good)}
  .pill.bad{color:var(--bad);border-color:var(--bad)}
  .pill.work{color:var(--accent);border-color:var(--accent)}
  button{font:inherit;padding:5px 12px;border-radius:6px;border:1px solid var(--line);
         background:var(--bg);color:var(--ink);cursor:pointer}
  button:hover{border-color:var(--accent)}
  button.primary{background:var(--accent);color:#fff;border-color:var(--accent)}
  main{flex:1 1 auto;display:flex;min-height:0}
  #left{flex:0 0 46%;min-width:0;display:flex;flex-direction:column;
        border-right:1px solid var(--line);min-height:0}
  #right{flex:1 1 auto;display:flex;flex-direction:column;min-width:0;background:var(--panel)}
  #bar{display:flex;gap:8px;align-items:center;padding:6px 10px;flex-wrap:nowrap;
       border-bottom:1px solid var(--line);flex:0 0 auto;overflow:hidden}
  select{font:inherit;padding:4px 6px;border-radius:6px;border:1px solid var(--line);
         background:var(--bg);color:var(--ink);max-width:38%;min-width:0}
  #editwrap{flex:1 1 auto;display:flex;min-height:0}
  #gutter{padding:10px 8px;text-align:right;color:var(--muted);background:var(--panel);
          font:13px/1.55 ui-monospace,SFMono-Regular,Menlo,monospace;white-space:pre;
          min-width:4ch;user-select:none;overflow:hidden;flex:0 0 auto;
          border-right:1px solid var(--line)}
  /* #hl sits behind the textarea and paints the highlight colour; #ed floats on
     top with a transparent background so its real, editable text shows through
     the colour. Both need identical font metrics/padding or the two won't line
     up. */
  #edstack{position:relative;flex:1 1 auto;min-width:0;min-height:0;background:var(--bg);
           overflow:hidden}
  #hl,#ed{position:absolute;inset:0;margin:0;border:0;padding:10px 12px;
          font:13px/1.55 ui-monospace,SFMono-Regular,Menlo,monospace;
          tab-size:2;white-space:pre;overflow:auto}
  /* Invisible copy of the text, one block per source line, laid out at the
     textarea's exact width: its row heights size the gutter numbers and give
     each line's scroll position once wrapping makes lines span several rows. */
  #measure{position:absolute;left:0;top:0;visibility:hidden;pointer-events:none;
           margin:0;border:0;padding:10px 12px;
           font:13px/1.55 ui-monospace,SFMono-Regular,Menlo,monospace;
           tab-size:2;white-space:pre}
  /* Soft wrap: long lines flow onto the next screen row instead of scrolling
     sideways. Display only -- no line breaks are written into the file. */
  body.wrap #hl, body.wrap #ed, body.wrap #measure{white-space:pre-wrap;overflow-wrap:break-word}
  body.wrap #ed{overflow-x:hidden}
  #hl{color:transparent;pointer-events:none;overflow:hidden}
  #hl mark{color:transparent;background:none;border-radius:2px;padding:0}
  #hl mark.hy{background:rgba(255,196,0,.45)}
  #hl mark.hr{background:rgba(255,70,70,.42)}
  #hl mark.hg{background:rgba(46,196,110,.4)}
  #ed{outline:0;resize:none;background:transparent;color:var(--ink)}
  #hlbar{display:flex;gap:5px;align-items:center}
  .sw{width:17px;height:17px;padding:0;border-radius:50%;flex:0 0 auto}
  #probs{flex:0 0 auto;max-height:30%;overflow:auto;border-top:1px solid var(--line);
         background:var(--panel);padding:8px 10px;
         font:12px/1.5 ui-monospace,SFMono-Regular,Menlo,monospace;display:none}
  #probs .e{color:var(--bad)} #probs .w{color:var(--muted)}
  #probs .hdr{font-weight:600;margin-bottom:4px}
  #view{flex:1 1 auto;overflow:auto;padding:14px;text-align:center}
  .pg{position:relative;display:inline-block;max-width:100%;margin:0 auto 14px;line-height:0}
  .pg img{width:100%;height:auto;box-shadow:0 1px 6px rgba(0,0,0,.25);background:#fff;
          display:block;cursor:crosshair}
  .hl{position:absolute;background:rgba(255,196,0,.32);outline:1px solid rgba(214,150,0,.85);
      border-radius:2px;pointer-events:none;transition:all .12s ease-out;display:none}
  .pgno{position:absolute;right:-2px;bottom:-13px;font-size:10px;color:var(--muted);line-height:1}
  #view iframe{width:100%;height:100%;border:0;background:#fff}
  .hint{color:var(--muted);font-size:12px}
  .out{cursor:pointer;padding:1px 0}
  .out:hover{color:var(--accent)}
  /* Cross-review panel: takes the place of the editor and PDF while it is open */
  #xr{flex:1 1 auto;background:var(--bg);display:flex;flex-direction:column;min-height:0}
  #xr[hidden]{display:none}
  body.xropen main{display:none}
  #xr input[type=text]{font:inherit;padding:4px 6px;border-radius:6px;border:1px solid var(--line);
      background:var(--bg);color:var(--ink);min-width:0}
  .xrbar{display:flex;gap:10px;align-items:center;flex-wrap:wrap;padding:7px 12px;
         border-bottom:1px solid var(--line);flex:0 0 auto}
  #xrsum{display:flex;gap:12px;flex-wrap:wrap;padding:8px 12px;border-bottom:1px solid var(--line);
         background:var(--panel);flex:0 0 auto;font-size:12px;max-height:24vh;overflow:auto}
  #xrsum .card{flex:1 1 360px;min-width:0}
  #xrsum .card b{font-size:13px}
  .ok{color:var(--good)} .bad{color:var(--bad)}
  .chip{display:inline-block;font-size:11px;line-height:16px;padding:0 7px;border-radius:99px;
        border:1px solid var(--line);white-space:nowrap}
  .chip.cy{background:rgba(255,196,0,.45)} .chip.cr{background:rgba(255,70,70,.42)}
  .chip.cg{background:rgba(46,196,110,.4)}
  .chip.cedge{background:repeating-linear-gradient(45deg,transparent 0 4px,rgba(130,130,130,.3) 4px 8px)}
  #xrlist{flex:1 1 auto;overflow:auto;min-height:200px}
  #xr{overflow-y:auto}
  .xrbar[hidden]{display:none}
  .chip.cb{background:rgba(59,130,246,.4)}
  header{flex-wrap:wrap;row-gap:6px}          /* the comments pill and button must not push the others off a narrow window */
  /* blue = "you decide here" (not frozen: only green is) */
  #hl mark.hb{background:rgba(59,130,246,.38)}
  #legend{position:fixed;top:92px;left:12px;z-index:30;max-width:360px;padding:10px 12px;border:1px solid var(--line);
          border-radius:8px;background:var(--panel);box-shadow:0 4px 16px rgba(0,0,0,.2);font-size:12.5px;line-height:1.9}
  #legend[hidden]{display:none}
  /* comments: an underline layer between the highlight layer and the text, like the anchors of a Google Docs comment */
  #al{position:absolute;inset:0;margin:0;border:0;padding:10px 12px;font:13px/1.55 ui-monospace,SFMono-Regular,Menlo,monospace;
      tab-size:2;white-space:pre;overflow:hidden;color:transparent;pointer-events:none}
  body.wrap #al{white-space:pre-wrap;overflow-wrap:break-word}
  #al .ac{text-decoration:underline;text-decoration-thickness:1.5px;text-underline-offset:3px}
  #al .ac.k-info{text-decoration-color:rgba(120,120,140,.85)}
  #al .ac.k-source{text-decoration-color:rgba(124,58,237,.9)}
  #al .ac.k-check{text-decoration-color:rgba(217,119,6,.95)}
  #al .ac.decide{text-decoration-color:rgba(37,99,235,.98);text-decoration-thickness:2.5px;background:rgba(37,99,235,.1)}
  #al .ac.done{text-decoration-style:dotted;text-decoration-thickness:1px;text-decoration-color:rgba(120,120,140,.45);background:none}
  #al .ac.on{outline:2px solid rgba(37,99,235,.65);border-radius:2px}
  #al .ac.flash{animation:annflash 1.4s ease-out}
  @keyframes annflash{0%{background:rgba(255,196,0,.85)}100%{background:rgba(255,196,0,0)}}
  #anns{flex:0 0 340px;display:flex;flex-direction:column;min-height:0;min-width:0;border-left:1px solid var(--line);background:var(--bg)}
  #anns[hidden]{display:none}
  #annhead{display:flex;flex-wrap:wrap;gap:6px 8px;align-items:center;padding:7px 10px;border-bottom:1px solid var(--line);flex:0 0 auto}
  #annfilter{display:flex;gap:8px;flex-wrap:wrap;align-items:center;padding:6px 10px;border-bottom:1px solid var(--line);
             flex:0 0 auto;font-size:12px}
  #annnew,#annexp{padding:8px 10px;border-bottom:1px solid var(--line);background:var(--panel);flex:0 0 auto;font-size:12.5px}
  #annnew[hidden],#annexp[hidden]{display:none}
  #annnew textarea,#annexp textarea,.ann textarea{width:100%;font:12.5px/1.4 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;
        border:1px solid var(--line);border-radius:6px;background:var(--bg);color:var(--ink);padding:5px 7px}
  #annexp textarea{font:11.5px/1.4 ui-monospace,Menlo,monospace;height:180px}
  #annlist{flex:1 1 auto;overflow:auto;padding:6px 8px;min-height:0}
  .ann{border:1px solid var(--line);border-radius:8px;padding:7px 9px;margin:0 0 8px;cursor:pointer;background:var(--bg);font-size:12.5px}
  .ann.on{border-color:var(--accent);box-shadow:0 0 0 1px var(--accent)}
  .ann.done{opacity:.6} .ann.lost{border-style:dashed}
  .annmeta{display:flex;gap:6px;align-items:baseline;flex-wrap:wrap}
  .annq{color:var(--muted);font-style:italic;margin:3px 0;border-left:3px solid var(--line);padding-left:6px;
        white-space:pre-wrap;overflow-wrap:anywhere}
  .annt{white-space:pre-wrap;overflow-wrap:anywhere;margin:3px 0}
  .annr{border-top:1px dashed var(--line);margin-top:5px;padding-top:4px;white-space:pre-wrap;overflow-wrap:anywhere}
  .annact{display:flex;gap:6px;margin-top:6px;flex-wrap:wrap}
  .annact button{padding:1px 8px;font-size:12px}
  .kb{font-size:11px;padding:0 7px;border-radius:99px;color:#fff;line-height:17px}
  .kb.k-decide{background:#2563eb} .kb.k-info{background:#6b7280} .kb.k-source{background:#7c3aed} .kb.k-check{background:#d97706}
  .kc{display:inline-flex;gap:3px;align-items:center}
  /* reviewer comments (kind "review"), author badges, the name box, import panel and the Share dialog */
  .kb.k-review{background:#0f766e}
  #al .ac.k-review{text-decoration-color:rgba(15,118,110,.95)}
  .av{display:inline-flex;align-items:center;justify-content:center;width:18px;height:18px;border-radius:50%;font-size:9px;
      font-weight:700;color:#fff;flex:0 0 auto;align-self:center;letter-spacing:-.2px}
  #annwho{display:flex;gap:6px;align-items:center;padding:5px 10px;border-bottom:1px solid var(--line);font-size:12px;flex:0 0 auto}
  #annwho input{width:150px;font-size:12px}
  #annimp{padding:8px 10px;border-bottom:1px solid var(--line);background:var(--panel);flex:0 0 auto;font-size:12.5px;max-height:46vh;overflow:auto}
  #annimp[hidden]{display:none}
  #annimp textarea{width:100%;height:80px;font:11.5px/1.4 ui-monospace,Menlo,monospace;border:1px solid var(--line);
                   border-radius:6px;background:var(--bg);color:var(--ink);padding:5px 7px;margin-top:5px}
  #annimp-res ul{margin:4px 0 0 16px;padding:0} #annimp-res li{margin:1px 0}
  .annsh{display:flex;gap:4px;align-items:center;margin-top:5px;font-size:11.5px;color:var(--muted);cursor:pointer}
  #sharedlg{position:fixed;inset:0;z-index:70;background:rgba(0,0,0,.45);display:flex;align-items:center;justify-content:center;padding:16px}
  #sharedlg[hidden]{display:none}
  #sharebox{width:min(660px,100%);max-height:94vh;overflow:auto;background:var(--bg);color:var(--ink);border:1px solid var(--line);
            border-radius:10px;box-shadow:0 8px 32px rgba(0,0,0,.4);padding:14px 16px;font-size:13px;line-height:1.45}
  #sharebox .row{margin:10px 0} #sharebox .row>b{display:block;margin-bottom:3px}
  #sharebox label{display:block}
  #sharebox input[type=text],#sharebox textarea{width:100%;font:13px/1.4 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;
        border:1px solid var(--line);border-radius:6px;background:var(--bg);color:var(--ink);padding:5px 7px}
  #share-files{max-height:112px;overflow:auto;border:1px solid var(--line);border-radius:6px;padding:3px 8px}
  .sharenote{border-left:3px solid #c98a00;padding:2px 0 2px 9px;margin:10px 0}
  #share-status code{font:12px ui-monospace,Menlo,monospace;overflow-wrap:anywhere}
  .shareok{border:1px solid var(--good);border-radius:8px;padding:8px 10px;margin-top:8px}
  .annact a.dl{padding:1px 10px;font-size:12px;border:1px solid var(--line);border-radius:6px;text-decoration:none;color:var(--ink);background:var(--panel)}
  #annpill{cursor:pointer}
  .xrhead,.xrrow{display:grid;grid-template-columns:112px minmax(0,1fr) minmax(0,1fr) minmax(0,1fr) 172px;
                 gap:10px;padding:6px 12px;align-items:start}
  .xrhead{position:sticky;top:0;background:var(--panel);border-bottom:1px solid var(--line);
          font-weight:600;font-size:12px;z-index:1}
  .xrrow{border-bottom:1px solid var(--line)}
  .xrrow.blk{background:rgba(180,35,24,.07)}
  .xrcell{font:12px/1.45 ui-monospace,SFMono-Regular,Menlo,monospace;white-space:pre-wrap;
          overflow-wrap:anywhere}
  .xrcell .ctx{color:var(--muted)} .xrcell i{color:var(--muted)}
  .xrcell mark{color:inherit;border-radius:2px;padding:0 1px}
  .xrcell mark.del{background:rgba(180,35,24,.22)} .xrcell mark.ins{background:rgba(6,118,71,.24)}
  .xrpick{display:flex;flex-direction:column;gap:1px;font-size:12px}
  .xrpick label.off{color:var(--muted);opacity:.55}
  .xrpick .ov{color:var(--bad)}
  #xrprompt{width:100%;height:120px;font:12px/1.4 ui-monospace,Menlo,monospace}
  /* recommendations: one line per source under the hunk, never combined into one */
  .xrsug{grid-column:1/-1;display:flex;flex-direction:column;gap:2px;font-size:12px;padding:0 0 3px 122px}
  .xrsug .ln{display:flex;gap:6px;flex-wrap:wrap;align-items:baseline}
  .src{font-size:11px;padding:0 6px;border-radius:99px;border:1px solid var(--line);color:var(--muted);white-space:nowrap}
  .src.imp{border-color:var(--accent);color:var(--accent)}
  .pk{font-weight:600;white-space:nowrap} .pk.take{color:var(--good)} .pk.keep{color:var(--muted)} .pk.judge{color:#b7791f}
  .xrflags{margin-top:4px;display:flex;flex-direction:column;gap:2px;font:11px/1.35 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif}
  .fl{border-left:3px solid var(--line);padding-left:5px;color:var(--muted)}
  .fl.block,.fl.avoid{border-color:var(--bad);color:var(--bad)} .fl.verify,.fl.style{border-color:#c98a00}
  .fl.pair{border-color:#7c3aed}
</style></head><body>

<header>
  <b>__PROJECT__</b>
  <span class="pill" id="tools">checking TeX…</span>
  <span style="flex:1"></span>
  <span class="pill" id="status">idle</span>
  <button id="pull" title="git pull -- fetch edits/highlights pushed from elsewhere (e.g. your phone)">&#8595; Pull</button>
  <button id="push" title="git add -A && commit && push -- send local edits/highlights to GitHub">&#8593; Push</button>
  <button id="xrbtn" title="Compare two candidate versions of this file against a baseline and merge hunk by hunk">Cross-review</button>
  <button id="sharebtn" title="Make one self-contained HTML file a reviewer can read in any browser and comment on, then import their comments here">Share for review</button>
  <button id="save" class="primary">Save &amp; compile <span class="hint">⌘S</span></button>
  <button id="recompile">Recompile</button>
</header>

<main>
  <div id="left">
    <div id="bar">
      <select id="files"></select>
      <select id="outline"><option>outline</option></select>
      <span id="hlbar" title="Highlight the selected text (⌥1 clear · ⌥2 revision · ⌥3 to-do · ⌥4 done)">
        <button class="sw" data-c=""  style="background:#fff;border:1px solid var(--line)" title="Clear highlight (⌥1)"></button>
        <button class="sw" data-c="y" style="background:#ffd600" title="Needs revision (⌥2)"></button>
        <button class="sw" data-c="r" style="background:#ff5a5a" title="To-do (⌥3)"></button>
        <button class="sw" data-c="g" style="background:#2ecc71" title="Done (⌥4)"></button>
      </span>
      <span style="flex:1"></span>
      <label class="hint" title="Wrap long lines at the edge of the pane (display only)"><input type="checkbox" id="wrap" checked> wrap</label>
      <label class="hint"><input type="checkbox" id="auto" checked> auto</label>
      <label class="hint"><input type="checkbox" id="follow" checked> follow</label>
    </div>
    <div id="editwrap"><div id="gutter">1</div><div id="edstack"><div id="measure"></div><div id="hl"></div><textarea id="ed" spellcheck="false"></textarea></div></div>
    <div id="probs"></div>
  </div>
  <div id="right"><div id="view"><p class="hint">Compiling…</p></div></div>
  <aside id="anns" hidden>
    <div id="annhead">
      <b>Comments</b> <span class="hint" id="anncount"></span>
      <span style="flex:1"></span>
      <button id="ann-import" title="Bring in the comments a reviewer wrote in a review copy (their comments-….json file, or its pasted contents)">Import reviewer comments</button>
      <button id="ann-export" title="A plain Markdown list of the open comments (kind, line, quote, text, replies) for reading or printing">Export</button>
      <button id="ann-close" title="Hide the comments (⌥M adds one)">✕</button>
    </div>
    <div id="annwho"><label class="hint" title="Used as the author of the comments and replies you write. Saved in .texpad-settings.json (add it to .gitignore).">Your name <input type="text" id="ann-who" maxlength="60" placeholder="you"></label><span class="hint" id="ann-whomsg"></span></div>
    <div id="annfilter">
      <select id="ann-status"><option value="open">open</option><option value="resolved">resolved</option><option value="all">all</option></select>
      <label class="kc"><input type="checkbox" data-k="decide" checked> <span class="kb k-decide">decide</span></label>
      <label class="kc"><input type="checkbox" data-k="info" checked> <span class="kb k-info">info</span></label>
      <label class="kc"><input type="checkbox" data-k="source" checked> <span class="kb k-source">source</span></label>
      <label class="kc"><input type="checkbox" data-k="check" checked> <span class="kb k-check">check</span></label>
      <label class="kc"><input type="checkbox" data-k="review" checked> <span class="kb k-review">review</span></label>
      <select id="ann-author" title="Show only the comments of one author"><option value="">all authors</option></select>
    </div>
    <div id="annnew" hidden>
      <div class="hint" id="annnew-quote"></div>
      <div style="display:flex;gap:6px;margin:5px 0">
        <select id="annnew-kind"><option value="decide">decide</option><option value="info">info</option><option value="source">source</option><option value="check">check</option></select>
        <span class="hint" style="align-self:center">kind</span>
      </div>
      <textarea id="annnew-text" rows="3" placeholder="Your comment (⌘/Ctrl+Enter adds it)"></textarea>
      <div class="annact"><button id="annnew-add" class="primary">Add comment</button><button id="annnew-cancel">Cancel</button></div>
    </div>
    <div id="annexp" hidden>
      <div class="annact" style="margin:0 0 6px"><button id="annexp-copy">Copy</button><button id="annexp-dl">Download .md</button><button id="annexp-close">Close</button></div>
      <textarea id="annexp-text" readonly></textarea>
    </div>
    <div id="annimp" hidden>
      <div class="hint">Choose the comments file(s) your reader sent back (<code>comments-….json</code>), or paste what is in them.
        Each comment is placed in your text by its quote; one that cannot be found is kept as <i>detached</i> with the reader's quote.</div>
      <div style="margin:6px 0"><input type="file" id="annimp-files" accept=".json,application/json,text/plain" multiple></div>
      <textarea id="annimp-text" placeholder="…or paste the JSON here"></textarea>
      <div class="annact"><button id="annimp-go" class="primary">Import</button><button id="annimp-close">Close</button></div>
      <div id="annimp-res" class="hint" style="margin-top:6px"></div>
    </div>
    <div class="hint" id="annmsg" style="padding:0 10px"></div>
    <div id="annlist"></div>
  </aside>
</main>

<div id="sharedlg" hidden>
  <div id="sharebox" role="dialog" aria-modal="true" aria-label="Share for review">
    <div style="display:flex;align-items:center;gap:8px"><b style="font-size:15px">Share for review</b><span class="hint" id="share-title"></span>
      <span style="flex:1"></span><button id="share-x" title="Close (Esc)">✕</button></div>
    <p class="hint" style="margin:6px 0 0">Writes <b>one HTML file</b> that opens in any browser, with no internet and nothing to install: the chapter as a reading copy,
      a place to comment on any passage, and a button that saves the reviewer's comments to a small file they send back to you.</p>
    <div class="row"><b>Chapters to include</b><div id="share-files"></div></div>
    <div class="row"><label><b>Reviewer</b> <span class="hint">(optional, shown in the file and used as the author of their comments)</span>
      <input type="text" id="share-reviewer" maxlength="60" placeholder="e.g. Prof. Example"></label></div>
    <div class="row"><b>My comments in the file</b> <span class="hint">(shown read-only and labelled as the author's)</span>
      <label><input type="radio" name="share-inc" value="none" checked> none</label>
      <label><input type="radio" name="share-inc" value="ticked"> only those I ticked “show to reviewer” (<span id="share-n-ticked">0</span> in this file)</label>
      <label><input type="radio" name="share-inc" value="all"> all my open comments (<span id="share-n-open">0</span> in this file)</label></div>
    <div class="row"><label><b>Message to the reviewer</b> <textarea id="share-msg" rows="3" placeholder="Shown at the top of the file."></textarea></label></div>
    <div class="row"><label><input type="checkbox" id="share-pdf"> Include the typeset PDF <span class="hint" id="share-pdfinfo"></span></label></div>
    <div class="sharenote">Anyone who has this file can read the chapter (and your comments, if you include them). Send it only to the person it is for.
      texpad does not send it anywhere: you attach it to an email yourself. It makes no network request, and neither does the file.</div>
    <div class="annact"><button id="share-go" class="primary">Create review file</button><button id="share-close">Close</button></div>
    <div id="share-status"></div>
  </div>
</div>

<section id="xr" hidden>
  <div class="xrbar">
    <b>Cross-review</b> <span class="hint" id="xrfile"></span>
    <label class="hint">baseline <select id="xr-bmode">
      <option value="ref">git ref in folder</option><option value="current">current file</option></select></label>
    <span id="xr-bref" class="xrbar" style="padding:0;border:0">
      <input type="text" id="xr-bfolder" size="30" placeholder="folder (default: this project)">
      <input type="text" id="xr-bname" size="9" value="baseline" title="git ref (tag, branch or commit)">
    </span>
    <label class="hint">A <input type="text" id="xr-a" size="32" placeholder="/path/to/folder A"></label>
    <label class="hint">B <input type="text" id="xr-b" size="32" placeholder="/path/to/folder B"></label>
    <button id="xr-run" class="primary">Compare</button>
    <span style="flex:1"></span>
    <button id="xr-close">Close ✕</button>
  </div>
  <div id="xrsum"><span class="hint">Pick the baseline and one or two candidate folders, then Compare.
    Nothing is written until you press Apply.</span></div>
  <div class="xrbar" id="xrsuggbar" hidden>
    <b>Suggestions</b> <span class="hint" id="xrsuggtxt"></span>
    <span style="flex:1"></span>
    <label class="hint" title="'Lean' picks are weaker: a change nothing flagged, or one flagged only mildly. Off: Apply suggestions uses clear picks only."><input type="checkbox" id="xr-lean"> include lean picks</label>
    <button id="xr-sugg" title="Pre-select the suggested choice for every hunk that has a clear pick and that you have not chosen yourself. Green stays blocked; sources that disagree are left alone.">Apply suggestions</button>
    <button id="xr-imptoggle" title="Paste a reviewer's reply (JSON or Markdown table) to add its recommendations next to texpad's own rules">Import recommendations ▾</button>
  </div>
  <div class="xrbar" id="xrimp" hidden style="align-items:flex-start">
    <textarea id="xr-imptext" rows="5" style="flex:1 1 420px;min-width:0;font:12px/1.4 ui-monospace,Menlo,monospace"
      placeholder="Paste the reviewer's reply here: a JSON array [{&quot;from_line&quot;: 45, &quot;to_line&quot;: 46, &quot;pick&quot;: &quot;a&quot;, &quot;why&quot;: &quot;...&quot;, &quot;flag&quot;: &quot;none&quot;}], or a Markdown passage table with a Location column (L206-215) and a Recommendation column (TAKE CLAUDE, KEEP BASELINE, MERGE, NEEDS AUTHOR CHECK). Text around it is ignored."></textarea>
    <span style="display:flex;flex-direction:column;gap:6px;flex:0 1 280px">
      <input type="text" id="xr-impname" size="20" value="imported review" title="Label shown next to these suggestions">
      <span><button id="xr-impgo" class="primary">Import</button> <button id="xr-impclear">Remove import</button></span>
      <span class="hint" id="xr-impmsg"></span>
    </span>
  </div>
  <div class="xrbar" id="xrflt" hidden>
    <span class="hint">show</span>
    <label class="hint"><input type="checkbox" class="xr-col" data-c="g" checked> green</label>
    <label class="hint"><input type="checkbox" class="xr-col" data-c="b" checked> blue</label>
    <label class="hint"><input type="checkbox" class="xr-col" data-c="r" checked> red</label>
    <label class="hint"><input type="checkbox" class="xr-col" data-c="y" checked> yellow</label>
    <label class="hint"><input type="checkbox" class="xr-col" data-c="-" checked> unmarked</label>
    <label class="hint"><input type="checkbox" class="xr-col" data-c="edge" checked> edge</label>
    <select id="xr-state">
      <option value="all">all hunks</option><option value="a">only A changed</option>
      <option value="b">only B changed</option><option value="both">both changed</option>
      <option value="differ">both changed, differently</option><option value="blocked">touches green</option>
      <option value="unbal">unbalanced { } or \begin/\end (pair these)</option>
      <option value="sugg">has a recommendation</option>
      <option value="differs">differs from my choice</option>
      <option value="conflict">rules and import disagree</option>
    </select>
    <label class="hint"><input type="checkbox" id="xr-ws"> hide whitespace-only</label>
    <span style="flex:1"></span>
    <span class="hint" id="xrcount"></span>
    <button id="xr-afirst" title="For every visible hunk take A where A changed it, else B where B did (green stays blocked)">A first</button>
    <button id="xr-bfirst" title="For every visible hunk take B where B changed it, else A where A did (green stays blocked)">B first</button>
    <button id="xr-reset" title="Keep the baseline everywhere visible">Reset</button>
  </div>
  <div id="xrlist"></div>
  <div class="xrbar" id="xrfoot" hidden style="border-top:1px solid var(--line);border-bottom:0">
    <span class="hint" id="xrchosen"></span>
    <span style="flex:1"></span>
    <select id="xr-target">
      <option value="open">apply to the open file</option><option value="copy">write a new copy</option></select>
    <input type="text" id="xr-copy" size="34" placeholder="sections/02_background.merged.tex">
    <label class="hint" title="Text that comes from an applied hunk is marked yellow (changed by a tool, waiting for your review); it never becomes green on its own."><input type="checkbox" id="xr-yellow" checked> mark changes yellow</label>
    <button id="xr-apply" class="primary">Apply merge</button>
  </div>
  <div class="xrbar" id="xrchunkbar" hidden style="border-top:1px solid var(--line);border-bottom:0;padding-top:5px;padding-bottom:0">
    <span class="hint">hunk lists for the reviewer (paste after the prompt, one message each):</span>
    <span id="xrchunks" style="display:flex;gap:6px;flex-wrap:wrap"></span>
  </div>
  <div class="xrbar" style="border-top:1px solid var(--line);border-bottom:0">
    <button id="xr-prompt" title="Copy a ready-to-paste review prompt for your own Claude or Gemini session">Copy review prompt</button>
    <span class="hint" id="xrmsg" style="flex:1 1 300px"></span>
  </div>
  <textarea id="xrprompt" readonly hidden></textarea>
</section>

<script>
const $ = s => document.querySelector(s);
let cur = "__MAIN__", dirty = false, pages = 0, imgMode = false, timer = null;
let curMarks = [], prevText = "";   // highlight ranges for the open file

async function jget(u){ const r = await fetch(u); return r.json(); }
async function jpost(u,b){ const r = await fetch(u,{method:"POST",
  headers:{"Content-Type":"application/json"}, body:JSON.stringify(b)}); return r.json(); }

function setStatus(t, cls){ const s=$("#status"); s.textContent=t; s.className="pill "+(cls||""); }

// ---- line layout: gutter numbers + line positions, wrap-aware --------------
// With soft wrap a source line can span several screen rows, so the gutter
// can't print one number per row. #measure lays every line out at the
// textarea's exact width; each line's rendered height sizes its gutter number,
// and its offsetTop is that line's scroll position.
function layoutLines(){
  const t = $("#ed"), m = $("#measure");
  // The textarea's own vertical scrollbar narrows its text area; the overlay
  // and the mirror have none, so give them the same extra right padding or
  // they'd wrap at a different column than the text you see.
  const sb = t.offsetWidth - t.clientWidth;
  $("#hl").style.paddingRight = (12 + sb) + "px";
  m.style.width = t.offsetWidth + "px";
  m.style.paddingRight = (12 + sb) + "px";
  const lines = t.value.split("\n");
  m.innerHTML = lines.map(l => "<div>" + (esc(l) || " ") + "</div>").join("");
  const rows = m.children;
  let g = "";
  // fractional heights: offsetHeight rounds to whole pixels, and over a few
  // hundred lines that rounding adds up to the numbers drifting off their lines
  for(let i = 0; i < rows.length; i++)
    g += "<div style='height:" + rows[i].getBoundingClientRect().height + "px'>" + (i+1) + "</div>";
  $("#gutter").innerHTML = g + "<div style='height:" + t.clientHeight + "px'></div>";
  $("#gutter").scrollTop = t.scrollTop;
}
let layoutQueued = false;
function gutter(){           // coalesced to once per frame while typing
  if(layoutQueued) return; layoutQueued = true;
  requestAnimationFrame(()=>{ layoutQueued = false; layoutLines(); });
}
function lineTop(ln){        // y position of source line ln (1-based) in the editor
  layoutLines();
  const row = $("#measure").children[ln-1];
  return row ? row.offsetTop : 0;
}
function setWrap(on){
  document.body.classList.toggle("wrap", on);
  $("#wrap").checked = on;
  try{ localStorage.setItem("texpad.wrap", on ? "1" : "0"); }catch(e){}
  layoutLines(); renderHL();
}
$("#wrap").addEventListener("change", e=>setWrap(e.target.checked));
new ResizeObserver(()=>gutter()).observe($("#ed"));   // pane resized -> rewrap
$("#ed").addEventListener("scroll", ()=>{
  $("#gutter").scrollTop = $("#ed").scrollTop;
  $("#hl").scrollTop = $("#ed").scrollTop; $("#hl").scrollLeft = $("#ed").scrollLeft;
});

// ---- highlight marks: {start,end,color} character offsets into the file --
function renderHL(){
  const text = $("#ed").value;
  const marks = curMarks.slice().sort((a,b)=>a.start-b.start);
  let html = "", pos = 0;
  for(const m of marks){
    if(m.start < pos) continue;               // defensive: drop bad overlaps
    if(m.start > pos) html += esc(text.slice(pos, m.start));
    html += "<mark class='h"+m.color+"'>" + esc(text.slice(m.start, m.end)) + "</mark>";
    pos = m.end;
  }
  html += esc(text.slice(pos));
  $("#hl").innerHTML = html + "\n";            // trailing \n gives the last line height
}

// Keep every mark's {start,end} valid across an edit by diffing old vs new
// text (common prefix / common suffix) and re-mapping each endpoint through
// the edit, the same trick real code editors use for sticky decorations.
function adjustMarks(oldT, newT){
  if(!curMarks.length || oldT === newT) return;
  const maxCommon = Math.min(oldT.length, newT.length);
  let pre = 0; while(pre < maxCommon && oldT[pre] === newT[pre]) pre++;
  let suf = 0; const limit = maxCommon - pre;
  while(suf < limit && oldT[oldT.length-1-suf] === newT[newT.length-1-suf]) suf++;
  const oldMidEnd = oldT.length - suf, newMidEnd = newT.length - suf, delta = newT.length - oldT.length;
  const map = (p, isStart) => p<=pre ? p : p>=oldMidEnd ? p+delta : (isStart ? newMidEnd : pre);
  curMarks = curMarks.map(m => ({start: map(m.start,true), end: map(m.end,false), color: m.color}))
                     .filter(m => m.end > m.start);
}

function saveMarksNow(){ jpost("/api/save", {path:cur, text:$("#ed").value, marks:curMarks}); }

function setHighlight(color){
  const t = $("#ed"), s = t.selectionStart, e = t.selectionEnd;
  if(s === e) return;                          // nothing selected
  const next = [];
  for(const m of curMarks){
    if(m.end <= s || m.start >= e){ next.push(m); continue; }   // no overlap
    if(m.start < s) next.push({start:m.start, end:s, color:m.color});   // left remainder
    if(m.end > e)   next.push({start:e, end:m.end, color:m.color});     // right remainder
  }
  if(color) next.push({start:s, end:e, color});
  curMarks = next.sort((a,b)=>a.start-b.start);
  renderHL(); saveMarksNow();
  t.focus(); t.setSelectionRange(s, e);
}
document.querySelectorAll("#hlbar .sw").forEach(b=>{
  b.addEventListener("mousedown", ev=>ev.preventDefault());   // keep the selection alive
  b.addEventListener("click", ()=>setHighlight(b.dataset.c));
});
document.addEventListener("keydown", e=>{
  if(e.altKey && !e.metaKey && !e.ctrlKey && document.activeElement === $("#ed")){
    const map = {"1":"", "2":"y", "3":"r", "4":"g"};
    if(map[e.key] !== undefined){ e.preventDefault(); setHighlight(map[e.key]); }
  }
});

function onTextEdited(){
  const t = $("#ed"), newText = t.value;
  adjustMarks(prevText, newText);
  prevText = newText;
  dirty = true; gutter(); renderHL(); setStatus("unsaved");
}
$("#ed").addEventListener("input", onTextEdited);
$("#ed").addEventListener("keydown", e=>{
  if(e.key==="Tab"){ e.preventDefault();
    const t=e.target, s=t.selectionStart, n=t.selectionEnd;
    t.value=t.value.slice(0,s)+"  "+t.value.slice(n); t.selectionStart=t.selectionEnd=s+2;
    onTextEdited();
  }
});
document.addEventListener("keydown", e=>{
  if((e.metaKey||e.ctrlKey) && e.key.toLowerCase()==="s"){ e.preventDefault(); saveCompile(); }
});

async function loadFile(path){
  if(dirty && !confirm("Discard unsaved changes in "+cur+"?")) { $("#files").value = cur; return; }
  const d = await jget("/api/file?path="+encodeURIComponent(path));
  if(d.error){ alert(d.error); return; }
  cur = path; $("#ed").value = d.text; dirty=false; gutter(); setStatus("saved"); lastLine=-1;
  curMarks = d.marks || []; prevText = d.text; renderHL();
  const o = $("#outline"); o.innerHTML = "<option value=''>outline ("+d.outline.length+")</option>";
  d.outline.forEach(it=>{
    const op=document.createElement("option"); op.value=it.line;
    op.textContent = "  ".repeat(it.depth) + (it.depth?"· ":"") + it.title;
    o.appendChild(op);
  });
}
$("#files").addEventListener("change", e=>loadFile(e.target.value));
$("#outline").addEventListener("change", e=>{
  const ln = parseInt(e.target.value,10); if(!ln) return;
  const t=$("#ed"), pos = t.value.split("\n").slice(0,ln-1).join("\n").length+1;
  t.focus(); t.setSelectionRange(pos,pos);
  t.scrollTop = lineTop(ln) - 60;
});

const esc = s => s.replace(/[<>&]/g, c=>({"<":"&lt;",">":"&gt;","&":"&amp;"}[c]));

function showProblems(list){
  const box=$("#probs");
  if(!list || !list.length){ box.style.display="none"; box.innerHTML=""; return; }
  const errs = list.filter(p=>p.sev==="error");
  box.style.display="block";
  box.innerHTML =
    (errs.length ? "<div class='hdr e'>"+errs.length+" error"+(errs.length>1?"s":"")+"</div>" : "") +
    list.map(p=>"<div class='"+(p.sev==="error"?"e":"w")+"'>"+esc(p.text)+"</div>").join("");
  box.scrollTop = 0;
}

let sync = {page:0, box:null};

function pageBox(n){ return document.querySelector("#view .pg[data-p='"+n+"']"); }

async function renderPdf(){
  const v = $("#view"), keep = v.scrollTop;
  if(!imgMode){
    v.innerHTML = "<iframe src='/pdf?t="+Date.now()+"#zoom=page-width'></iframe>";
    return;
  }
  const stamp = Date.now();
  // Preload every page off-screen, then swap in one go: no flash, no scroll jump.
  const imgs = [];
  for(let i=1;i<=pages;i++){
    const im = new Image();
    im.src = "/page?n="+i+"&t="+stamp;
    im.alt = "page "+i;
    imgs.push(im.decode().catch(()=>{}).then(()=>im));
  }
  const loaded = await Promise.all(imgs);
  const frag = document.createDocumentFragment();
  loaded.forEach((im,i)=>{
    const w = document.createElement("div");
    w.className = "pg"; w.dataset.p = i+1;
    const hl = document.createElement("div"); hl.className = "hl";
    const no = document.createElement("div"); no.className = "pgno"; no.textContent = (i+1)+"/"+pages;
    w.appendChild(im); w.appendChild(hl); w.appendChild(no);
    frag.appendChild(w);
  });
  v.replaceChildren(frag);
  v.scrollTop = keep;
  if(sync.page) placeHighlight(sync.page, sync.box, false);
}

// ---- forward sync: caret in the editor -> page + highlighted box --------
function placeHighlight(page, box, scroll){
  document.querySelectorAll("#view .hl").forEach(h=>h.style.display="none");
  const w = pageBox(page); if(!w) return;
  const im = w.querySelector("img"), hl = w.querySelector(".hl");
  if(!im || !im.naturalWidth) return;
  const ptW = im.naturalWidth * 72/110, ptH = im.naturalHeight * 72/110;  // rendered at 110 dpi
  hl.style.left   = (100*box.x/ptW)+"%";
  hl.style.top    = (100*box.y/ptH)+"%";
  hl.style.width  = (100*box.w/ptW)+"%";
  hl.style.height = (100*box.h/ptH)+"%";
  hl.style.display = "block";
  if(scroll){
    const v = $("#view");
    const target = w.offsetTop + im.clientHeight*(box.y/ptH) - v.clientHeight*0.35;
    v.scrollTo({top: Math.max(0,target), behavior:"smooth"});
  }
}

function caretLine(){
  const t = $("#ed");
  return t.value.slice(0, t.selectionStart).split("\n").length;
}

let syncTimer = null, lastLine = -1;
function scheduleSync(){
  if(!imgMode || !$("#follow").checked) return;
  clearTimeout(syncTimer);
  syncTimer = setTimeout(async ()=>{
    const line = caretLine();
    if(line === lastLine) return;
    lastLine = line;
    const r = await jget("/api/sync?file="+encodeURIComponent(cur)+"&line="+line);
    if(!r || !r.page) return;
    sync = {page:r.page, box:r};
    placeHighlight(r.page, r, true);
  }, 220);
}
["keyup","click","input"].forEach(e=>$("#ed").addEventListener(e, scheduleSync));

// ---- reverse sync: click the PDF -> jump the editor ---------------------
$("#view").addEventListener("click", async ev=>{
  const im = ev.target.closest(".pg img"); if(!im) return;
  const w = im.parentElement, rect = im.getBoundingClientRect();
  const ptW = im.naturalWidth * 72/110, ptH = im.naturalHeight * 72/110;
  const x = (ev.clientX-rect.left)/rect.width  * ptW;
  const y = (ev.clientY-rect.top )/rect.height * ptH;
  const r = await jpost("/api/revsync",{page:+w.dataset.p, x, y});
  if(!r || !r.path) return;
  if(r.path !== cur) await loadFile(r.path);
  const t = $("#ed"), lines = t.value.split("\n");
  const start = lines.slice(0, r.line-1).join("\n").length + (r.line>1?1:0);
  t.focus();
  t.setSelectionRange(start, start + (lines[r.line-1]||"").length);
  t.scrollTop = lineTop(r.line) - t.clientHeight/2;
  $("#files").value = cur;
});

// At most one compile in flight from this page. Requests that arrive while
// one is running (auto-save fires on every pause in typing) collapse into a
// single follow-up run, so builds never queue up behind each other and the
// newest text always gets compiled last.
let compiling = false, compileAgain = false;
async function compile(){
  if(compiling){ compileAgain = true; return; }
  compiling = true;
  try{ await compileOnce(); }
  finally{
    compiling = false;
    if(compileAgain){ compileAgain = false; compile(); }
  }
}
async function compileOnce(){
  setStatus("compiling…","work");
  const r = await jpost("/api/compile",{});
  if(r.busy){            // another tab is compiling this project -- retry shortly
    compileAgain = true; await new Promise(res=>setTimeout(res, 1500)); return;
  }
  pages = r.pages||0;
  showProblems(r.problems);
  if(r.errors){
    setStatus(r.errors+" error"+(r.errors>1?"s":"")+(r.haspdf?" · showing last good output":""),"bad");
    if(r.haspdf) await renderPdf();
  } else if(r.haspdf){
    setStatus("compiled · "+pages+" pages","ok"); await renderPdf();
  } else {
    setStatus("no PDF produced","bad");
  }
}
async function saveCompile(){
  if(dirty){ const r=await jpost("/api/save",{path:cur,text:$("#ed").value,marks:curMarks});
             if(r.error){ alert(r.error); return; } dirty=false; }
  await compile();
}
$("#save").addEventListener("click", saveCompile);
$("#recompile").addEventListener("click", compile);

// ---- explicit git sync: what makes another device's edits/highlights show
// up here, and this device's edits/highlights show up elsewhere -----------
async function gitPull(){
  setStatus("Pulling…", "work");
  const r = await jpost("/api/pull", {});
  if(!r.ok){ setStatus("Pull failed: " + r.output, "bad"); return; }
  setStatus(r.output || "Already up to date.", "ok");
  await loadFile(cur);       // pick up whatever just came in for the open file
}
async function gitPush(){
  if(dirty){ await jpost("/api/save", {path:cur, text:$("#ed").value, marks:curMarks}); dirty=false; }
  setStatus("Pushing…", "work");
  const r = await jpost("/api/push", {message: "Edit from texpad"});
  setStatus(r.ok ? (r.output || "Pushed.") : "Push failed: " + r.output, r.ok ? "ok" : "bad");
}
$("#pull").addEventListener("click", gitPull);
$("#push").addEventListener("click", gitPush);
$("#ed").addEventListener("input", ()=>{
  if(!$("#auto").checked) return;
  clearTimeout(timer); timer=setTimeout(saveCompile, 1600);
});

// ---- cross-review: compare two candidate versions against a baseline ------
// This only SELECTS between versions that already exist on disk: texpad writes no
// prose of its own and calls no model. The server recomputes every hunk from disk
// on Compare and again on Apply, so this page just carries the author's choices.
const xr = {data:null, req:null, choice:{}, over:new Set(), user:new Set(), prompt:"", imp:{text:"", name:""}};
// xr.user = hunks whose choice the author made themselves: Apply suggestions never touches those.
const XRCLS = {g:"cg", b:"cb", y:"cy", r:"cr", edge:"cedge", "-":"cu"};
const XRNAME = {g:"green", b:"blue", y:"yellow", r:"red", "-":"unmarked", edge:"edge"};
const XRPREF = {bmode:"#xr-bmode", bfolder:"#xr-bfolder", bname:"#xr-bname", a:"#xr-a", b:"#xr-b"};
const xrClip = (t,n) => t.length > n ? t.slice(0,n) + "…" : t;
const xrVis = t => esc(t).replace(/\n/g, "↵\n");

function xrPrefs(save){      // remembered per browser; the page works without it
  for(const [k, sel] of Object.entries(XRPREF)){
    try{
      if(save) localStorage.setItem("texpad.xr."+k, $(sel).value);
      else { const v = localStorage.getItem("texpad.xr."+k); if(v !== null) $(sel).value = v; }
    }catch(e){}
  }
}
function xrMsg(t, cls){ const m = $("#xrmsg"); m.textContent = t; m.className = "hint " + (cls||""); }
function xrBaselineUi(){ $("#xr-bref").style.display = $("#xr-bmode").value === "ref" ? "flex" : "none"; }

async function xrOpen(){
  if(dirty){                  // the comparison reads the file from disk
    const r = await jpost("/api/save", {path:cur, text:$("#ed").value, marks:curMarks});
    if(r.error){ alert(r.error); return; }
    dirty = false; setStatus("saved");
  }
  xrPrefs(false); xrBaselineUi();
  const c = $("#xr-copy");
  if(!c.value || c.dataset.for !== cur){ c.value = cur.replace(/(\.[^./]+)$/, ".merged$1"); c.dataset.for = cur; }
  $("#xrfile").textContent = cur;
  $("#xr").hidden = false; document.body.classList.add("xropen");
  xrLoadPrompt();
}
function xrClose(){ xrPrefs(true); $("#xr").hidden = true; document.body.classList.remove("xropen"); }

function xrHideTools(){
  for(const id of ["#xrflt", "#xrfoot", "#xrsuggbar", "#xrchunkbar"]) $(id).hidden = true;
  $("#xrlist").innerHTML = "";
}
async function xrRun(keep){      // keep === true: re-compare (after an import) without losing the author's choices
  xrPrefs(true);
  const req = {file:cur, a:$("#xr-a").value.trim(), b:$("#xr-b").value.trim(),
    baseline:{mode:$("#xr-bmode").value, folder:$("#xr-bfolder").value.trim(), ref:$("#xr-bname").value.trim()},
    import_text:xr.imp.text, import_name:xr.imp.name};
  xrMsg("comparing…");
  const r = await jpost("/api/xr/compare", req);
  if(r.error){
    xr.data = null; xrHideTools();
    xrMsg(r.error, "bad"); return;
  }
  const same = keep === true && xr.data && xr.data.sig === r.sig;
  xr.data = r; xr.req = req;
  if(!same){ xr.choice = {}; xr.over = new Set(); xr.user = new Set(); }
  const open = $("#xr-target").querySelector("option[value=open]");
  open.disabled = !r.baseline.matches_open;
  if(open.disabled) $("#xr-target").value = "copy";
  xr.prompt = r.prompt; $("#xrprompt").value = r.prompt;     // now names the candidates
  xrSummary(); xrSuggBar(); xrChunks();
  $("#xrflt").hidden = $("#xrfoot").hidden = $("#xrsuggbar").hidden = false;
  xrRenderList();
  xrMsg(r.sites.length + " hunks. " + (r.baseline.matches_open ? ""
    : "The open file is not the baseline text, so Apply can only write a new copy."));
}

function xrCites(c){
  const f = o => Object.entries(o).map(([k,n]) => esc(k) + (n > 1 ? "×" + n : "")).join(", ");
  const add = Object.keys(c.cites_added).length, rem = Object.keys(c.cites_removed).length;
  return (add ? "added " + f(c.cites_added) : "") + (add && rem ? " · " : "") +
         (rem ? "removed " + f(c.cites_removed) : "") || "no change";
}
function xrSummary(){
  const d = xr.data;
  let h = "<div class='card'><b>baseline</b> " + esc(d.baseline.label) + " · " + d.baseline.chars +
    " chars · " + d.baseline.marks + " marks" +
    (d.baseline.note ? "<br><span class='bad'>" + esc(d.baseline.note) + "</span>" : "") +
    (d.baseline.live_marks_differ ? "<br><span class='bad'>The open file's marks differ from those at the ref; " +
       "green under either is protected.</span>" : "") + "</div>";
  for(const k of ["a","b"]){
    const c = d.candidates[k]; if(!c) continue;
    h += "<div class='card'><b>" + k.toUpperCase() + "</b> " + esc(c.folder) + "<br><span class='" +
      (c.green_violated ? "bad" : "ok") + "'>" + esc(c.verdict) + "</span> · green spans kept " +
      c.green_kept + " of " + c.green_total + (c.green_ws_only ? " (" + c.green_ws_only + " whitespace-only)" : "") +
      "<br>change blocks " + ["g","b","r","y","-","edge"].map(x =>
        "<span class='chip " + XRCLS[x] + "'>" + XRNAME[x] + " " + c.by_colour[x] + "</span>").join(" ") +
      "<br>citation keys " + xrCites(c) + "</div>";
  }
  $("#xrsum").innerHTML = h;
}

const xrUnbal = (s, k) => !!s[k+"_bal"] && (s[k+"_bal"][0] !== 0 || s[k+"_bal"][1] !== 0);
function xrFilter(){
  const on = new Set([...document.querySelectorAll(".xr-col")].filter(x => x.checked).map(x => x.dataset.c));
  const st = $("#xr-state").value, noWs = $("#xr-ws").checked;
  return s => on.has(s.colour) && !(noWs && s.ws) && (
    st === "all" || (st === "a" || st === "b" || st === "both" ? s.state === st
    : st === "differ" ? s.agree === "differ" : st === "unbal" ? xrUnbal(s, "a") || xrUnbal(s, "b")
    : st === "sugg" ? !!s.rule.pick || s.imports.length > 0
    : st === "differs" ? (() => { const p = xrCombinedPick(s); return p !== null && p !== (xr.choice[s.id] || "base"); })()
    : st === "conflict" ? s[xrLean() ? "plan_lean" : "plan_clear"].status === "conflict"
    : s.blocked_a || s.blocked_b));
}
const xrLean = () => $("#xr-lean").checked;
function xrCombinedPick(s){   // the pick the two sources agree on, as a radio value (a | b | base), or null
  const p = s[xrLean() ? "plan_lean" : "plan_clear"].pick;
  return p === "baseline" ? "base" : p;
}
const XRPICK = {a:"take A", b:"take B", baseline:"keep baseline", merge:"merge: your call", check:"needs author check"};
function xrSuggLine(src, imp, pick, text, why){
  const cls = pick === "a" || pick === "b" ? "take" : pick === "baseline" ? "keep" : "judge";
  return "<div class='ln'><span class='src" + (imp ? " imp" : "") + "'>" + esc(src) + "</span>" +
    (text ? "<span class='pk " + cls + "'>" + esc(text) + "</span>" : "") + "<span>" + esc(why) + "</span></div>";
}
function xrSuggHtml(s){       // one line per source, labelled; sources are never combined here
  const r = s.rule, out = [];
  if(r.pick) out.push(xrSuggLine("rules · " + r.rule, false, r.pick, "Suggest: " + XRPICK[r.pick] +
    (r.strength === "lean" ? " (lean)" : ""), r.why));
  else out.push(xrSuggLine("rules", false, "", "", r.why));
  for(const i of s.imports){
    const note = i.raw_pick !== i.pick ? " (" + XRPICK[i.raw_pick] + " = no change here)" : "";
    out.push(xrSuggLine("import · " + i.name, true, i.pick, "Suggest: " + XRPICK[i.pick] + note +
      (i.caveat ? " (with caveats)" : ""), (i.why || "") + (i.flag && i.flag !== "none" ? " [" + i.flag + "]" : "") +
      " · " + i.lines + " · " + i.passage));
  }
  if(s.plan_lean.status === "conflict")
    out.push("<div class='ln bad'>The sources suggest different picks: not combined, nothing is pre-selected.</div>");
  return "<div class='xrsug'>" + out.join("") + "</div>";
}
function xrFlagsHtml(s, k){
  const f = s["flags_" + k];
  return f.length ? "<div class='xrflags'>" + f.map(x => "<div class='fl " + x.sev + "'>⚑ " + esc(x.text) + "</div>").join("") + "</div>" : "";
}
function xrBalNote(s){       // a hunk that adds or removes a brace/environment without its partner
  return ["a", "b"].filter(k => xrUnbal(s, k)).map(k => {
    const [br, env] = s[k+"_bal"];
    return "⚠ " + k.toUpperCase() + " " + (br ? "{ } " + (br > 0 ? "+" : "") + br : "") +
           (env ? " \\begin/\\end " + (env > 0 ? "+" : "") + env : "");
  }).join("<br>");
}
function xrCell(s, kind){
  const txt = kind === "base" ? s.base : s[kind];
  if(txt === null) return "<i>unchanged</i>";
  return "<span class='ctx'>" + xrVis(s.before.slice(-28)) + "</span><mark class='" +
    (kind === "base" ? "del" : "ins") + "'>" + (txt === "" ? "<i>∅</i>" : xrVis(xrClip(txt, 400))) +
    "</mark><span class='ctx'>" + xrVis(s.after.slice(0, 28)) + "</span>";
}
function xrRow(s){
  const pick = xr.choice[s.id] || "base", ov = xr.over.has(s.id);
  const off = k => s[k+"_n"] === 0 || (s["blocked_"+k] && !ov);
  const star = xrCombinedPick(s);
  const radio = (v, label) => "<label" + (v !== "base" && off(v) ? " class='off'" : "") +
    "><input type='radio' name='xr" + s.id + "' value='" + v + "'" + (pick === v ? " checked" : "") +
    (v !== "base" && off(v) ? " disabled" : "") + "> " + label +
    (star === v ? " <span class='hint' title='The sources agree on this pick'>★</span>" : "") + "</label>";
  const blocked = s.blocked_a || s.blocked_b;
  const st = s.state === "a" ? "A only" : s.state === "b" ? "B only"
    : s.agree === "same" ? "A = B" : s.agree === "same_ws" ? "A ≈ B (spacing)" : "A ≠ B";
  return "<div class='xrrow" + (blocked ? " blk" : "") + "' data-id='" + s.id + "'>" +
    "<div><b>#" + s.id + "</b> L" + s.line + "<br><span class='chip " + XRCLS[s.colour] + "'>" +
    XRNAME[s.colour] + "</span><br><span class='hint'>" + st + (s.ws ? " · whitespace only" : "") + "</span>" +
    (xrBalNote(s) ? "<br><span class='bad' title='This hunk adds or removes a brace or environment that another hunk " +
       "probably closes. Take both together or neither.'>" + xrBalNote(s) + "</span>" : "") + "</div>" +
    "<div class='xrcell'>" + xrCell(s, "base") + "</div><div class='xrcell'>" + xrCell(s, "a") + xrFlagsHtml(s, "a") +
    "</div><div class='xrcell'>" + xrCell(s, "b") + xrFlagsHtml(s, "b") + "</div><div class='xrpick'>" +
    radio("base", "keep baseline") + radio("a", "take A" + (s.blocked_a ? " (green)" : "")) +
    radio("b", "take B" + (s.blocked_b ? " (green)" : "")) +
    (blocked ? "<label class='ov'><input type='checkbox' class='xr-ov'" + (ov ? " checked" : "") +
       "> override green</label>" : "") + "</div>" + xrSuggHtml(s) + "</div>";
}
function xrRenderList(){
  const d = xr.data; if(!d) return;
  const rows = d.sites.filter(xrFilter());
  $("#xrlist").innerHTML = "<div class='xrhead'><div>hunk</div><div>baseline</div><div>A</div><div>B</div>" +
    "<div>choose</div></div>" + rows.map(xrRow).join("");
  $("#xrcount").textContent = rows.length + " of " + d.sites.length + " hunks shown";
  xrChosen();
}
function xrChosen(){
  let a = 0, b = 0, o = 0;
  for(const [id, c] of Object.entries(xr.choice)){
    if(c === "a") a++; else if(c === "b") b++;
    if(c !== "base" && xr.over.has(+id) && xr.data.sites[id]["blocked_"+c]) o++;
  }
  $("#xrchosen").textContent = (a + b) + " hunk(s) chosen: A " + a + " · B " + b +
    (o ? " · " + o + " green override(s)" : "");
}
function xrBulk(first){       // first = "a" | "b" | null (reset); only hunks that are visible
  const d = xr.data; if(!d) return;
  const allowed = (s, k) => s[k+"_n"] > 0 && (!s["blocked_"+k] || xr.over.has(s.id));
  for(const s of d.sites.filter(xrFilter())){
    const other = first === "a" ? "b" : "a";
    xr.choice[s.id] = !first ? "base" : allowed(s, first) ? first : allowed(s, other) ? other : "base";
    if(first) xr.user.add(s.id); else xr.user.delete(s.id);    // a bulk button is the author's own choice
  }
  xrRenderList();
}
$("#xrlist").addEventListener("change", ev => {
  const row = ev.target.closest(".xrrow"); if(!row) return;
  const id = +row.dataset.id, s = xr.data.sites[id];
  if(ev.target.classList.contains("xr-ov")){
    if(ev.target.checked) xr.over.add(id);
    else {
      xr.over.delete(id);
      const c = xr.choice[id];
      if(c && c !== "base" && s["blocked_"+c]) xr.choice[id] = "base";
    }
    row.outerHTML = xrRow(s);
  } else if(ev.target.type === "radio"){ xr.choice[id] = ev.target.value; xr.user.add(id); }
  xrChosen();
});

async function xrApply(){
  const d = xr.data; if(!d) return;
  const target = $("#xr-target").value;
  if(!Object.values(xr.choice).some(c => c !== "base")){ xrMsg("Nothing chosen yet.", "bad"); return; }
  if(target === "open" && !confirm("Overwrite " + cur + " with the merged text?\n" +
     "The previous text and marks are copied to build/crossreview-backup/ first.")) return;
  xrMsg("applying…");
  const r = await jpost("/api/xr/apply", Object.assign({}, xr.req, {sig:d.sig, choices:xr.choice,
    overrides:[...xr.over], target:target, copy_path:$("#xr-copy").value.trim(),
    mark_yellow:$("#xr-yellow").checked}));
  if(r.error){ xrMsg(r.error, "bad"); return; }
  xr.data = null; xrHideTools();
  $("#xrsum").innerHTML = "<span class='ok'>Applied A " + r.hunks.a + " · B " + r.hunks.b + " hunk(s) to " +
    esc(r.path) + " (" + r.chars + " chars; marks " + r.marks_before + " → " + r.marks_after +
    ", green " + r.green_before + " → " + r.green_after + (r.override ? ", green override used" : "") + "). " +
    (r.yellow_spans ? r.yellow_spans + " span" + (r.yellow_spans > 1 ? "s" : "") + " marked yellow (" + r.yellow_chars +
       " characters): review them, then turn them green yourself." : "No text was marked yellow.") +
    (r.blue_spans ? " " + r.blue_spans + " span" + (r.blue_spans > 1 ? "s" : "") + " of rewritten text stayed blue: the decision is still yours." : "") +
    (r.comments && r.comments.carried + r.comments.detached ? " Comments: " + r.comments.carried + " followed the edits" +
       (r.comments.detached ? ", " + r.comments.detached + " detached (their text was replaced or not found)" : "") + "." : "") +
    (r.backup ? " Backup: " + esc(r.backup) + "." : "") + " Press Compare again to continue.</span>" +
    (r.warnings.length ? "<br><span class='bad'>⚠ " + r.warnings.map(esc).join("<br>⚠ ") + "</span>" : "");
  xrMsg("");
  if(r.target === "open"){ await loadFile(cur); if($("#auto").checked) compile(); }
  else if(![...$("#files").options].some(o => o.value === r.path)){
    const o = document.createElement("option"); o.value = o.textContent = r.path; $("#files").appendChild(o);
  }
}

// The prompt is fetched when the panel opens, so the click handler can write to the
// clipboard at once (browsers only allow that inside the click, not after a request).
async function xrLoadPrompt(){
  const r = await jget("/api/xr/prompt?file=" + encodeURIComponent(cur));
  xr.prompt = r.text || ""; $("#xrprompt").value = xr.prompt;
}
function xrCopyText(text, okMsg){
  const box = $("#xrprompt");
  const done = ok => {
    box.hidden = ok;
    xrMsg(ok ? okMsg : "The clipboard is not available here: the text is selected below, press ⌘C.", ok ? "ok" : "bad");
  };
  const fallback = () => {
    box.value = text; box.hidden = false; box.focus(); box.select();
    let ok = false; try{ ok = document.execCommand("copy"); }catch(e){}
    done(ok);
  };
  if(navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(text).then(() => done(true), fallback);
  else fallback();
}
function xrCopyPrompt(){
  if(!xr.prompt){ xrLoadPrompt(); xrMsg("Prompt not loaded yet - click again.", "bad"); return; }
  xrCopyText(xr.prompt, "Review prompt copied (" + xr.prompt.length + " characters). Paste it into your own Claude or " +
    "Gemini session, then the hunk lists below it, one message each.");
}

// ---- recommendations: texpad's own rules + whatever a reviewer answered ------
function xrSuggBar(){
  const d = xr.data, c = d.sugg[xrLean() ? "lean" : "clear"], need = c.judgement + c.conflict + c.decide;
  let t = c.suggested + " suggestion" + (c.suggested === 1 ? "" : "s") + ": " + c.a + " take A, " + c.b + " take B, " +
    c.baseline + " keep baseline; " + need + " need your judgement" +
    (c.conflict ? " (" + c.conflict + " where rules and import disagree)" : "") +
    (c.decide ? " (" + c.decide + " touch blue text: yours to decide)" : "") +
    (!xrLean() && c.lean ? "; " + c.lean + " more are lean picks (tick 'include lean picks')" : "");
  const i = d.import;
  if(i) t += " · import “" + i.name + "”: " + i.found + " of " + i.passages + " passages matched hunks" +
    (i.unmatched.length ? " (none for " + i.unmatched.map(u => u.lines).join("; ") + ")" : "") +
    (i.problems.length ? "; " + i.problems.length + " unreadable" : "");
  $("#xrsuggtxt").textContent = t;
}
function xrChunks(){
  const box = $("#xrchunks"); box.innerHTML = "";
  for(const c of xr.data.chunks){
    const b = document.createElement("button");
    b.textContent = "Copy hunks #" + c.from + "–" + c.to;
    b.title = c.count + " hunks in baseline line numbers, with the candidates' wording and rule flags";
    b.addEventListener("click", () => xrCopyText(c.text, "Hunks #" + c.from + "–" + c.to + " copied (" + c.text.length +
      " characters). Paste it after the review prompt and ask for the JSON array."));
    box.appendChild(b);
  }
  $("#xrchunkbar").hidden = !xr.data.chunks.length;
}
async function xrApplySugg(){
  const d = xr.data; if(!d) return;
  const r = await jpost("/api/xr/plan", Object.assign({}, xr.req, {user:[...xr.user], overrides:[...xr.over],
    include_lean:xrLean()}));
  if(r.error){ xrMsg(r.error, "bad"); return; }
  if(r.sig !== d.sig){ xrMsg("A file changed on disk since this comparison - press Compare again.", "bad"); return; }
  for(const [id, c] of Object.entries(r.choices)) xr.choice[id] = c;    // not marked as the author's own
  xrRenderList();
  const a = r.applied, k = r.skipped, n = a.a + a.b + a.baseline;
  xrMsg("Applied " + n + " suggestion" + (n === 1 ? "" : "s") + " (take A " + a.a + ", take B " + a.b + ", keep baseline " +
    a.baseline + "). Left alone: " + k.user + " you chose yourself, " + k.green + " blocked by green, " + k.conflict +
    " where the sources disagree, " + k.decide + " on blue text (yours to decide), " + (k.judgement + k.lean + k.none) + " without a clear pick.", "ok");
}
async function xrImport(clear){
  xr.imp = clear ? {text:"", name:""} : {text:$("#xr-imptext").value, name:$("#xr-impname").value.trim() || "imported review"};
  if(clear) $("#xr-imptext").value = "";
  await xrRun(true);
  const i = xr.data && xr.data.import, m = $("#xr-impmsg");
  m.className = "hint";
  if(!xr.data){ m.textContent = ""; return; }
  if(!i){ m.textContent = clear ? "Import removed." : "Nothing to import."; return; }
  m.textContent = i.records + " recommendation" + (i.records === 1 ? "" : "s") + " in " + i.passages + " passage" +
    (i.passages === 1 ? "" : "s") + ": " + i.found + " matched hunks" +
    (i.unmatched.length ? ", none for " + i.unmatched.map(u => u.passage + " (" + u.lines + ")").join("; ") : "") +
    (i.problems.length ? ". Unreadable: " + i.problems.slice(0, 3).join(" | ") : "") + ".";
  if(!i.records || i.problems.length) m.className = "hint bad";
}
$("#xrbtn").addEventListener("click", xrOpen);
$("#xr-close").addEventListener("click", xrClose);
$("#xr-run").addEventListener("click", xrRun);
$("#xr-bmode").addEventListener("change", xrBaselineUi);
$("#xr-apply").addEventListener("click", xrApply);
$("#xr-prompt").addEventListener("click", xrCopyPrompt);
$("#xr-afirst").addEventListener("click", () => xrBulk("a"));
$("#xr-bfirst").addEventListener("click", () => xrBulk("b"));
$("#xr-reset").addEventListener("click", () => xrBulk(null));
$("#xr-sugg").addEventListener("click", xrApplySugg);
$("#xr-lean").addEventListener("change", () => { if(xr.data){ xrSuggBar(); xrRenderList(); } });
$("#xr-imptoggle").addEventListener("click", () => { $("#xrimp").hidden = !$("#xrimp").hidden; });
$("#xr-impgo").addEventListener("click", () => xrImport(false));
$("#xr-impclear").addEventListener("click", () => xrImport(true));
document.querySelectorAll("#xrflt input, #xrflt select").forEach(e => e.addEventListener("change", xrRenderList));
document.addEventListener("keydown", e => {
  if(e.key !== "Escape") return;
  if(!$("#sharedlg").hidden) shareClose(); else if(!$("#xr").hidden) xrClose();
});

// ---- blue "decide" colour and comments (annotations) -------------------------
// Blue is just another mark colour (the marks code above is colour-agnostic); this block adds its swatch and
// shortcut. Comments are anchored to a span like a Google Docs comment and live in .texpad-annotations.json
// next to the marks; they are never written into the .tex source. The server owns them (/api/ann); the page
// keeps them in curAnns, moves their anchors through every edit with the very adjustMarks the highlights use,
// and writes the new positions back once the text is saved.
let curAnns = [], annPrev = "", annActive = null, annFlash = null, annNew = null, annForm = null, annSyncTimer = null;
const annFilter = {status:"open", author:"", kinds:{decide:true, info:true, source:true, check:true, review:true}};
const ANNKINDS = ["decide", "info", "source", "check", "review"];       // review = imported from a reviewer, not added by hand
const annDate = s => {                // a reviewer's time arrives as UTC (…Z): show it in local time like the author's own
  s = String(s || "");
  if(/Z$/.test(s)){ const d = new Date(s), p = n => String(n).padStart(2, "0");
    if(!isNaN(d)) return d.getFullYear() + "-" + p(d.getMonth() + 1) + "-" + p(d.getDate()) + " " + p(d.getHours()) + ":" + p(d.getMinutes()); }
  return s.replace("T", " ").slice(0, 16);
};
const annOpen = a => a.status !== "resolved";

function annMsg(t, bad){ const m = $("#annmsg"); m.textContent = t || ""; m.className = "hint " + (bad ? "bad" : ""); }

function adjustAnns(oldT, newT){      // anchors follow edits exactly like the marks: through adjustMarks itself
  if(!curAnns.length || oldT === newT) return;
  const live = curAnns.filter(a => a._anchor !== "detached"), saved = curMarks;
  curMarks = live.map((a, i) => ({start:a.start, end:a.end, color:String(i)}));
  let kept;
  try{ adjustMarks(oldT, newT); kept = new Map(curMarks.map(m => [m.color, m])); }
  finally{ curMarks = saved; }
  live.forEach((a, i) => {            // an anchor whose text was replaced entirely is detached, never deleted
    const m = kept.get(String(i));
    if(m){ a.start = m.start; a.end = m.end; } else { a._anchor = "detached"; a._lost = true; }
  });
}

function annRender(){                 // the underline layer over the text
  const al = $("#al"), t = $("#ed"); if(!al) return;
  const text = t.value, sb = t.offsetWidth - t.clientWidth;
  al.style.paddingRight = (12 + sb) + "px";
  const ok = curAnns.filter(a => a._anchor !== "detached" && a.end > a.start && a.end <= text.length);
  const cuts = new Set([0, text.length]);
  ok.forEach(a => { cuts.add(a.start); cuts.add(a.end); });
  const pts = [...cuts].sort((x, y) => x - y);
  let html = "";
  for(let i = 0; i < pts.length - 1; i++){
    const s = pts[i], e = pts[i + 1], cov = ok.filter(a => a.start <= s && a.end >= e), seg = esc(text.slice(s, e));
    if(!cov.length){ html += seg; continue; }
    const live = cov.filter(annOpen), top = live.find(a => a.kind === "decide") || live[0];
    const cls = !live.length ? "done" : top.kind === "decide" ? "decide" : "k-" + top.kind;
    html += "<span class='ac " + cls + (cov.some(a => a.id === annActive) ? " on" : "") +
            (cov.some(a => a.id === annFlash) ? " flash" : "") + "'>" + seg + "</span>";
  }
  al.innerHTML = html + "\n";
  al.scrollTop = t.scrollTop; al.scrollLeft = t.scrollLeft;
}

function annCounts(){
  const open = curAnns.filter(annOpen), dec = open.filter(a => a.kind === "decide").length;
  const lost = curAnns.filter(a => a._anchor === "detached").length, done = curAnns.length - open.length;
  const pill = $("#annpill");
  pill.textContent = "comments " + open.length + (dec ? " · " + dec + " decide" : "") + (lost ? " · " + lost + " detached" : "");
  pill.className = "pill " + (dec ? "work" : "");
  $("#anncount").textContent = open.length + " open · " + done + " resolved" + (lost ? " · " + lost + " detached" : "");
}

const annVisible = a => (annFilter.status === "all" || (annFilter.status === "open") === annOpen(a)) && annFilter.kinds[a.kind] !== false &&
  (!annFilter.author || a.author === annFilter.author);
function annCard(a){
  const done = !annOpen(a), lost = a._anchor === "detached", form = annForm && annForm.id === a.id ? annForm.mode : "";
  const reps = (Array.isArray(a.replies) ? a.replies : []).map(r => "<div class='annr'>" + annBadge(r.author || "?") + " <b>" + esc(String(r.author || "?")) +
    "</b> <span class='hint'>" + esc(annDate(r.created)) + "</span><br>" + esc(String(r.text || "")) + "</div>").join("");
  const kindSel = "<select class='annf-kind'>" + ANNKINDS.filter(k => k !== "review" || a.kind === "review").map(k => "<option" + (k === a.kind ? " selected" : "") + ">" + k + "</option>").join("") + "</select>";
  let body = "<div class='annt'>" + esc(String(a.text || "")) + "</div>" + reps;
  if(form === "reply") body += "<textarea class='annf-text' rows='2' placeholder='Reply'></textarea><div class='annact'><button data-act='send' class='primary'>Reply</button><button data-act='cancel'>Cancel</button></div>";
  else if(form === "edit") body = kindSel + "<textarea class='annf-text' rows='3'>" + esc(String(a.text || "")) + "</textarea>" + reps +
    "<div class='annact'><button data-act='save-edit' class='primary'>Save</button><button data-act='cancel'>Cancel</button></div>";
  else body += (a.kind !== "review" && !done ? "<label class='annsh' title='Include this comment, read-only, in the next review copy'><input type='checkbox' data-share" +
      (a.share ? " checked" : "") + "> show to reviewer</label>" : "") +
    "<div class='annact'><button data-act='reply'>Reply</button><button data-act='toggle'>" + (done ? "Reopen" : "Resolve") +
    "</button>" + (a.kind === "review" ? "" : "<button data-act='edit'>Edit</button>") + "<button data-act='delete'>Delete</button></div>";
  return "<div class='ann" + (done ? " done" : "") + (lost ? " lost" : "") + (a.id === annActive ? " on" : "") + "' data-id='" + esc(String(a.id)) + "'>" +
    "<div class='annmeta'>" + annBadge(a.author || "?") + "<span class='kb k-" + esc(String(a.kind || "info")) + "'>" + esc(String(a.kind || "info")) + "</span> <b>" +
    esc(String(a.author || "?")) + "</b> <span class='hint'>" + esc(annDate(a.created)) + (a._line ? " · L" + a._line : "") +
    (done ? " · resolved" : "") + "</span></div><div class='annq'>“" + esc(xrClip(String(a.quote || ""), 160)) + "”</div>" +
    (a.review && a.review.unmatched && lost ? "<div class='hint'>The reader's passage was not found in the current text; their quote is kept above.</div>" : "") + body + "</div>";
}
function annAuthorSelect(){
  const sel = $("#ann-author"), names = [...new Set(curAnns.map(a => String(a.author || "?")))].sort((x, y) => x.localeCompare(y));
  if(annFilter.author && !names.includes(annFilter.author)) annFilter.author = "";
  sel.innerHTML = "<option value=''>all authors</option>" + names.map(n => "<option value='" + escA(n) + "'" + (n === annFilter.author ? " selected" : "") + ">" + esc(n) + "</option>").join("");
}
function annPanelRender(){
  annAuthorSelect();
  const vis = curAnns.filter(annVisible);
  const anchored = vis.filter(a => a._anchor !== "detached").sort((x, y) => x.start - y.start);
  const lost = vis.filter(a => a._anchor === "detached");
  $("#annlist").innerHTML = anchored.map(annCard).join("") +
    (lost.length ? "<div class='hint' style='margin:8px 2px'>Detached: the anchored text was not found any more</div>" + lost.map(annCard).join("") : "") +
    (vis.length ? "" : "<p class='hint'>" + (curAnns.length ? "No comments match the filters."
      : "No comments on this file yet. Select text and press Comment (⌥M).") + "</p>");
}
function annPanel(show){ $("#anns").hidden = !show; }

async function annLoad(){
  const file = cur, r = await jget("/api/ann?file=" + encodeURIComponent(file));
  if(file !== cur) return;
  curAnns = r.error ? [] : r.annotations;
  annNew = annForm = annActive = null; $("#annnew").hidden = true; annMsg(r.error || "", !!r.error);
  if(curAnns.some(a => a._anchor === "moved")) annSyncSoon();      // persist the re-found positions
  annRender(); annCounts(); annPanelRender();
  annPanel(curAnns.some(annOpen));                                 // opens with the open comments visible
}

async function annSyncNow(){          // write the anchors' new positions (and refreshed quote/context) back
  clearTimeout(annSyncTimer); annSyncTimer = null;
  if(dirty || !curAnns.length) return;
  const t = $("#ed").value;
  const anchors = curAnns.filter(a => a._anchor !== "detached" && a.end > a.start).map(a => ({id:a.id, start:a.start, end:a.end,
    quote:t.slice(a.start, a.end), prefix:t.slice(Math.max(0, a.start - 40), a.start), suffix:t.slice(a.end, a.end + 40)}));
  const lost = curAnns.filter(a => a._lost).map(a => a.id);     // the text was removed here: do not re-anchor by a bare word
  if(anchors.length || lost.length) await jpost("/api/ann", {file:cur, op:"sync", anchors:anchors, detached:lost});
  curAnns.forEach(a => { delete a._lost; });
}
function annSyncSoon(){               // after the text is saved, so quote and file always agree
  clearTimeout(annSyncTimer);
  annSyncTimer = setTimeout(() => { if(dirty) annSyncSoon(); else annSyncNow(); }, 700);
}
function annTextChanged(){            // idempotent: the input event and the Tab key both end up here
  const nw = $("#ed").value; if(nw === annPrev) return;
  const lostBefore = curAnns.filter(a => a._anchor === "detached").length;
  adjustAnns(annPrev, nw); annPrev = nw;
  annRender(); annCounts(); if(curAnns.length) annSyncSoon();
  if(curAnns.filter(a => a._anchor === "detached").length !== lostBefore) annPanelRender();
}
$("#ed").addEventListener("input", annTextChanged);
const _onTextEdited = onTextEdited;
onTextEdited = function(){ _onTextEdited(); annTextChanged(); };
const _loadFile = loadFile;
loadFile = async function(path){
  await annSyncNow();                 // the positions of the file we are leaving
  const r = await _loadFile(path);
  annPrev = $("#ed").value; await annLoad();
  return r;
};
$("#ed").addEventListener("scroll", () => { const al = $("#al"); if(al){ al.scrollTop = $("#ed").scrollTop; al.scrollLeft = $("#ed").scrollLeft; } });
new ResizeObserver(() => annRender()).observe($("#ed"));

async function annPost(op, extra){
  await annSyncNow();
  const r = await jpost("/api/ann", Object.assign({file:cur, op:op, doc:$("#ed").value}, extra));
  if(r.error){ annMsg(r.error, true); return null; }
  curAnns = r.annotations; annForm = null; annMsg("");
  annRender(); annCounts(); annPanelRender();
  return r;
}
function annJump(id){
  const a = curAnns.find(x => x.id === id); if(!a) return;
  annActive = id;
  if(a._anchor !== "detached"){
    const t = $("#ed"), line = t.value.slice(0, a.start).split("\n").length;
    t.focus(); t.setSelectionRange(a.start, a.end);
    t.scrollTop = Math.max(0, lineTop(line) - t.clientHeight / 3);
    annFlash = id; setTimeout(() => { if(annFlash === id){ annFlash = null; annRender(); } }, 1500);
  } else annMsg("The text this comment was anchored to is not in the file any more.", true);
  annRender(); annPanelRender();
  const card = document.querySelector(".ann[data-id='" + id + "']"); if(card) card.scrollIntoView({block:"nearest"});
}
$("#annlist").addEventListener("click", async ev => {
  const card = ev.target.closest(".ann"); if(!card) return;
  const id = card.dataset.id, a = curAnns.find(x => x.id === id), btn = ev.target.closest("button");
  const sh = ev.target.closest("input[data-share]");
  if(sh){ await annPost("share", {id:id, value:sh.checked}); return; }
  if(!btn){ if(!ev.target.closest("textarea, select")) annJump(id); return; }
  const act = btn.dataset.act, val = () => (card.querySelector(".annf-text") || {}).value || "";
  if(act === "reply" || act === "edit"){ annForm = {id:id, mode:act}; annPanelRender();
    const f = document.querySelector(".ann[data-id='" + id + "'] .annf-text"); if(f) f.focus(); }
  else if(act === "cancel"){ annForm = null; annPanelRender(); }
  else if(act === "send"){ if(val().trim()) await annPost("reply", {id:id, text:val(), author:annAuthor}); }
  else if(act === "save-edit"){ if(val().trim()) await annPost("edit", {id:id, text:val(), kind:card.querySelector(".annf-kind").value}); }
  else if(act === "toggle") await annPost(annOpen(a) ? "resolve" : "reopen", {id:id});
  else if(act === "delete"){ if(confirm("Delete this comment and its replies?")) await annPost("delete", {id:id}); }
});

function annStartAdd(){               // select text, then Comment (or ⌥M)
  const t = $("#ed"), s = t.selectionStart, e = t.selectionEnd;
  if(s === e){ annPanel(true); annMsg("Select the text you want to comment on, then press Comment (⌥M).", true); return; }
  annNew = {start:s, end:e, quote:t.value.slice(s, e)};
  annPanel(true); annMsg("");
  $("#annnew-quote").textContent = "Comment on “" + xrClip(annNew.quote, 120) + "”";
  $("#annnew-text").value = ""; $("#annnew").hidden = false; $("#annnew-text").focus();
}
async function annSubmitNew(){
  if(!annNew) return;
  const text = $("#annnew-text").value, doc = $("#ed").value;
  if(!text.trim()){ annMsg("Write the comment first.", true); return; }
  let {start, end} = annNew;
  if(doc.slice(start, end) !== annNew.quote){               // the text moved while the box was open
    const i = doc.indexOf(annNew.quote);
    if(i < 0){ annMsg("The selected text changed: select it again.", true); return; }
    start = i; end = i + annNew.quote.length;
  }
  const r = await annPost("add", {start:start, end:end, kind:$("#annnew-kind").value, text:text, author:annAuthor});
  if(r){ annNew = null; $("#annnew").hidden = true; annActive = r.id; annFlash = r.id;
    annRender(); annPanelRender(); setTimeout(() => { annFlash = null; annRender(); }, 1500); }
}
async function annExport(){
  await annSyncNow();
  const r = await fetch("/api/ann/export?file=" + encodeURIComponent(cur)), md = await r.text();
  $("#annexp-text").value = md; $("#annexp").hidden = false;
}
function annCopyExport(){
  const box = $("#annexp-text"); box.focus(); box.select();
  const done = ok => annMsg(ok ? "Copied the comments list." : "Press ⌘C: the list is selected.", !ok);
  if(navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(box.value).then(() => done(true), () => { let ok = false; try{ ok = document.execCommand("copy"); }catch(e){} done(ok); });
  else { let ok = false; try{ ok = document.execCommand("copy"); }catch(e){} done(ok); }
}
function annDownloadExport(){
  const a = document.createElement("a");
  a.href = URL.createObjectURL(new Blob([$("#annexp-text").value], {type:"text/markdown"}));
  a.download = "comments-" + cur.replace(/[\/\\]/g, "_").replace(/\.[^.]*$/, "") + ".md";
  document.body.appendChild(a); a.click(); a.remove();
}

(function(){                          // header: counts pill and the Comment button
  const pill = document.createElement("span");
  pill.className = "pill"; pill.id = "annpill"; pill.textContent = "comments 0";
  pill.title = "The open comments of this file: click to show or hide them";
  pill.addEventListener("click", () => annPanel($("#anns").hidden));
  $("#status").before(pill);
  const b = document.createElement("button");
  b.id = "ann-add"; b.textContent = "Comment"; b.title = "Comment on the selected text (⌥M)";
  b.addEventListener("mousedown", ev => ev.preventDefault());       // keep the selection alive
  b.addEventListener("click", annStartAdd);
  $("#xrbtn").before(b);
  const al = document.createElement("div"); al.id = "al"; $("#hl").after(al);
})();
(function(){                          // the blue swatch, its shortcut, and the legend
  const bar = $("#hlbar"), sw = document.createElement("button");
  sw.className = "sw"; sw.dataset.c = "b"; sw.style.background = "#3b82f6";
  sw.title = "Decide here (⌥5): you have to decide this";
  sw.addEventListener("mousedown", ev => ev.preventDefault());
  sw.addEventListener("click", () => setHighlight("b"));
  bar.appendChild(sw);
  const q = document.createElement("button");
  q.className = "sw"; q.textContent = "?"; q.style.fontSize = "11px"; q.title = "Colour legend";
  q.addEventListener("mousedown", ev => ev.preventDefault());
  bar.appendChild(q);
  bar.title = "Highlight the selected text (⌥1 clear · ⌥2 revise · ⌥3 to-do · ⌥4 done · ⌥5 decide)";
  const lg = document.createElement("div"); lg.id = "legend"; lg.hidden = true;
  lg.innerHTML = "<b>Highlight colours</b> <span class='hint'>(select text, click a dot or press ⌥1–⌥5)</span><br>" +
    "<span class='chip'>white</span> no mark (⌥1)<br><span class='chip cy'>yellow</span> revise, or changed by a tool and waiting for your review (⌥2)<br>" +
    "<span class='chip cr'>red</span> to do (⌥3)<br><span class='chip cg'>green</span> done and frozen: tools may not change it (⌥4)<br>" +
    "<span class='chip cb'>blue</span> you decide here: not frozen, but nothing is decided for you (⌥5)<br>" +
    "<span class='hint'>Comments: underline = a comment is anchored there (thick blue = an open “decide”, teal = from a reviewer, faded = resolved).</span>";
  document.body.appendChild(lg);
  q.addEventListener("click", ev => { ev.stopPropagation(); lg.hidden = !lg.hidden; });
  document.addEventListener("click", ev => { if(!lg.hidden && !lg.contains(ev.target)) lg.hidden = true; });
})();
document.addEventListener("keydown", e => {
  if(!e.altKey || e.metaKey || e.ctrlKey) return;
  if(e.code === "Digit5" && document.activeElement === $("#ed")){ e.preventDefault(); setHighlight("b"); }
  else if(e.code === "KeyM"){ e.preventDefault(); annStartAdd(); }
});
$("#annnew-add").addEventListener("click", annSubmitNew);
$("#annnew-cancel").addEventListener("click", () => { annNew = null; $("#annnew").hidden = true; });
$("#annnew-text").addEventListener("keydown", e => {
  if((e.metaKey || e.ctrlKey) && e.key === "Enter"){ e.preventDefault(); annSubmitNew(); }
  else if(e.key === "Escape"){ annNew = null; $("#annnew").hidden = true; }
});
$("#ann-close").addEventListener("click", () => annPanel(false));
$("#ann-export").addEventListener("click", annExport);
$("#annexp-copy").addEventListener("click", annCopyExport);
$("#annexp-dl").addEventListener("click", annDownloadExport);
$("#annexp-close").addEventListener("click", () => { $("#annexp").hidden = true; });
$("#ann-status").addEventListener("change", e => { annFilter.status = e.target.value; annPanelRender(); });
$("#ann-author").addEventListener("change", e => { annFilter.author = e.target.value; annPanelRender(); });
document.querySelectorAll("#annfilter input[data-k]").forEach(c => c.addEventListener("change", () => { annFilter.kinds[c.dataset.k] = c.checked; annPanelRender(); }));
$("#ed").addEventListener("click", () => {                          // click the text to open its comment
  const t = $("#ed"); if(t.selectionStart !== t.selectionEnd) return;
  const p = t.selectionStart;
  const hit = curAnns.filter(a => a._anchor !== "detached" && a.start <= p && p < a.end).sort((x, y) => (x.end - x.start) - (y.end - y.start))[0];
  if(!hit) return;
  annActive = hit.id; annPanel(true); annRender(); annPanelRender();
  const card = document.querySelector(".ann[data-id='" + hit.id + "']"); if(card) card.scrollIntoView({block:"nearest"});
});

// ---- author name, sharing a review copy, importing the reviewer's comments ------------------------------
// The review copy is ONE self-contained HTML file the server writes into build/review/ (/api/review/share): texpad
// sends it nowhere and the file makes no request. What the reader writes comes back as a small JSON file that
// /api/review/import turns into comments of kind "review" in the same sidecar as the author's own; nothing is
// ever written into the .tex source.
const escA = s => esc(String(s == null ? "" : s)).replace(/"/g, "&quot;").replace(/'/g, "&#39;");
let annAuthor = "you";
function annInitials(n){
  const w = String(n || "?").trim().split(/[\s._-]+/).filter(Boolean);
  return (w.length > 1 ? w[0][0] + w[w.length - 1][0] : (w[0] || "?").slice(0, 2)).toUpperCase();
}
function annHue(n){ let h = 0; for(const c of String(n)) h = (h * 31 + c.codePointAt(0)) >>> 0; return h % 360; }
const annBadge = n => "<span class='av' style='background:hsl(" + annHue(n) + ",50%,38%)' title='" + escA(n) + "'>" + esc(annInitials(n)) + "</span>";

async function annWhoLoad(){
  try{ const r = await jget("/api/settings"); if(r && r.author) annAuthor = r.author; }catch(e){}
  $("#ann-who").value = annAuthor;
}
async function annWhoSave(){
  const v = $("#ann-who").value.trim(), m = $("#ann-whomsg");
  if(v === annAuthor || (!v && annAuthor === "you")) return;
  const r = await jpost("/api/settings", {author:v});
  if(r.error){ m.textContent = r.error; m.className = "hint bad"; return; }
  annAuthor = r.author || "you"; $("#ann-who").value = annAuthor;
  m.textContent = "saved"; m.className = "hint ok"; setTimeout(() => { m.textContent = ""; }, 2500);
}
$("#ann-who").addEventListener("change", annWhoSave);
$("#ann-who").addEventListener("keydown", e => { if(e.key === "Enter"){ e.preventDefault(); annWhoSave(); } });

function lsGet(k){ try{ return localStorage.getItem(k) || ""; }catch(e){ return ""; } }
function lsSet(k, v){ try{ localStorage.setItem(k, v); }catch(e){} }
async function saveIfDirty(){             // sharing and importing read the files from disk
  if(!dirty) return true;
  const r = await jpost("/api/save", {path:cur, text:$("#ed").value, marks:curMarks});
  if(r.error){ alert(r.error); return false; }
  dirty = false; setStatus("saved"); return true;
}
const mbText = n => (n / 1048576).toFixed(1) + " MB";

// -- Share for review
function shareClose(){ $("#sharedlg").hidden = true; }
async function shareOpen(){
  if(!await saveIfDirty()) return;
  await annSyncNow();
  const info = await jget("/api/review/info?file=" + encodeURIComponent(cur));
  if(info.error){ alert(info.error); return; }
  const files = Array.isArray(info.files) ? info.files : [];
  $("#share-files").innerHTML = files.map(f => "<label><input type='checkbox' value='" + escA(f) + "'" + (f === cur ? " checked" : "") + "> " + esc(f) + "</label>").join("") ||
    "<span class='hint'>no .tex files</span>";
  const first = document.querySelector("#share-files input:checked");
  if(first) setTimeout(() => first.parentElement.scrollIntoView({block:"nearest"}), 0);      // the open chapter may be far down the list
  const n = info.comments || {open:0, ticked:0};
  $("#share-n-ticked").textContent = n.ticked; $("#share-n-open").textContent = n.open;
  document.querySelector("input[name=share-inc][value=none]").checked = true;
  $("#share-reviewer").value = lsGet("texpad.reviewer"); $("#share-msg").value = lsGet("texpad.reviewmsg");
  const pdf = $("#share-pdf"), pi = $("#share-pdfinfo");
  if(info.pdf == null){ pdf.checked = false; pdf.disabled = true; pi.textContent = "(there is no compiled build/main.pdf yet: Save & compile first)"; }
  else if(info.pdf > info.pdf_max){ pdf.checked = false; pdf.disabled = true; pi.textContent = "(" + mbText(info.pdf) + " is over the " + mbText(info.pdf_max) + " limit)"; }
  else { pdf.disabled = false; pdf.checked = true; pi.textContent = "(" + mbText(info.pdf) + ", embedded in the file; the reader gets an “Open typeset PDF” button)"; }
  $("#share-title").textContent = info.title || "";
  $("#share-status").innerHTML = ""; $("#share-go").disabled = false;
  $("#sharedlg").hidden = false; $("#share-reviewer").focus();
}
async function shareGo(){
  const st = $("#share-status"), files = [...document.querySelectorAll("#share-files input:checked")].map(i => i.value);
  if(!files.length){ st.innerHTML = "<p class='bad'>Tick at least one chapter.</p>"; return; }
  const inc = (document.querySelector("input[name=share-inc]:checked") || {}).value || "none";
  const reviewer = $("#share-reviewer").value.trim(), message = $("#share-msg").value;
  lsSet("texpad.reviewer", reviewer); lsSet("texpad.reviewmsg", message);
  const go = $("#share-go"); go.disabled = true; st.innerHTML = "<p class='hint'>Making the review file…</p>";
  let r;
  try{ r = await jpost("/api/review/share", {files:files, include:inc, reviewer:reviewer, message:message, pdf:$("#share-pdf").checked}); }
  catch(e){ r = {error:String(e)}; }
  go.disabled = false;
  if(r.error){ st.innerHTML = "<p class='bad'>" + esc(r.error) + "</p>"; return; }
  const kb = r.bytes / 1024, size = kb >= 1024 ? (kb / 1024).toFixed(1) + " MB" : Math.round(kb) + " KB";
  st.innerHTML = "<div class='shareok'><b>Created</b> <code>" + esc(r.path) + "</code> (" + size + (r.replaced ? ", replaced the file from earlier today" : "") + ")<br>" +
    "<span class='hint'>" + esc(files.join(", ")) + " · " + (r.references || 0) + " references · " + (r.comments || 0) + " of your comments shown · " +
    (r.pdf ? "typeset PDF included" : "no PDF") + "</span><br>" +
    "<span class='hint'>Full path:</span> <code id='share-abs'>" + esc(r.abs) + "</code><div class='annact'>" +
    "<a class='dl' href='/api/review/download?name=" + encodeURIComponent(r.name) + "' download='" + escA(r.name) + "'>Download</a>" +
    "<button data-copy='" + escA(r.abs) + "'>Copy path</button></div>" +
    "<span class='hint'>Attach this one file to an email or message. When the reader sends back their <code>comments-….json</code>, use <b>Import reviewer comments</b> in the Comments panel.</span></div>" +
    (r.warnings || []).map(w => "<p class='bad' style='margin:6px 0 0'>" + esc(w) + "</p>").join("");
}
$("#sharebtn").addEventListener("click", shareOpen);
$("#share-go").addEventListener("click", shareGo);
$("#share-x").addEventListener("click", shareClose);
$("#share-close").addEventListener("click", shareClose);
$("#sharedlg").addEventListener("mousedown", ev => { if(ev.target === $("#sharedlg")) shareClose(); });
$("#share-status").addEventListener("click", ev => {
  const b = ev.target.closest("button[data-copy]"); if(!b) return;
  const done = ok => { b.textContent = ok ? "Copied" : "Select the path and press ⌘C"; };
  if(navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(b.dataset.copy).then(() => done(true), () => done(false));
  else done(false);
});

// -- Import reviewer comments
const readText = f => f.text ? f.text() : new Promise((res, rej) => { const fr = new FileReader(); fr.onload = () => res(String(fr.result)); fr.onerror = rej; fr.readAsText(f); });
function annImpOpen(){ annPanel(true); $("#annimp").hidden = false; $("#annimp-res").textContent = ""; }
async function annImpGo(){
  const res = $("#annimp-res");
  if(!await saveIfDirty()) return;
  await annSyncNow();
  const texts = [];
  try{ for(const f of $("#annimp-files").files) texts.push(await readText(f)); }
  catch(e){ res.innerHTML = "<span class='bad'>Could not read the file: " + esc(String(e)) + "</span>"; return; }
  const pasted = $("#annimp-text").value.trim(); if(pasted) texts.push(pasted);
  if(!texts.length){ res.innerHTML = "<span class='bad'>Choose a comments file or paste its contents first.</span>"; return; }
  res.textContent = "Importing…";
  const r = await jpost("/api/review/import", {texts:texts, file:cur});
  if(r.error){ res.innerHTML = "<span class='bad'>" + esc(r.error) + "</span>"; return; }
  const others = Object.keys(r.files || {}).filter(f => f !== cur);
  const items = (r.problems || []).concat(r.details || []);
  res.innerHTML = "<b class='" + (r.imported ? "ok" : "") + "'>" + r.imported + " imported, " + r.detached + " detached, " + r.skipped + " skipped</b>" +
    (others.length ? "<br>also in: " + esc(others.map(f => f + " (" + r.files[f] + ")").join(", ")) : "") +
    (items.length ? "<ul>" + [...new Set(items)].slice(0, 12).map(x => "<li>" + esc(x) + "</li>").join("") + "</ul>" : "");
  $("#annimp-files").value = ""; $("#annimp-text").value = "";
  annFilter.kinds.review = true; document.querySelector("#annfilter input[data-k=review]").checked = true;
  annNew = annForm = null; $("#annnew").hidden = true;
  const keep = $("#annimp-res").innerHTML;
  await annLoad(); $("#annimp").hidden = false; $("#annimp-res").innerHTML = keep;
}
$("#ann-import").addEventListener("click", annImpOpen);
$("#annimp-go").addEventListener("click", annImpGo);
$("#annimp-close").addEventListener("click", () => { $("#annimp").hidden = true; });

(async function init(){
  let wrapOn = true;                       // wrap is the default
  try{ wrapOn = localStorage.getItem("texpad.wrap") !== "0"; }catch(e){}
  document.body.classList.toggle("wrap", wrapOn); $("#wrap").checked = wrapOn;
  const s = await jget("/api/state");
  imgMode = !!s.tools.pdftoppm;
  const t = s.tools;
  $("#tools").textContent = t.latexmk ? "latexmk"+(t.biber?" + biber":" (no biber)")
                          : t.pdflatex ? "pdflatex"+(t.biber?" + biber":"")
                          : "no TeX found";
  $("#tools").className = "pill " + (t.latexmk||t.pdflatex ? "ok" : "bad");
  if(!s.git){
    $("#pull").disabled = true; $("#push").disabled = true;
    $("#pull").title = $("#push").title = "This folder isn't a git repository.";
  }
  const f=$("#files"); s.files.forEach(p=>{ const o=document.createElement("option");
    o.value=p; o.textContent=p; f.appendChild(o); });
  await annWhoLoad();
  await loadFile("__MAIN__");
  await compile();
})();
</script></body></html>
"""


# --------------------------------------------------------------------------
def main():
    global ROOT, MAIN
    ap = argparse.ArgumentParser(description="A tiny local Overleaf.")
    ap.add_argument("project", nargs="?", default=".", help="project directory")
    ap.add_argument("--main", default="main.tex", help="root .tex file")
    ap.add_argument("--port", type=int, default=8765)
    ap.add_argument("--no-open", action="store_true")
    a = ap.parse_args()

    ROOT = Path(a.project).expanduser().resolve()
    MAIN = a.main
    if not (ROOT / MAIN).exists():
        sys.exit(f"texpad: no {MAIN} in {ROOT}")

    tc = toolchain()
    print(f"texpad  ->  http://127.0.0.1:{a.port}")
    print(f"project : {ROOT}")
    print("tex     : " + (tc["latexmk"] or tc["pdflatex"] or "NONE FOUND -- see the app for install steps"))
    print("Ctrl-C to stop.\n")

    if not a.no_open:
        threading.Timer(0.8, lambda: webbrowser.open(f"http://127.0.0.1:{a.port}")).start()
    with Server(("127.0.0.1", a.port), Handler) as srv:
        try:
            srv.serve_forever()
        except KeyboardInterrupt:
            print("\nbye")


if __name__ == "__main__":
    mimetypes.init()
    main()
