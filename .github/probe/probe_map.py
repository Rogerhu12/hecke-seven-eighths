#!/usr/bin/env python3
"""Sorry-probe driver for the MOM_ENGINE_STEP error map (probe branch only).

This is NOT a proof and is never merged.  Each round builds the task target
with Lake (independent targets keep building after a failure), records every
`error:` with its file, line and declaration, and then replaces with `sorry`
ONLY the proof bodies of the theorem/lemma/example declarations that errored,
so that the next round reaches the modules downstream of them.  Statements,
definition bodies, structures, attributes and imports are never changed: an
error inside any of those is recorded as "unstubbable" and left in place.

A watcher samples the running `lean` processes, records their elapsed time
(the slowest modules), and kills a module that runs longer than
PROBE_KILL_AFTER seconds so the rest of the round can finish; such a module
is recorded as "slow", and before the next round every theorem/lemma proof
body of it is replaced with `sorry` so that its downstream modules are
reached too (a module that is still slow after that is skipped quickly).

usage: probe_map.py round N    (state and evidence live in probe-evidence/)
       probe_map.py analyse FILE LINE COL [MESSAGE] [--write]   (local test)
"""
from __future__ import annotations

import json
import os
import re
import signal
import subprocess
import sys
import threading
import time
from pathlib import Path

TARGET = '+HeckeSkeleton.Moments.MOM_ENGINE_STEP.Interface:olean'
ROOT = Path.cwd()
EV = ROOT / 'probe-evidence'
STATE = EV / 'state.json'
KILL_AFTER = int(os.environ.get('PROBE_KILL_AFTER', '1200'))
BUDGET = int(os.environ.get('PROBE_BUDGET_MIN', '320')) * 60
START = int(os.environ.get('PROBE_JOB_START', str(int(time.time()))))

ANSI = re.compile(r'\x1b\[[0-9;?]*[A-Za-z]')
HEAD = re.compile(r'^([✔✖⚠ℹ])\s+\[(\d+)/(\d+)\]\s+(\S+)\s+(\S+)(?:\s+\(([^)]*)\))?\s*$')
MSG = re.compile(r'^(error|warning|info|trace):\s?(.*)$')
LOC = re.compile(r'^(\S*?\.lean):(\d+):(\d+):\s?(.*)$')


def now() -> str:
    return time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())


def norm_src(path: str) -> str:
    i = path.find('HeckeSkeleton/')
    return path[i:] if i >= 0 else path


def module_of(src: str) -> str:
    return src[:-5].replace('/', '.') if src.endswith('.lean') else src


def parse_duration(text: str | None) -> float | None:
    if not text:
        return None
    total, found = 0.0, False
    for value, unit in re.findall(r'([\d.]+)\s*(ms|s|m|h)\b', text):
        found = True
        total += float(value) * {'ms': 0.001, 's': 1, 'm': 60, 'h': 3600}[unit]
    return total if found else None


def load_state() -> dict:
    if STATE.exists():
        return json.loads(STATE.read_text(encoding='utf-8'))
    return {'rounds': [], 'stubs': [], 'unstubbable': [], 'module_errors': [], 'slow': {},
            'killed': {}, 'finished': None}


def save_state(st: dict) -> None:
    EV.mkdir(parents=True, exist_ok=True)
    STATE.write_text(json.dumps(st, indent=1, ensure_ascii=False) + '\n', encoding='utf-8')


def set_output(**kw) -> None:
    out = os.environ.get('GITHUB_OUTPUT')
    if out:
        with open(out, 'a') as f:
            for k, v in kw.items():
                f.write(f'{k}={v}\n')


# --------------------------------------------------------------------------
# lean process watcher

def lean_procs():
    try:
        out = subprocess.run(['ps', '-ww', '-eo', 'pid=,etimes=,rss=,args='],
                             capture_output=True, text=True, timeout=30).stdout
    except Exception:
        return []
    res = []
    for line in out.splitlines():
        parts = line.split(None, 3)
        if len(parts) < 4:
            continue
        pid, et, rss, args = parts
        argv = args.split()
        if not argv or os.path.basename(argv[0]) != 'lean':
            continue
        src = next((a for a in argv[1:] if a.endswith('.lean')), None)
        if src is None:
            continue
        res.append((int(pid), int(et), int(rss), norm_src(src)))
    return res


class Watcher(threading.Thread):
    def __init__(self, log_path: Path, known_slow: set[str]):
        super().__init__(daemon=True)
        self.log_path = log_path
        self.known_slow = known_slow
        self.stop = threading.Event()
        self.max_elapsed: dict[str, int] = {}
        self.max_rss: dict[str, int] = {}
        self.killed: dict[str, int] = {}

    def run(self):
        last_log = 0.0
        with self.log_path.open('w', encoding='utf-8') as log:
            while not self.stop.is_set():
                procs = lean_procs()
                for pid, et, rss, src in procs:
                    self.max_elapsed[src] = max(self.max_elapsed.get(src, 0), et)
                    self.max_rss[src] = max(self.max_rss.get(src, 0), rss)
                    limit = 5 if src in self.known_slow else KILL_AFTER
                    if et > limit and src not in self.killed:
                        try:
                            os.kill(pid, signal.SIGKILL)
                            self.killed[src] = et
                            log.write(f'{now()} KILL {src} after {et}s (limit {limit}s)\n')
                            print(f'PROBE killed slow module {src} after {et}s', flush=True)
                        except ProcessLookupError:
                            pass
                if time.time() - last_log >= 60:
                    last_log = time.time()
                    log.write(f'{now()} ' + '; '.join(
                        f'{src} {et}s {rss // 1024}MB' for _, et, rss, src in sorted(
                            procs, key=lambda p: -p[1])) + '\n')
                    log.flush()
                self.stop.wait(15)


# --------------------------------------------------------------------------
# Lake log parsing

def parse_log(path: Path) -> dict:
    modules: dict[str, dict] = {}
    errors: list[dict] = []
    cur_module = None
    cur = None

    def flush():
        nonlocal cur
        if cur is not None:
            cur['message'] = '\n'.join(cur.pop('lines'))[:6000]
            errors.append(cur)
            cur = None

    with path.open(encoding='utf-8', errors='replace') as f:
        for raw in f:
            line = ANSI.sub('', raw.rstrip('\n').rstrip('\r'))
            m = HEAD.match(line)
            if m:
                flush()
                sym, _, _, verb, name, dur = m.groups()
                cur_module = name
                modules[name] = {'symbol': sym, 'verb': verb, 'seconds': parse_duration(dur)}
                continue
            m = MSG.match(line)
            if m:
                flush()
                kind, rest = m.groups()
                if kind == 'error':
                    loc = LOC.match(rest)
                    if loc:
                        cur = {'module': cur_module, 'file': norm_src(loc[1]), 'line': int(loc[2]),
                               'col': int(loc[3]), 'lines': [loc[4]]}
                    else:
                        cur = {'module': cur_module, 'file': None, 'line': None, 'col': None,
                               'lines': [rest]}
                continue
            if line.startswith('Some required targets logged failures') or line.startswith('Build completed'):
                flush()
                cur_module = None
                continue
            if cur is not None and len(cur['lines']) < 60:
                cur['lines'].append(line)
    flush()
    return {'modules': modules, 'errors': errors}


# --------------------------------------------------------------------------
# Lean source scanning and proof stubbing

OPEN = '([{⟨⦃⟦'
CLOSE = ')]}⟩⦄⟧'
BOUNDARY = re.compile(
    r'^(?:/--|/-!|@\[|theorem\b|lemma\b|example\b|def\b|abbrev\b|instance\b|structure\b|class\b|'
    r'inductive\b|opaque\b|axiom\b|private\b|protected\b|noncomputable\b|nonrec\b|partial\b|'
    r'unsafe\b|end\b|namespace\b|section\b|variable\b|universe\b|open\b|include\b|omit\b|'
    r'attribute\b|set_option\b|#|mutual\b|export\b|local\b|scoped\b|macro\b|macro_rules\b|'
    r'syntax\b|notation\b|infix\b|infixl\b|infixr\b|prefix\b|postfix\b|elab\b|initialize\b|'
    r'deriving\b|irreducible_def\b|alias\b|suppress_compilation\b|unseal\b|seal\b|import\b)')
DECL = re.compile(
    r'(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped|local)\s+)*'
    r'(theorem|lemma|example|def|abbrev|instance|structure|class|inductive|opaque|axiom|'
    r'irreducible_def|alias)\b\s*([^\s(\[{:⦃]*)')
STUBBABLE = {'theorem', 'lemma', 'example'}


def scan(text: str):
    """Return (code, depth, ctx): code[i] is True when text[i] is code (not in a
    comment or string); depth[i] is the bracket depth before text[i]; ctx[i] is
    the lexical state before text[i] (0 code, 1 line comment, 2 block comment,
    3 string)."""
    n = len(text)
    code = [False] * n
    depth = [0] * n
    ctx = [0] * n
    i, d, block = 0, 0, 0
    in_line = in_str = False

    def mark(j, state):
        if j < n:
            depth[j] = d
            ctx[j] = state

    while i < n:
        c = text[i]
        mark(i, 1 if in_line else 2 if block else 3 if in_str else 0)
        if in_line:
            if c == '\n':
                in_line = False
            i += 1
            continue
        if block:
            if text.startswith('/-', i):
                block += 1
                mark(i + 1, 2)
                i += 2
                continue
            if text.startswith('-/', i):
                block -= 1
                mark(i + 1, 2)
                i += 2
                continue
            i += 1
            continue
        if in_str:
            if c == '\\':
                mark(i + 1, 3)
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if text.startswith('--', i):
            in_line = True
            i += 1
            continue
        if text.startswith('/-', i):
            block = 1
            mark(i + 1, 2)
            i += 2
            continue
        if c == '"':
            in_str = True
            i += 1
            continue
        code[i] = True
        if c in OPEN:
            d += 1
        elif c in CLOSE:
            d = max(0, d - 1)
        i += 1
    return code, depth, ctx


def is_word_at(text: str, i: int, word: str) -> bool:
    if not text.startswith(word, i):
        return False
    before = text[i - 1] if i > 0 else ' '
    after = text[i + len(word)] if i + len(word) < len(text) else ' '

    def ident(ch: str) -> bool:
        return ch.isalnum() or ch in "_'.!?"
    return not ident(before) and not ident(after)


class Source:
    def __init__(self, path: Path):
        self.path = path
        self.text = path.read_bytes().decode('utf-8')
        self.nl = '\r\n' if '\r\n' in self.text else '\n'
        self.lines = self.text.splitlines(keepends=True)
        self.offsets = [0]
        for ln in self.lines:
            self.offsets.append(self.offsets[-1] + len(ln))
        self.code, self.depth, self.ctx = scan(self.text)
        self.boundaries = []
        for k, ln in enumerate(self.lines):
            off = self.offsets[k]
            if ln[:1].strip() and off < len(self.text) and self.ctx[off] == 0 \
                    and self.depth[off] == 0 and BOUNDARY.match(ln):
                self.boundaries.append(k)

    def pos(self, line: int, col: int) -> int:
        k = max(0, min(line - 1, len(self.lines) - 1))
        return self.offsets[k] + min(col, max(0, len(self.lines[k].rstrip('\r\n'))))

    def line_of(self, off: int) -> int:
        lo, hi = 0, len(self.lines) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if self.offsets[mid] <= off:
                lo = mid
            else:
                hi = mid - 1
        return lo

    def code_line(self, k: int) -> bool:
        a, z = self.offsets[k], self.offsets[k + 1]
        return any(self.code[j] and not self.text[j].isspace() for j in range(a, z))

    def enclosing(self, line: int):
        k0 = line - 1
        prev = [b for b in self.boundaries if b <= k0]
        if not prev:
            return None
        b = prev[-1]
        nxt = [x for x in self.boundaries if x > b]
        return b, (nxt[0] if nxt else len(self.lines))

    def analyse(self, line: int, col: int, message: str) -> dict:
        """Classify an error position.  Stubbable results carry 'sep' (offset
        just after the top-level ':=', or of a top-level alternative/where)
        and 'end' (end offset of the proof text)."""
        rng = self.enclosing(line)
        if rng is None:
            return {'decl': None, 'kind': 'outside', 'stubbable': False, 'reason': 'before first command'}
        b, e = rng
        start, stop = self.offsets[b], self.offsets[e]
        head = self.lines[b]
        m = DECL.match(head)
        if not m:
            return {'decl': head.strip()[:80], 'kind': 'command', 'stubbable': False,
                    'reason': 'error is not inside a declaration', 'decl_line': b + 1}
        kind, name = m.group(1), m.group(2) or m.group(1)
        info = {'decl': name, 'kind': kind, 'decl_line': b + 1, 'stubbable': False}
        top = [i for i in range(start + m.end(), stop) if self.code[i] and self.depth[i] == 0]
        sep = sep_kind = None
        pending = 0  # top-level `let`/`have` binders in the statement own the next `:=`
        for i in top:
            if any(is_word_at(self.text, i, w) for w in ('let', 'have', 'letI', 'haveI')):
                pending += 1
                continue
            if self.text.startswith(':=', i):
                if pending:
                    pending -= 1
                    continue
                sep, sep_kind = i + 2, ':='
                break
            if is_word_at(self.text, i, 'where'):
                sep, sep_kind = i, 'where'
                break
        if sep is None:
            for i in top:
                k = self.line_of(i)
                if self.text[i] == '|' and k > b and self.text[self.offsets[k]:i].strip() == '' \
                        and '=>' in self.lines[k]:
                    sep, sep_kind = i, '|'
                    break
        if sep is None:
            info['reason'] = 'no proof separator found'
            return info
        info['sep_kind'] = sep_kind
        header_end = sep - 2 if sep_kind == ':=' else sep
        err = self.pos(line, col)
        if err < header_end and not message.startswith('(kernel)'):
            info['reason'] = 'error is in the statement/header'
            return info
        if kind not in STUBBABLE:
            info['reason'] = f'error is inside a {kind} body (definition bodies are never changed)'
            return info
        k = e - 1
        while k > self.line_of(sep) and (not self.lines[k].strip() or not self.code_line(k)):
            k -= 1
        end = self.offsets[k] + len(self.lines[k].rstrip('\r\n'))
        if sep_kind != 'where' and any(is_word_at(self.text, i, 'where') for i in top if sep <= i < end):
            info['reason'] = 'proof has a where-clause (auxiliary declarations); stub manually'
            return info
        info.update(stubbable=True, sep=sep, end=end)
        return info

    def stub(self, infos: list[dict]) -> str:
        text = self.text
        for info in sorted({i['sep']: i for i in infos}.values(), key=lambda i: -i['sep']):
            sep, end = info['sep'], info['end']
            if info['sep_kind'] == ':=':
                text = text[:sep] + ' by' + self.nl + '  sorry' + text[end:]
            else:
                text = text[:sep].rstrip() + ' := by' + self.nl + '  sorry' + text[end:]
        return text


def stub_slow_module(rel: str, rnd: int) -> list[dict]:
    """Stub every theorem/lemma proof body of a module killed as slow."""
    path = ROOT / rel
    if not path.exists():
        return []
    src = Source(path)
    infos = []
    for b in src.boundaries:
        m = DECL.match(src.lines[b])
        if not m or m.group(1) not in STUBBABLE:
            continue
        nxt = [x for x in src.boundaries if x > b]
        last = nxt[0] if nxt else len(src.lines)
        info = src.analyse(last, len(src.lines[last - 1]), '')
        if info['stubbable']:
            infos.append(info)
    if not infos:
        return []
    path.write_bytes(src.stub(infos).encode('utf-8'))
    return [{'round': rnd, 'file': rel, 'module': module_of(rel), 'decl': i['decl'],
             'kind': i['kind'], 'decl_line': i['decl_line']} for i in infos]


def stub_errors(errors: list[dict], rnd: int):
    by_file: dict[str, list[dict]] = {}
    for err in errors:
        by_file.setdefault(err['file'], []).append(err)
    new_stubs, unstubbable = [], []
    for rel, errs in sorted(by_file.items()):
        path = ROOT / rel
        if not path.exists():
            for err in errs:
                err.update(decl=None, kind='missing-file', stubbable=False)
                unstubbable.append(err)
            continue
        src = Source(path)
        todo: dict[int, tuple[dict, list[dict]]] = {}
        for err in errs:
            info = src.analyse(err['line'], err['col'], err['message'])
            err.update({k: v for k, v in info.items() if k not in ('sep', 'end')})
            if info['stubbable']:
                todo.setdefault(info['sep'], (info, []))[1].append(err)
            else:
                unstubbable.append(err)
        if todo:
            path.write_bytes(src.stub([v[0] for v in todo.values()]).encode('utf-8'))
            for info, errs2 in todo.values():
                new_stubs.append({'round': rnd, 'file': rel, 'module': module_of(rel),
                                  'decl': info['decl'], 'kind': info['kind'],
                                  'decl_line': info['decl_line'],
                                  'errors': [{'line': x['line'], 'col': x['col'],
                                              'first': x['message'].split('\n')[0][:300]}
                                             for x in errs2]})
    return new_stubs, unstubbable


# --------------------------------------------------------------------------
# rounds

def run_build(rd: Path, timeout: int, known_slow: set[str]):
    watcher = Watcher(rd / 'processes.log', known_slow)
    watcher.start()
    cmd = ['timeout', '--signal=TERM', '--kill-after=60s', f'{timeout}s', 'lake', 'build', TARGET]
    t0 = time.time()
    shown = 0
    with (rd / 'build.log').open('w', encoding='utf-8') as log:
        log.write(json.dumps({'command': cmd, 'started': now()}) + '\n')
        p = subprocess.Popen(cmd, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             text=True, encoding='utf-8', errors='replace')
        assert p.stdout is not None
        for line in p.stdout:
            log.write(line)
            log.flush()
            clean = ANSI.sub('', line).rstrip()
            if clean.startswith('✖') or clean.startswith('error:'):
                print(clean[:300], flush=True)
            elif HEAD.match(clean) and 'MOM_ENGINE_STEP' in clean:
                shown += 1
                if shown % 25 == 0:
                    print(f'{now()} {clean[:200]}', flush=True)
        code = p.wait()
    watcher.stop.set()
    watcher.join(timeout=30)
    return code, time.time() - t0, watcher


def write_summary(st: dict) -> None:
    lines = ['# MOM_ENGINE_STEP sorry-probe summary', '',
             'This is a sorry-probe used only to expose errors; it is not a fix.', '',
             f"finished: {st.get('finished')}", '']
    for r in st['rounds']:
        lines.append(f"- round {r['round']}: exit {r['exit']}, {r['minutes']:.1f} min, "
                     f"ok MOM modules {r['mom_ok']}, failed modules {len(r['failed'])}, "
                     f"located errors {r['errors']}, new stubs {r['new_stubs']}, "
                     f"unstubbable {r['unstubbable']}, killed {len(r['killed'])}")
    lines += ['', '## Stubbed (erroring proof bodies replaced by sorry)', '']
    for s in st['stubs']:
        e = s['errors'][0]
        lines.append(f"- r{s['round']} {s['file']}:{s['decl_line']} `{s['decl']}` ({len(s['errors'])} errors; "
                     f"first {e['line']}:{e['col']} {e['first'][:160]})")
    lines += ['', '## Unstubbable errors (left in place)', '']
    for u in st['unstubbable']:
        first = u['message'].splitlines()[0][:200] if u.get('message') else ''
        lines.append(f"- r{u['round']} {u.get('file')}:{u.get('line')}:{u.get('col')} decl `{u.get('decl')}` "
                     f"[{u.get('kind')}] {u.get('reason', '')}: {first}")
    lines += ['', '## Module-level errors without a location', '']
    for u in st['module_errors']:
        lines.append(f"- r{u['round']} {u.get('module')}: {u['message'][:200]}")
    lines += ['', '## Proofs of slow modules stubbed so that their downstream builds', '']
    for s in st.get('slow_stubs', []):
        lines.append(f"- r{s['round']} {s['file']}:{s['decl_line']} `{s['decl']}`")
    lines += ['', '## Killed as slow', '']
    for src, info in st['killed'].items():
        lines.append(f'- {src}: {info}')
    lines += ['', '## Slowest modules (max observed lean process / Lake build time, s)', '']
    for src, sec in sorted(st['slow'].items(), key=lambda kv: -kv[1])[:40]:
        lines.append(f'- {src}: {sec}')
    (EV / 'summary.md').write_text('\n'.join(lines) + '\n', encoding='utf-8')


def do_round(n: int) -> int:
    st = load_state()
    if st.get('finished'):
        print(f'probe already finished: {st["finished"]}')
        set_output(ran='false')
        return 0
    remaining = START + BUDGET - time.time()
    if remaining < 900:
        st['finished'] = 'out-of-time'
        save_state(st)
        write_summary(st)
        set_output(ran='false')
        return 0
    rd = EV / f'round-{n}'
    rd.mkdir(parents=True, exist_ok=True)
    known_slow = {src for src, info in st['killed'].items()
                  if 'stubbed_round' not in info or 'killed_after_stub' in info}
    print(f'PROBE round {n}: build budget {int(remaining - 300)}s, known slow {sorted(known_slow)}',
          flush=True)
    code, elapsed, watcher = run_build(rd, int(remaining - 300), known_slow)
    res = parse_log(rd / 'build.log')
    failed = sorted(m for m, v in res['modules'].items() if v['symbol'] == '✖')
    mom_ok = sum(1 for m, v in res['modules'].items()
                 if v['symbol'] != '✖' and 'MOM_ENGINE_STEP' in m)
    for src, et in watcher.max_elapsed.items():
        st['slow'][src] = max(st['slow'].get(src, 0), et)
    for m, v in res['modules'].items():
        if v['seconds'] and v['verb'] in ('Built', 'Building') and m.startswith('HeckeSkeleton'):
            src = m.replace('.', '/') + '.lean'
            st['slow'][src] = max(st['slow'].get(src, 0), int(v['seconds']))
    for src, et in watcher.killed.items():
        info = st['killed'].setdefault(src, {'round': n, 'elapsed': et})
        if info.get('stubbed_round', n) < n:
            info['killed_after_stub'] = n
    located = [e for e in res['errors'] if e['file'] is not None and e['line'] is not None]
    unlocated = [e for e in res['errors'] if e['file'] is None
                 and not e['message'].startswith('build failed')]
    for e in located + unlocated:
        e['round'] = n
    st['module_errors'] += unlocated
    new_stubs, unstubbable = stub_errors(located, n)
    st['stubs'] += new_stubs
    slow_stubs = []
    for src, info in st['killed'].items():
        if 'stubbed_round' not in info:
            info['stubbed_round'] = n
            slow_stubs += stub_slow_module(src, n)
    st.setdefault('slow_stubs', []).extend(slow_stubs)

    def key(u):
        # line numbers shift when other proofs of the same file were stubbed
        return (u.get('file'), u.get('decl'), u.get('kind'), (u.get('message') or '').split('\n')[0])
    seen = {key(u) for u in st['unstubbable']}
    unstubbable = [u for u in unstubbable if key(u) not in seen]
    st['unstubbable'] += unstubbable
    (rd / 'errors.json').write_text(json.dumps(located + unlocated, indent=1, ensure_ascii=False) + '\n',
                                    encoding='utf-8')
    (rd / 'modules.json').write_text(json.dumps(res['modules'], indent=0, ensure_ascii=False) + '\n',
                                     encoding='utf-8')
    st['rounds'].append({'round': n, 'exit': code, 'minutes': elapsed / 60, 'mom_ok': mom_ok,
                         'failed': failed, 'errors': len(located), 'new_stubs': len(new_stubs),
                         'unstubbable': len(unstubbable), 'killed': sorted(watcher.killed),
                         'slow_stubs': len(slow_stubs)})
    if code == 0 and not failed:
        st['finished'] = 'clean'
    elif code in (124, 137):
        st['finished'] = 'out-of-time'
    elif not new_stubs and not slow_stubs:
        st['finished'] = 'stuck: only unstubbable errors or slow modules remain'
    save_state(st)
    diff = subprocess.run(['git', 'diff', '--', 'HeckeSkeleton'], cwd=ROOT, capture_output=True).stdout
    (EV / 'stubs.patch').write_bytes(diff)
    write_summary(st)
    print((EV / 'summary.md').read_text(encoding='utf-8'), flush=True)
    set_output(ran='true')
    return 0


def main() -> int:
    if len(sys.argv) == 3 and sys.argv[1] == 'round':
        return do_round(int(sys.argv[2]))
    if len(sys.argv) == 4 and sys.argv[1] == 'mark':
        # diagnostic copy: a stderr marker command before every declaration
        src = Source(Path(sys.argv[2]))
        starts = {}
        for idx, b in enumerate(src.boundaries):
            m = DECL.match(src.lines[b])
            if not m:
                continue
            j = idx
            while j > 0 and src.lines[src.boundaries[j - 1]].startswith(('/--', '@[')) \
                    and not DECL.match(src.lines[src.boundaries[j - 1]]):
                j -= 1
            starts[src.boundaries[j]] = f'{b + 1} {m.group(1)} {m.group(2)}'
        out = []
        for k, ln in enumerate(src.lines):
            if k in starts:
                out.append(f'#eval IO.eprintln "PROBE_MARK before line {starts[k]}"{src.nl}')
            out.append(ln)
        out.append(f'{src.nl}#eval IO.eprintln "PROBE_MARK end of file"{src.nl}')
        Path(sys.argv[3]).write_bytes(''.join(out).encode('utf-8'))
        return 0
    if len(sys.argv) >= 5 and sys.argv[1] == 'analyse':
        src = Source(Path(sys.argv[2]))
        msg = sys.argv[5] if len(sys.argv) > 5 and sys.argv[5] != '--write' else ''
        info = src.analyse(int(sys.argv[3]), int(sys.argv[4]), msg)
        print(info)
        if info.get('stubbable') and sys.argv[-1] == '--write':
            src.path.write_bytes(src.stub([info]).encode('utf-8'))
        return 0
    print(__doc__)
    return 2


if __name__ == '__main__':
    sys.exit(main())
