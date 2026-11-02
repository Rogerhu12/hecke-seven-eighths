#!/usr/bin/env python3
"""Build one MOM_ENGINE_STEP group on top of the statement skeleton.

The branch cloud/mom-engine-step-skeleton holds every STEP module that is not
yet on dtests-handoff as its skeleton (see skeleton.py).  A group pull request
into that branch restores the real proofs of the modules listed in
.github/groups/<group>.txt, and this script builds exactly those modules.

It fails when a group module does not build, or when a group file contains
`sorry`, `admit`, `native_decide` or an `axiom` declaration.  It also lists
group files whose statements or definitions differ from the frozen interface
(.github/groups/interface.json); those changes must be announced on PR #9.
A module whose Lean process runs longer than GROUP_KILL_AFTER seconds is
killed and reported as slow.  On the skeleton branch itself every listed
module is built and the sorry check is skipped.

Evidence (build log, errors, summary) goes to group-build/.
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path.cwd()
GROUPS = ROOT / '.github/groups'
EV = ROOT / 'group-build'
sys.path.insert(0, str(GROUPS))
import skeleton  # noqa: E402

pm = skeleton.pm
pm.KILL_AFTER = int(os.environ.get('GROUP_KILL_AFTER', '1200'))
FORBIDDEN = re.compile(r'\b(sorry|admit|native_decide)\b|^\s*(?:private\s+|protected\s+)?axiom\b', re.M)


def group_name() -> str:
    if os.environ.get('GROUP'):
        return os.environ['GROUP']
    head = os.environ.get('GITHUB_HEAD_REF') or os.environ.get('GITHUB_REF_NAME', '')
    m = re.search(r'-(g\d+)$', head)
    return m.group(1) if m else 'all'


def group_files(name: str) -> list[str]:
    lists = sorted(GROUPS.glob('g*.txt')) if name == 'all' else [GROUPS / f'{name}.txt']
    return [ln.strip() for p in lists for ln in p.read_text(encoding='utf-8').splitlines() if ln.strip()]


def forbidden(path: str) -> list[str]:
    text = Path(path).read_bytes().decode('utf-8')
    code, _, _ = pm.scan(text)
    masked = ''.join(ch if code[i] else (ch if ch == '\n' else ' ') for i, ch in enumerate(text))
    return [f'{path}:{masked.count(chr(10), 0, m.start()) + 1}: {m.group(0).strip()}'
            for m in FORBIDDEN.finditer(masked)]


def main() -> int:
    name = group_name()
    files = group_files(name)
    modules = [pm.module_of(f) for f in files]
    EV.mkdir(exist_ok=True)
    print(f'group {name}: {len(files)} modules', flush=True)

    bad = [] if name == 'all' else [hit for f in files for hit in forbidden(f)]
    iface = json.loads((GROUPS / 'interface.json').read_text(encoding='utf-8'))
    changed = [f for f in files if iface.get(f) != skeleton.fingerprint(Path(f).read_bytes().decode('utf-8'))]
    if name == 'all':
        changed = []

    watcher = pm.Watcher(EV / 'processes.log', set())
    watcher.start()
    cmd = ['lake', 'build', *(f'+{m}:olean' for m in modules)]
    t0 = time.time()
    with (EV / 'build.log').open('w', encoding='utf-8') as log:
        p = subprocess.Popen(cmd, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             text=True, encoding='utf-8', errors='replace')
        for line in p.stdout:
            log.write(line)
            clean = pm.ANSI.sub('', line).rstrip()
            if clean.startswith(('✖', 'error:')):
                print(clean[:300], flush=True)
        code = p.wait()
    watcher.stop.set()
    watcher.join(timeout=30)
    res = pm.parse_log(EV / 'build.log')
    mine = set(modules)
    failed = sorted(m for m, v in res['modules'].items() if v['symbol'] == '✖')
    errors = [e for e in res['errors'] if not (e['message'] or '').startswith('build failed')]
    (EV / 'errors.json').write_text(json.dumps(errors, indent=1, ensure_ascii=False) + '\n', encoding='utf-8')

    lines = [f'# Group {name}: {len(files)} modules, lake exit {code}, {(time.time() - t0) / 60:.1f} min', '']
    lines += [f'- failed group modules: {len([m for m in failed if m in mine])}',
              f'- failed modules outside the group (skeleton problems): {len([m for m in failed if m not in mine])}',
              f'- slow modules killed: {len(watcher.killed)}',
              f'- forbidden tokens in group files: {len(bad)}',
              f'- group files whose statements/definitions differ from the frozen interface: {len(changed)}', '']
    lines += ['## Errors', '']
    for e in errors:
        tag = '' if e.get('module') in mine else ' (outside the group)'
        first = (e['message'] or '').split('\n')[0][:200]
        lines.append(f"- {e.get('file') or e.get('module')}:{e.get('line')}:{e.get('col')}{tag} {first}")
    lines += ['', '## Killed as slow', ''] + [f'- {s}: {t}s' for s, t in watcher.killed.items()]
    lines += ['', '## Forbidden tokens', ''] + [f'- {b}' for b in bad]
    lines += ['', '## Interface changes (announce on PR #9)', ''] + [f'- {c}' for c in changed]
    slow = sorted(watcher.max_elapsed.items(), key=lambda kv: -kv[1])[:15]
    lines += ['', '## Slowest modules (s)', ''] + [f'- {s}: {t}' for s, t in slow]
    summary = '\n'.join(lines) + '\n'
    (EV / 'summary.md').write_text(summary, encoding='utf-8')
    print(summary, flush=True)
    if os.environ.get('GITHUB_STEP_SUMMARY'):
        with open(os.environ['GITHUB_STEP_SUMMARY'], 'a', encoding='utf-8') as fh:
            fh.write(summary)
    return 0 if code == 0 and not failed and not bad and not watcher.killed else 1


if __name__ == '__main__':
    sys.exit(main())
