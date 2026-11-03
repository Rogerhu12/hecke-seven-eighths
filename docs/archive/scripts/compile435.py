"""Compile this project's skeleton and its SkeletonInputs with Lean 4.35.

Direct `lean` invocations only: Lake keeps running its own build in the same
workspace, so outputs go to a separate directory and nothing under the
project's .lake is written. Incremental: a module is rebuilt when its source or
any rebuilt dependency changed. Failed modules block their dependents.

Usage: python -I compile435.py [target module, default HeckeSkeleton.Audit]
"""
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

AXIOM = Path(__file__).resolve().parent.parent
INPUTS = AXIOM / 'SkeletonInputs'
WORK = Path(os.environ.get('COMPILE435_WORK') or Path(__file__).resolve().parent / 'skel435')
OUT = WORK / 'out'
LOGS = WORK / 'logs'
TOOLCHAIN = Path(os.path.expanduser('~')) / '.elan' / 'toolchains' / 'leanprover--lean4---v4.35.0-rc3'
LEAN = TOOLCHAIN / 'bin' / 'lean.exe'
FLAGS = ['-DautoImplicit=false', '-DrelaxedAutoImplicit=false', '-j2']


def sha(data):
    return hashlib.sha256(data).hexdigest()


def lean_path():
    paths = [OUT, AXIOM / '.lake' / 'build' / 'lib' / 'lean',
             AXIOM / 'vendor' / 'class-field-theory' / '.lake' / 'build' / 'lib' / 'lean']
    for pkg in sorted((AXIOM / '.lake' / 'packages').iterdir()):
        lib = Path(os.path.realpath(pkg)) / '.lake' / 'build' / 'lib' / 'lean'
        if lib.is_dir():
            paths.append(lib)
    paths.append(TOOLCHAIN / 'lib' / 'lean')
    return os.pathsep.join(str(p) for p in paths)


def source(module):
    """Return (root, file) for modules compiled here, None for prebuilt ones."""
    if module.startswith('HeckeSkeleton.') or module.startswith('HeckeAxiom.'):
        return AXIOM, AXIOM / (module.replace('.', '/') + '.lean')
    candidate = INPUTS / (module + '.lean')
    if '.' not in module and candidate.is_file():
        return INPUTS, candidate
    return None


def imports(path):
    text = re.sub(r'/-.*?-/', '', path.read_text(encoding='utf-8-sig'), flags=re.S)
    return re.findall(r'^(?:public\s+)?(?:meta\s+)?import\s+(\S+)', text, re.M)


def main():
    if hasattr(sys.stdout, 'reconfigure'):
        sys.stdout.reconfigure(encoding='utf-8')
    target = sys.argv[1] if len(sys.argv) > 1 else 'HeckeSkeleton.Audit'
    OUT.mkdir(parents=True, exist_ok=True)
    LOGS.mkdir(parents=True, exist_ok=True)
    order, deps, seen = [], {}, set()

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        root, path = source(module)
        deps[module] = [d for d in imports(path) if source(d)]
        for d in deps[module]:
            visit(d)
        order.append(module)

    visit(target)
    stamps_file = WORK / 'stamps.json'
    stamps = json.loads(stamps_file.read_text(encoding='utf-8')) if stamps_file.is_file() else {}
    env = dict(os.environ, LEAN_PATH=lean_path(), LEAN_SYSROOT=str(TOOLCHAIN), LEAN_NUM_THREADS='2')
    status, results = {}, []
    for i, module in enumerate(order, 1):
        root, path = source(module)
        if any(status[d] != 'ok' for d in deps[module]):
            status[module] = 'blocked'
            results.append({'module': module, 'status': 'blocked',
                            'blocked_by': [d for d in deps[module] if status[d] != 'ok']})
            continue
        stamp = sha((sha(path.read_bytes()) + ''.join(stamps[d]['stamp'] for d in deps[module])).encode())
        stem = OUT / module.replace('.', '/')
        if stamps.get(module, {}).get('stamp') == stamp and Path(str(stem) + '.olean').is_file():
            status[module] = 'ok'
            results.append({'module': module, 'status': 'ok', 'reused': True})
            continue
        stem.parent.mkdir(parents=True, exist_ok=True)
        log = LOGS / (module + '.log')
        cmd = [str(LEAN), *FLAGS, '-R', str(root), '-o', str(stem) + '.olean', '-i', str(stem) + '.ilean', str(path)]
        start = time.time()
        with log.open('w', encoding='utf-8') as handle:
            code = subprocess.run(cmd, cwd=str(AXIOM), env=env, stdout=handle, stderr=subprocess.STDOUT).returncode
        seconds = round(time.time() - start, 1)
        status[module] = 'ok' if code == 0 else 'failed'
        row = {'module': module, 'status': status[module], 'seconds': seconds, 'log': str(log)}
        if code == 0:
            stamps[module] = {'stamp': stamp}
        else:
            stamps.pop(module, None)
            errors = [l for l in log.read_text(encoding='utf-8', errors='replace').splitlines() if 'error' in l]
            row['first_errors'] = errors[:8]
        results.append(row)
        print(f'[{i}/{len(order)}] {module}: {status[module]} ({seconds}s)', flush=True)
        stamps_file.write_text(json.dumps(stamps, indent=1), encoding='utf-8')
    counts = {s: sum(1 for r in results if r['status'] == s) for s in ('ok', 'failed', 'blocked')}
    summary = {'target': target, 'lean': str(LEAN), 'modules': len(order), 'counts': counts, 'results': results}
    (WORK / 'summary.json').write_text(json.dumps(summary, indent=1, ensure_ascii=False), encoding='utf-8')
    print(json.dumps(counts))
    for r in results:
        if r['status'] == 'failed':
            print('FAILED', r['module'])
            for e in r['first_errors']:
                print('   ', e[:300])
    return 0 if counts['failed'] == 0 and counts['blocked'] == 0 else 1


if __name__ == '__main__':
    raise SystemExit(main())
