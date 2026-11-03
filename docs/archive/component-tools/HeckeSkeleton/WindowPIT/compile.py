"""Build one Lake module at a time in dependency order with LEAN_NUM_THREADS=4.

Lake owns every compiled artifact and its cache. This script writes only plans,
logs and receipts under .build; it never calls lean.exe or uses .build/out.
"""
from __future__ import annotations
import argparse
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
WORK = HERE / '.build'
LOGS = WORK / 'lake-logs'
TAUCETI = ROOT / '.lake/packages/TauCeti'
LAKE = shutil.which('lake')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source(name):
    if name == 'HeckeSkeleton.WindowPIT' or name.startswith('HeckeSkeleton.WindowPIT.'):
        return ROOT, ROOT / (name.replace('.', '/') + '.lean')
    if name.startswith('TauCeti.'):
        return TAUCETI, TAUCETI / (name.replace('.', '/') + '.lean')
    return None


def imports(path):
    body = re.sub(r'/-.*?-/', '', path.read_text(encoding='utf-8-sig'), flags=re.S)
    return re.findall(r'^(?:public\s+)?(?:meta\s+)?import\s+(\S+)', body, re.M)


def shared_paths():
    paths = [ROOT / '.lake/build/lib/lean',
             ROOT / 'vendor/class-field-theory/.lake/build/lib/lean']
    paths += [p.resolve() / '.lake/build/lib/lean'
              for p in sorted((ROOT / '.lake/packages').iterdir())]
    return paths


def prebuilt(name):
    for directory in shared_paths():
        path = directory / (name.replace('.', '/') + '.olean')
        if path.is_file():
            return path
    return None


@contextmanager
def compiler_slot():
    """Only one Lake build or audit may run through this task's scripts."""
    WORK.mkdir(parents=True, exist_ok=True)
    with (WORK / 'compiler.lock').open('a+b') as handle:
        if handle.tell() == 0:
            handle.write(b'0')
            handle.flush()
        while True:
            handle.seek(0)
            try:
                if os.name == 'nt':
                    import msvcrt
                    msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
                else:
                    import fcntl
                    fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except OSError:
                time.sleep(0.1)
        try:
            yield
        finally:
            handle.seek(0)
            if os.name == 'nt':
                import msvcrt
                msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                import fcntl
                fcntl.flock(handle, fcntl.LOCK_UN)


def resource_failure(body):
    low = body.lower()
    return ('failed to read file' in low and '.olean' in low) or any(token in low for token in [
        'out of memory', 'not enough memory', 'insufficient memory', 'failed to allocate',
        'allocation failed', 'commitment limit', 'paging file is too small', '内存不足', '页面文件太小'])


def run_lake(command, label, path, module=None, retry_delay=180, resource_retries=3, cwd=ROOT):
    if LAKE is None:
        raise FileNotFoundError('lake was not found on PATH')
    LOGS.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_NUM_THREADS='4')
    # Let Lake select only its official workspace/package artifacts.
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SYSROOT', None)
    for attempt in range(resource_retries + 1):
        suffix = '' if attempt == 0 else f'.retry-{attempt}'
        log = LOGS / (label + suffix + '.log')
        start = time.monotonic()
        with compiler_slot(), log.open('w', encoding='utf-8') as output:
            code = subprocess.run([LAKE, *command], cwd=cwd, env=env,
                                  stdout=output, stderr=subprocess.STDOUT).returncode
        body = log.read_text(encoding='utf-8', errors='replace')
        artifact = prebuilt(module) if module and code == 0 else None
        if module and code == 0 and artifact is None:
            raise FileNotFoundError('Lake reported success but the official olean is missing: ' + module)
        receipt = {'module': module, 'source': str(path), 'source_sha256': digest(path),
                   'command': ['lake', *command], 'lean_num_threads': 4, 'attempt': attempt,
                   'exit_code': code, 'seconds': round(time.monotonic() - start, 1),
                   'artifact': str(artifact) if artifact else None,
                   'artifact_sha256': digest(artifact) if artifact else None, 'log': str(log)}
        log.with_suffix('.json').write_text(json.dumps(receipt, indent=2), encoding='utf-8')
        print(json.dumps(receipt), flush=True)
        if code == 0:
            if module is None or 'PIT_' in body:
                # Cached Lake warnings can occupy thousands of lines. Keep
                # the full log on disk and show just the audit evidence here.
                for line in body.splitlines():
                    if 'PIT_' in line or ('depends on axioms:' in line and 'HeckeSkeleton.' in line):
                        print(line, flush=True)
            return
        if not resource_failure(body) or attempt == resource_retries:
            print('\n'.join(body.splitlines()[-45:]), flush=True)
            raise SystemExit(code)
        print(f'RESOURCE_RETRY {label}: waiting {retry_delay}s before retry {attempt + 1}', flush=True)
        remaining = retry_delay
        while remaining:
            delay = min(30, remaining)
            time.sleep(delay)
            remaining -= delay
            print(f'RETRY_WAIT {label}: {remaining}s remaining', flush=True)


def main():
    if hasattr(sys.stdout, 'reconfigure'):
        sys.stdout.reconfigure(encoding='utf-8')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('modules', nargs='*')
    parser.add_argument('--check', type=Path, help='Typecheck a temporary audit via lake env lean')
    parser.add_argument('--plan', action='store_true')
    parser.add_argument('--retry-delay', type=int, default=180)
    parser.add_argument('--resource-retries', type=int, default=3)
    args = parser.parse_args()
    if args.retry_delay < 0 or args.resource_retries < 0:
        parser.error('Retry settings must be nonnegative')
    seen, visiting, order = set(), set(), []

    def visit(name, explicit=False):
        if name in seen:
            return
        if name in visiting:
            raise ValueError('Import cycle at ' + name)
        own_source = source(name)
        if own_source is None:
            # Lake resolves the pinned toolchain's own modules, which do not
            # live in a workspace or dependency package build directory.
            if name in {'Init', 'Lean', 'Lake'} or name.startswith(('Init.', 'Lean.', 'Lake.')):
                seen.add(name)
                return
            if prebuilt(name) is None:
                raise FileNotFoundError('Precompiled dependency missing: ' + name)
            seen.add(name)
            return
        if name.startswith('TauCeti.') and not explicit and prebuilt(name) is not None:
            seen.add(name)
            return
        root, path = own_source
        if not path.is_file():
            raise FileNotFoundError(path)
        visiting.add(name)
        for dep in imports(path):
            visit(dep)
        visiting.remove(name)
        seen.add(name)
        order.append((name, root, path))

    for module in args.modules:
        visit(module, explicit=True)
    if args.check:
        check = (ROOT / args.check).resolve()
        if not check.is_relative_to(HERE):
            raise ValueError('--check must stay inside WindowPIT/')
        for dep in imports(check):
            visit(dep)
    rows = [{'module': name, 'source': str(path), 'lines': len(path.read_text(encoding='utf-8-sig').splitlines())}
            for name, _, path in order]
    WORK.mkdir(parents=True, exist_ok=True)
    (WORK / 'lake-dependency-plan.json').write_text(json.dumps(rows, indent=2), encoding='utf-8')
    if args.plan:
        print(json.dumps({'modules': len(rows), 'lines': sum(row['lines'] for row in rows)}))
        return
    for i, (module, _, path) in enumerate(order, 1):
        print(f'LAKE [{i}/{len(order)}] {module}', flush=True)
        run_lake(['build', module], module, path, module,
                 args.retry_delay, args.resource_retries)
    if args.check:
        run_lake(['env', 'lean', str(check)], 'check-' + check.stem, check,
                 retry_delay=args.retry_delay, resource_retries=args.resource_retries)


if __name__ == '__main__':
    main()
