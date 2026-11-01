#!/usr/bin/env python3
"""Serialize HIGHBIN's native Lean processes with explicit resource settings.

Create a temporary toolchain view whose compiler delegates to the unchanged
pinned Lean executable under one process lock.  Lake's documented
LAKE_OVERRIDE_LEAN/LEAN_SYSROOT mechanism selects this view.  This changes
resource scheduling only; declarations, dependencies and compiler version
remain unchanged. A zero memory setting preserves Lean's default without a
language-level memory cap. Metadata queries do not acquire the compilation lock.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', default=shutil.which('lean'))
    parser.add_argument('--directory', type=Path, required=True)
    parser.add_argument('--github-env', type=Path)
    parser.add_argument('--memory-mib', type=int, default=0,
                        help='Per-compiler limit in MiB; 0 uses Lean default')
    args = parser.parse_args()
    if not args.lean or args.memory_mib < 0:
        parser.error('a Lean executable and nonnegative memory limit are required')
    prefix = Path(subprocess.check_output(
        [args.lean, '--print-prefix'], text=True).strip()).resolve()
    real_lean = prefix / 'bin' / 'lean'
    version = subprocess.check_output([str(real_lean), '--version'], text=True).strip()
    if '4.35.0-rc3' not in version:
        raise SystemExit('Unexpected compiler: ' + version)
    directory = args.directory.resolve()
    if directory == prefix or prefix in directory.parents:
        raise SystemExit('The temporary view must not modify the installed toolchain')
    directory.mkdir(parents=True, exist_ok=True)
    for entry in prefix.iterdir():
        if entry.name != 'bin':
            target = directory / entry.name
            if not target.exists() and not target.is_symlink():
                target.symlink_to(entry, target_is_directory=entry.is_dir())
    bindir = directory / 'bin'
    bindir.mkdir(exist_ok=True)
    for entry in (prefix / 'bin').iterdir():
        if entry.name != 'lean':
            target = bindir / entry.name
            if not target.exists() and not target.is_symlink():
                target.symlink_to(entry, target_is_directory=entry.is_dir())
    wrapper = bindir / 'lean'
    if wrapper.is_symlink():
        raise SystemExit('Refusing to overwrite a compiler symlink')
    wrapper.write_text('''#!/usr/bin/env python3
import fcntl
import os
import subprocess
import sys

real = %r
if len(sys.argv) == 2 and sys.argv[1] in ('--version', '--print-prefix', '--githash'):
    os.execv(real, [real, *sys.argv[1:]])
arguments = []
incoming = iter(sys.argv[1:])
for argument in incoming:
    # Lean 4.35 stops option parsing immediately at --run (also -r),
    # so its source filename and all following program arguments are data.
    if argument in ('--', '--run', '-r'):
        arguments.append(argument)
        arguments.extend(incoming)
        break
    if argument in ('-j', '--threads', '-M', '--memory'):
        next(incoming, None)
    elif argument.startswith(('-j', '-M', '--threads=', '--memory=')):
        continue
    elif argument == '-D':
        value = next(incoming, None)
        if value is None:
            arguments.append(argument)
        elif not value.startswith('max_memory='):
            arguments.extend((argument, value))
    elif argument.startswith('-Dmax_memory='):
        continue
    else:
        arguments.append(argument)
with open(%r, 'a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    code = subprocess.call([real, '-j1', %r, *arguments])
    sys.exit(code if code >= 0 else 128 - code)
''' % (str(real_lean), str(directory / 'compile.lock'), '-M' + str(args.memory_mib)))
    wrapper.chmod(0o755)
    settings = {'LAKE_OVERRIDE_LEAN': '1', 'LEAN_SYSROOT': str(directory)}
    if args.github_env:
        with args.github_env.open('a') as output:
            for name, value in settings.items():
                output.write(name + '=' + value + '\n')
    print(json.dumps({'compiler': version, 'memory_mib': args.memory_mib,
                      'simultaneous_compilers': 1, 'environment': settings}))


if __name__ == '__main__':
    main()
