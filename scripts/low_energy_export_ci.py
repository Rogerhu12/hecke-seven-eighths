#!/usr/bin/env python3
"""Export the checked-out sources and installed Lean environment for replay.

This is a read-only diagnostic export. It does not generate proofs, replace
modules, or change verification receipts. Only tracked repository files and
compiler/library files are exported; Git credentials and .git are excluded.
"""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.low-energy-replay'


def sha256(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def runtime_filter(info):
    parts = Path(info.name).parts
    if '.git' in parts:
        return None
    if info.isfile() and info.name.endswith(('.a', '.o', '.c', '.ilean')):
        return None
    return info


def main():
    OUT.mkdir(exist_ok=True)
    env = json.loads(subprocess.check_output([
        'lake', 'env', 'python3', '-c',
        'import os,json;print(json.dumps({k:os.environ.get(k, "") for k in '
        '["PATH","LEAN_PATH","LEAN_SRC_PATH","LD_LIBRARY_PATH"]}))'
    ], cwd=ROOT, text=True).strip().splitlines()[-1])
    lean = shutil.which('lean', path=env['PATH'])
    if lean is None:
        raise RuntimeError('The pinned Lean executable was not found.')
    sysroot = Path(subprocess.check_output([lean, '--print-prefix'],
        cwd=ROOT, env={**os.environ, **env}, text=True).strip()).resolve()
    version = subprocess.check_output([lean, '--version'],
        cwd=ROOT, env={**os.environ, **env}, text=True).strip()
    if '4.35.0-rc3' not in version:
        raise RuntimeError('Refusing to export an unexpected Lean version: ' + version)
    source = OUT / 'source.tar.gz'
    subprocess.run(['git', 'archive', '--format=tar.gz', '-o', str(source), 'HEAD'],
        cwd=ROOT, check=True)
    runtime = OUT / 'runtime.tar.gz'
    with tarfile.open(runtime, 'w:gz', compresslevel=1) as archive:
        for component in ('bin', 'lib'):
            path = sysroot / component
            if path.exists():
                archive.add(path, arcname='toolchain/' + component,
                    filter=runtime_filter)
    libraries = OUT / 'libraries.tar.gz'
    mappings = []
    seen = set()
    with tarfile.open(libraries, 'w:gz', compresslevel=1) as archive:
        for raw in env['LEAN_PATH'].split(os.pathsep):
            if not raw:
                continue
            path = Path(raw)
            path = (path if path.is_absolute() else ROOT / path).resolve()
            if path == (ROOT / '.lake/build/lib/lean').resolve():
                mappings.append({'original': raw, 'replay': 'project/.lake/build/lib/lean'})
                continue
            if path == sysroot / 'lib/lean':
                mappings.append({'original': raw, 'replay': 'toolchain/lib/lean'})
                continue
            if not path.is_dir() or path in seen:
                continue
            label = 'libraries/' + str(len(seen))
            seen.add(path)
            archive.add(path, arcname=label, filter=runtime_filter)
            mappings.append({'original': raw, 'replay': label})
    manifest = {
        'schema': 1,
        'purpose': 'source/compiler replay; not a proof verification receipt',
        'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT,
            text=True).strip(),
        'lean': version,
        'original_root': str(ROOT),
        'original_sysroot': str(sysroot),
        'environment': env,
        'lean_path_mappings': mappings,
        'archives': {p.name: {'sha256': sha256(p), 'bytes': p.stat().st_size}
            for p in (source, runtime, libraries)},
    }
    (OUT / 'environment.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps(manifest, indent=2), flush=True)


if __name__ == '__main__':
    main()
