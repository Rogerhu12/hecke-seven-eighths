#!/usr/bin/env python3
"""Statement skeleton of the MOM_ENGINE_STEP modules that are not yet on
dtests-handoff (coordination tool, see cloud_tasks/MOM_ENGINE_STEP_GROUPS.md).

The skeleton of a Lean file is the file with every theorem/lemma/example proof
body replaced by `sorry`.  Statements, definitions, structures, instances and
proofs that are just `rfl` (those are `dsimp` lemmas, so downstream
elaboration can depend on them) are kept.  A module elaborates the same way
against the skeleton of its dependencies as against their real versions,
because theorem proofs are never unfolded.

usage: skeleton.py make FILE...       rewrite each file in place as its skeleton
       skeleton.py interface FILE...  print {file: sha256 of its skeleton} as JSON
An argument @LIST stands for the files listed one per line in LIST.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import re
import sys
import tempfile
from pathlib import Path

ROOT = Path.cwd()
_spec = importlib.util.spec_from_file_location('probe_map', ROOT / '.github/probe/probe_map.py')
pm = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(pm)

RFL = re.compile(r'^(?:by )?(?:exact )?(?:fun [^=]*=> )?(?:rfl|Iff\.rfl|HEq\.rfl|Eq\.refl _|\(Eq\.refl _\))$')


def skeleton_text(text: str) -> str:
    with tempfile.TemporaryDirectory() as d:
        path = Path(d) / 'M.lean'
        path.write_bytes(text.encode('utf-8'))
        src = pm.Source(path)
        infos = []
        for b in src.boundaries:
            m = pm.DECL.match(src.lines[b])
            if not m or m.group(1) not in pm.STUBBABLE:
                continue
            nxt = [x for x in src.boundaries if x > b]
            last = nxt[0] if nxt else len(src.lines)
            info = src.analyse(last, len(src.lines[last - 1]), '')
            if not info['stubbable']:
                continue
            body = ' '.join(src.text[info['sep']:info['end']].split())
            if info['sep_kind'] == ':=' and RFL.match(body):
                continue
            infos.append(info)
        return src.stub(infos) if infos else text


def fingerprint(text: str) -> str:
    return hashlib.sha256(skeleton_text(text).replace('\r\n', '\n').encode('utf-8')).hexdigest()


def main() -> int:
    if len(sys.argv) < 3 or sys.argv[1] not in ('make', 'interface'):
        print(__doc__)
        return 2
    files = []
    for a in sys.argv[2:]:
        files += [ln.strip() for ln in Path(a[1:]).read_text(encoding='utf-8').splitlines()
                  if ln.strip()] if a.startswith('@') else [a]
    if sys.argv[1] == 'make':
        for f in files:
            p = Path(f)
            p.write_bytes(skeleton_text(p.read_bytes().decode('utf-8')).encode('utf-8'))
        return 0
    print(json.dumps({f: fingerprint(Path(f).read_bytes().decode('utf-8')) for f in files},
                     indent=0, sort_keys=True))
    return 0


if __name__ == '__main__':
    sys.exit(main())
