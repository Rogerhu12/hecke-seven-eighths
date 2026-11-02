#!/usr/bin/env python3
"""Join split field projections in Lean files.

Lean 4 reads `x.f` as a projection only when there is no whitespace before
the dot.  A line that starts with `.f ...` right after a line ending in `)`
is therefore parsed as an extra argument `(.f ...)` of the expression above,
which gives "Function expected" errors.  This tool moves every such `.f`
line onto the end of the previous line (only the newline and indentation
are removed), repeating until nothing changes, so chains of projections are
handled too.  Comments and strings are left alone.

usage: join_projections.py FILE...   (an argument @LIST reads files from LIST)
Prints the number of joins per changed file.
"""
from __future__ import annotations

import importlib.util
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
_spec = importlib.util.spec_from_file_location('probe_map', ROOT / '.github/probe/probe_map.py')
pm = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(pm)

DOT = re.compile(r'^([ \t]+)\.[A-Za-z_]')


def join_once(text: str) -> tuple[str, bool]:
    code, _, ctx = pm.scan(text)
    lines = text.split('\n')
    offs, off = [], 0
    for ln in lines:
        offs.append(off)
        off += len(ln) + 1
    for i in range(1, len(lines)):
        m = DOT.match(lines[i])
        if not m or ctx[offs[i] + len(m.group(1))] != 0:
            continue
        prev = lines[i - 1].rstrip()
        end = offs[i - 1] + len(prev) - 1
        if not prev.endswith(')') or not code[end]:
            continue
        lines[i - 1] = prev + lines[i].lstrip()
        del lines[i]
        return '\n'.join(lines), True
    return text, False


def join_all(text: str) -> tuple[str, int]:
    n = 0
    while True:
        text, changed = join_once(text)
        if not changed:
            return text, n
        n += 1


def main() -> int:
    files = []
    for a in sys.argv[1:]:
        files += [ln.strip() for ln in Path(a[1:]).read_text(encoding='utf-8').splitlines()
                  if ln.strip()] if a.startswith('@') else [a]
    for f in files:
        p = Path(f)
        text = p.read_bytes().decode('utf-8')
        nl = '\r\n' if '\r\n' in text else '\n'
        new, n = join_all(text.replace('\r\n', '\n'))
        if n:
            p.write_bytes(new.replace('\n', nl).encode('utf-8'))
            print(f'{f}: {n}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
