"""Run Lean 4.35 on one file with the compile435 search path plus a work directory's outputs.

Usage: python -I run_lean435.py <work dir> <file.lean>
"""
import importlib.util
import os
import subprocess
import sys
from pathlib import Path

here = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('compile435', here / 'compile435.py')
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)
work, file = Path(sys.argv[1]), Path(sys.argv[2])
paths = [str(work / 'out')] + c.lean_path().split(os.pathsep)
env = dict(os.environ, LEAN_PATH=os.pathsep.join(paths), LEAN_SYSROOT=str(c.TOOLCHAIN), LEAN_NUM_THREADS='2')
raise SystemExit(subprocess.run([str(c.LEAN), *c.FLAGS, str(file)], cwd=str(c.AXIOM), env=env).returncode)
