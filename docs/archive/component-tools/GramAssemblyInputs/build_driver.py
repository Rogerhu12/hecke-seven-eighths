"""Sequential per-module builder for GramAssemblyInputs (one lean process at a time).
Usage: python -I driver.py [--only NAME ...]"""
import json, os, re, subprocess, sys, time, ctypes
sys.stdout.reconfigure(encoding='utf-8')
PROJ = r"C:/Users/Boyang/Desktop/Math/Hecke L 435"
LIB = os.path.join(PROJ, 'GramAssemblyInputs')
SP = os.path.join(LIB, ".port")
os.makedirs(SP, exist_ok=True)
STATUS = os.path.join(SP, "build_status.json")
LOGDIR = os.path.join(SP, 'logs'); os.makedirs(LOGDIR, exist_ok=True)
man = json.load(open(os.path.join(LIB, 'PORT_MANIFEST.json'), encoding='utf-8'))
order = man['order']
only = set(sys.argv[sys.argv.index('--only') + 1:]) if '--only' in sys.argv else None
imp_re = re.compile(r'^import\s+(\S+)', re.M)
deps = {n: [i for i in imp_re.findall(open(os.path.join(LIB, n + '.lean'), encoding='utf-8').read()[:8000]) if i in order] for n in order}
status = json.load(open(STATUS, encoding='utf-8')) if os.path.exists(STATUS) else {}
class MEMSTAT(ctypes.Structure):
    _fields_ = [('dwLength', ctypes.c_ulong), ('dwMemoryLoad', ctypes.c_ulong), ('ullTotalPhys', ctypes.c_ulonglong),
                ('ullAvailPhys', ctypes.c_ulonglong), ('ullTotalPageFile', ctypes.c_ulonglong), ('ullAvailPageFile', ctypes.c_ulonglong),
                ('ullTotalVirtual', ctypes.c_ulonglong), ('ullAvailVirtual', ctypes.c_ulonglong), ('ullAvailExtendedVirtual', ctypes.c_ulonglong)]
def mem():
    m = MEMSTAT(); m.dwLength = ctypes.sizeof(MEMSTAT)
    ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(m))
    return m.ullAvailPhys / 2**30, m.ullAvailPageFile / 2**30  # avail RAM, avail commit
def wait_mem():
    while True:
        ram, commit = mem()
        if commit > 10 and ram > 1.5:
            return
        print(f"  waiting for memory: avail RAM {ram:.1f} GB, avail commit {commit:.1f} GB", flush=True)
        time.sleep(60)
env = dict(os.environ, LEAN_NUM_THREADS='4')
for n in order:
    if only is not None and n not in only: continue
    if status.get(n) == 'ok': continue
    bad = [d for d in deps[n] if status.get(d) != 'ok']
    if bad:
        status[n] = 'blocked:' + ','.join(bad)
        json.dump(status, open(STATUS, 'w'), indent=1)
        print(f"[skip] {n} blocked by {bad}", flush=True)
        continue
    wait_mem()
    t = time.time()
    r = subprocess.run(['lake', 'build', n], cwd=PROJ, env=env, capture_output=True, text=True, encoding='utf-8', errors='replace')
    out = r.stdout + r.stderr
    lines = [l for l in out.splitlines() if 'designed for use with the module system' not in l]
    open(os.path.join(LOGDIR, n + '.log'), 'w', encoding='utf-8').write('\n'.join(lines))
    ok = r.returncode == 0
    status[n] = 'ok' if ok else 'fail'
    json.dump(status, open(STATUS, 'w'), indent=1)
    errs = [l for l in lines if re.search(r'error', l)][:3]
    print(f"[{'ok' if ok else 'FAIL'}] {n} ({time.time()-t:.0f}s)" + ('' if ok else ' :: ' + ' | '.join(e[:200] for e in errs)), flush=True)
done = sum(1 for v in status.values() if v == 'ok')
print(f"DONE ok={done} fail={sum(1 for v in status.values() if v == 'fail')} blocked={sum(1 for v in status.values() if v.startswith('blocked'))}", flush=True)
