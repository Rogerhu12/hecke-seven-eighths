"""Reproducible combined-body QA for the standalone THETA_GLOBAL lemmas.

Run from any directory. This does not replace native project import checks.
The required Lean and Mathlib versions are the repository's pinned versions.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess

root = Path(__file__).resolve().parents[1]
base = root / 'ThetaGlobal'
names = [
    'FiniteShellCoefficients', 'FiniteClassExpansion', 'FiniteTensorCoefficients',
    'FinitePowerQuotient', 'FiniteHaarShells', 'FiniteMellinIntegration', 'FiniteTensorMellin',
    'FiniteMellinRatio',
    'ReflectedAbsoluteCore', 'ReflectedLocalBounds', 'ReflectedIdealMajorant',
    'ReflectedCoefficientModel', 'ReflectedCoefficientSummability', 'ReflectedDominatedLimit',
    'GlobalMarks', 'GlobalPhases', 'GlobalFrequency', 'GlobalFrequencyReconstruction',
    'GlobalSupportReindex',
    'GlobalEmbedding', 'GlobalCharacterSums', 'GlobalDigitSupport', 'GlobalFourierDescent', 'GlobalAngular',
    'GlobalCompactPeriod', 'GlobalAffineJets', 'WeightedUnfolding', 'SheetMellin', 'GaussianRegularization',
    'GaussianTransfer', 'ConvolutionMass', 'ScalarMellinConvolution',
    'VerticalContour', 'VerticalInverseBounds', 'TestMellinLimit',
    'DeconvolverMoments', 'AnnularTransfer', 'ScalarGaussianLimits',
    'GaussianStripDecay', 'GammaDeconvolver', 'GammaAnnularTransfer',
    'GammaReciprocalGrowth', 'GammaProfileGrowth', 'GlobalProjectOrbitAbsolute',
    'ReflectedAudit',
]

parser = argparse.ArgumentParser()
parser.add_argument('--check', action='store_true', help='run lake env lean after generation')
args = parser.parse_args()
outdir = root / 'verification/theta_global'
outdir.mkdir(parents=True, exist_ok=True)
imports = set()
blocks = []
manifest = []
for index, name in enumerate(names):
    path = base / (name + '.lean')
    source = path.read_text()
    body = []
    for line in source.splitlines():
        match = re.fullmatch(r'(?:public\s+)?import\s+([A-Za-z0-9_.]+)', line)
        if match:
            module = match.group(1)
            if module.startswith('ThetaGlobal.'):
                if module.split('.')[-1] not in names[:index]:
                    raise ValueError(f'Out of order dependency: {name} imports {module}')
            elif not module.startswith(('Mathlib.', 'Lean.')):
                raise ValueError(f'Non-standalone import in {name}: {module}')
            else:
                imports.add(module)
        elif line.strip() in ('module', '@[expose] public section'):
            pass
        else:
            body.append(line)
    extra_end = '\nend\n' if re.search(r'^noncomputable section\s*$', source, re.M) else ''
    blocks.append(f'\n/- BEGIN SOURCE BODY: ThetaGlobal/{name}.lean -/\n'
        f'section Verification_{name}\n' + '\n'.join(body) + extra_end +
        f'\nend Verification_{name}\n'
        f'/- END SOURCE BODY: ThetaGlobal/{name}.lean -/\n')
    manifest.append({'module': 'ThetaGlobal.' + name,
        'source': str(path.relative_to(root)),
        'sha256': hashlib.sha256(source.encode()).hexdigest()})

output = ('module\n\n' + '\n'.join('public import ' + m for m in sorted(imports)) +
    '\n\n@[expose] public section\n' +
    '/-! Generated combined-body QA. See manifest.json for exact source hashes. -/\n' +
    ''.join(blocks))
source_path = outdir / 'Standalone.lean'
source_path.write_text(output)
report = {'lean': '4.35.0-rc3',
    'mathlib': '0493595ecd5da8ef14742febab99728f98e948e8',
    'verification_kind': 'combined source bodies, not native project imports',
    'transformations': ['consolidate imports and module/public headers',
        'isolate each original file in a named section',
        'close the original end-of-file noncomputable section'],
    'bundle_sha256': hashlib.sha256(output.encode()).hexdigest(),
    'modules': manifest}
print(f'Generated {len(names)} modules with {len(imports)} imports: {source_path}')
if args.check:
    command = ['lake', 'env', 'lean', '-j2', str(source_path.relative_to(root))]
    result = subprocess.run(command, cwd=root, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT)
    (outdir/'Standalone.log').write_text(result.stdout)
    unchanged = all(hashlib.sha256((root/m['source']).read_bytes()).hexdigest() ==
        m['sha256'] for m in manifest)
    unchanged = unchanged and hashlib.sha256(source_path.read_bytes()).hexdigest() == report['bundle_sha256']
    reported_sorry = 'sorryAx' in result.stdout
    report.update({'command': command, 'exit_code': result.returncode,
        'source_unchanged': unchanged,
        'reported_sorryAx': reported_sorry})
    print(result.stdout)
    print('Exit:',result.returncode,'sources unchanged:',unchanged)
(outdir/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
if args.check:
    raise SystemExit(2 if not unchanged else 3 if reported_sorry else result.returncode)
