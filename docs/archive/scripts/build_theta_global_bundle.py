"""Reproducible combined-body QA for the standalone THETA_GLOBAL lemmas.

Run from any directory. This does not replace native project import checks.
The required Lean and Mathlib versions are the repository's pinned versions.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
import re
import subprocess


def audit_reported_axioms(expected, output):
    """Check every requested #print record, including wrapped Lean output."""
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    pattern = re.compile(
        r"^'([^'\r\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|"
        r"does not depend on any axioms)[ \t]*$", re.M)
    matches = list(pattern.finditer(output))
    matched_starts = {match.start() for match in matches}
    headers = re.finditer(
        r"^'[^'\r\n]+' (?:depends on axioms:|does not depend on any axioms)",
        output, re.M)
    malformed = [output[header.start():].splitlines()[0] for header in headers
                 if header.start() not in matched_starts]
    records = []
    for match in matches:
        axioms = [name.strip() for name in (match.group(2) or '').split(',')
                  if name.strip()]
        records.append({'declaration': match.group(1), 'axioms': axioms})
    requested = Counter(expected)
    reported = Counter(record['declaration'] for record in records)
    missing = list((requested - reported).elements())
    unexpected = list((reported - requested).elements())
    forbidden = [record for record in records
                 if set(record['axioms']) - allowed]
    return {'passed': bool(expected) and not (missing or unexpected or forbidden or malformed),
            'expected_record_count': len(expected),
            'reported_record_count': len(records),
            'missing': missing, 'unexpected': unexpected,
            'forbidden': forbidden, 'malformed': malformed, 'records': records}


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
expected_axioms = []
for index, name in enumerate(names):
    path = base / (name + '.lean')
    source = path.read_text()
    expected_axioms.extend(re.findall(r'^#print axioms\s+(\S+)\s*$', source, re.M))
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
    'expected_axiom_declarations': expected_axioms,
    'modules': manifest}
print(f'Generated {len(names)} modules with {len(imports)} imports: {source_path}')
if args.check:
    # Direct `lake env lean` does not inherit the library's leanOptions.
    # Match the two implicit-parameter options used by the native build.
    command = ['lake', 'env', 'lean', '-j2', '-DautoImplicit=false',
        '-DrelaxedAutoImplicit=false', str(source_path.relative_to(root))]
    result = subprocess.run(command, cwd=root, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT)
    (outdir/'Standalone.log').write_text(result.stdout)
    unchanged = all(hashlib.sha256((root/m['source']).read_bytes()).hexdigest() ==
        m['sha256'] for m in manifest)
    unchanged = unchanged and hashlib.sha256(source_path.read_bytes()).hexdigest() == report['bundle_sha256']
    reported_sorry = 'sorryAx' in result.stdout
    axiom_audit = audit_reported_axioms(expected_axioms, result.stdout)
    report.update({'command': command, 'exit_code': result.returncode,
        'source_unchanged': unchanged,
        'reported_sorryAx': reported_sorry, 'axiom_audit': axiom_audit})
    print(result.stdout)
    print('Exit:',result.returncode,'sources unchanged:',unchanged)
    print('Axiom audit:', 'passed' if axiom_audit['passed'] else 'FAILED',
          f"({axiom_audit['reported_record_count']}/{len(expected_axioms)} records)")
    for issue in ('missing', 'unexpected', 'forbidden', 'malformed'):
        if axiom_audit[issue]:
            print(f'Axiom audit {issue}:', axiom_audit[issue])
(outdir/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
if args.check:
    raise SystemExit(2 if not unchanged else
        3 if reported_sorry or not axiom_audit['passed'] else result.returncode)
