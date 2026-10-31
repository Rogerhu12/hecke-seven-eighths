"""Bundle actual reflected-project source bodies for a single Lean process.

This performs transformed combined source-body QA, not native project import
verification. Every transformation is recorded in the manifest alongside the
raw source SHA and transformed-body SHA. No declaration is mocked, admitted,
or skipped. Run with --check after obtaining the pinned Mathlib cache.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import time
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--order', type=Path,
    default=ROOT / 'verification/theta_global/actual_reflected_order.txt')
parser.add_argument('--name', default='ActualReflectedVerification')
parser.add_argument('--manifest', type=Path,
    default=ROOT / 'verification/theta_global/actual_reflected_manifest.json')
parser.add_argument('--audit', action='append')
parser.add_argument('--curated-imports', type=Path,
    default=REPO / 'verification/theta_global/vendor_curated_imports_snapshot.json')
parser.add_argument('--foundation-order', type=Path)
parser.add_argument('--foundation-module')
parser.add_argument('--output', type=Path)
parser.add_argument('--mathlib-source', type=Path, default=REPO / '.lake/packages/mathlib')
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
for path_arg in ('order', 'manifest', 'foundation_order', 'output', 'mathlib_source', 'curated_imports'):
    value = getattr(args, path_arg)
    if value is not None:
        setattr(args, path_arg, value.resolve())
if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', args.name):
    raise SystemExit('Expected a simple Lean module name.')
roots = [REPO, REPO / 'vendor/flt', REPO / 'vendor/tauceti',
         REPO / 'vendor/class-field-theory/Lean4', REPO / 'vendor/zeta23',
         REPO / 'vendor/openai', REPO / 'SkeletonInputs', REPO / 'GramCoreInputs',
         REPO / 'GramAssemblyInputs', args.mathlib_source]
order = args.order.read_text().splitlines()
curated_raw = args.curated_imports.read_bytes()
curated_snapshot = json.loads(curated_raw)
curated_imports = {item['module']: [dep for dep in item['curated_imports'] if dep.startswith('Mathlib.')]
    for item in curated_snapshot['modules']}
additional_imports = curated_snapshot.get('harness_additional_imports', {})
foundation = set(args.foundation_order.read_text().splitlines()) if args.foundation_order else set()
if bool(foundation) != bool(args.foundation_module):
    raise SystemExit('Foundation order and module must be supplied together.')

def without_comments(text):
    out = []
    i = 0
    level = 0
    while i < len(text):
        if text[i:i+2] == '/-':
            level += 1; out.append('  '); i += 2
        elif level and text[i:i+2] == '-/':
            level -= 1; out.append('  '); i += 2
        elif level:
            out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text[i:i+2] == '--':
            end = text.find('\n', i)
            if end < 0: end = len(text)
            out.append(' ' * (end-i)); i = end
        else:
            out.append(text[i]); i += 1
    return ''.join(out)

def open_scopes(source, module):
    stack = []
    for line in without_comments(source).splitlines():
        m = re.match(r'^(?:@\[.*?\]\s*)?(?:(?:public|private|noncomputable)\s+)?'
                     r'(namespace|section)\b(?:\s+([^\s]+))?', line)
        if m:
            stack.append((m.group(1),m.group(2) or ''))
            continue
        m = re.match(r'^end(?:\s+([^\s]+))?\s*$',line)
        if not m: continue
        if not stack: raise ValueError(f'Unmatched end in {module}: {line}')
        name = m.group(1)
        if not name:
            stack.pop(); continue
        names = []
        while stack:
            kind, top = stack.pop()
            names.insert(0,top)
            if '.'.join(names) == name: break
        else:
            raise ValueError(f'Unmatched named end in {module}: {line}')
    return stack

imports = {'Lean.Util.CollectAxioms'}
if args.foundation_module:
    imports.add(args.foundation_module)
# Legacy HeckeGeneral.Analysis.IdealSummability uses the public cardinality
# lemma from this private import of DedekindZeta. Expose its actual module
# explicitly when consolidating legacy files into a modern module.
imports.add('Mathlib.Algebra.BigOperators.Ring.Nat')
blocks = []
manifest = []
source_paths = []
for index,module in enumerate(order):
    rel = Path(*module.split('.')).with_suffix('.lean')
    path = next(r/rel for r in roots if (r/rel).is_file())
    source = path.read_bytes().decode('utf-8')
    source_paths.append(path)
    source_path = (str(path.relative_to(REPO)) if path.is_relative_to(REPO) else
        '.lake/packages/mathlib/' + str(path.relative_to(args.mathlib_source)))
    body = []
    umbrella_override_count = 0
    for line in source.splitlines():
        m = re.match(r'^(?:public\s+)?import\s+([A-Za-z0-9_.]+)\s*$',line)
        if m:
            original_dep = m.group(1)
            if original_dep == 'Mathlib' and module in curated_imports:
                umbrella_override_count += 1
            replacements = (curated_imports[module] if original_dep == 'Mathlib' and
                module in curated_imports else [original_dep])
            for dep in replacements:
                if dep in order:
                    if dep not in order[:index]: raise ValueError(f'Out-of-order import {module}: {dep}')
                elif dep in foundation:
                    pass
                else: imports.add(dep)
        elif re.fullmatch(r'module(?:[ \t]*--.*)?[ \t]*', line): pass
        else: body.append(line)
    for dep in additional_imports.get(module, []):
        if dep in order:
            if dep not in order[:index]: raise ValueError(f'Out-of-order extra import {module}: {dep}')
        elif dep not in foundation:
            imports.add(dep)
    scopes = open_scopes(source,module)
    body_text = '\n'.join(body)
    meta_command_helper = module == 'FLTReuse.M1868db956c866c8d'
    if meta_command_helper:
        assert body_text.count('def p2mOpenCore ') == 1, module
        body_text = body_text.replace('def p2mOpenCore ', 'meta def p2mOpenCore ')
    exported_private_helper = module == 'FLTReuse.Ma6dd0c4d713fb96a'
    if exported_private_helper:
        assert body_text.count('private lemma rightActions_smul_eq_one_tmul_mul') == 1, module
        body_text = body_text.replace('private lemma rightActions_smul_eq_one_tmul_mul',
            'public lemma rightActions_smul_eq_one_tmul_mul')
    qualified_fourier = module in {'HeckeGeneral.Arithmetic.ProductResidueFourier',
        'HeckeGeneral.Arithmetic.ResidueGaussSums'}
    qualification_counts = {name: len(re.findall(r'(?<![\w.])' + name + r'(?![\w.])', body_text))
        for name in ('fourier', 'fourier_zero')} if qualified_fourier else {}
    if qualified_fourier:
        body_text = re.sub(r'(?<![\w.])(fourier|fourier_zero)(?![\w.])',
            lambda match: 'HeckeGeneral.Arithmetic.PeriodicFourier.' + match.group(1), body_text)
    closures = '\n'.join('end' + (' ' + name if name else '')
        for _kind, name in reversed(scopes))
    legacy_visibility = not bool(re.search(r'^module[ \t]*$', without_comments(source), re.M))
    compatibility = ('set_option backward.privateInPublic true\n'
        'set_option backward.proofsInPublic true\n') if legacy_visibility else ''
    transformed_body = compatibility + body_text + '\n' + closures
    blocks.append(f'\n/- BEGIN ACTUAL SOURCE BODY: {module} -/\n'
        f'section Actual_{module.replace(".","_")}\n' + transformed_body +
        f'\nend Actual_{module.replace(".","_")}\n'
        f'/- END ACTUAL SOURCE BODY: {module} -/\n')
    manifest.append({'module':module,'path':source_path,
        'sha256':hashlib.sha256(source.encode()).hexdigest(),
        'normalized_source_sha256':hashlib.sha256(source.replace('\r\n','\n').replace('\r','\n').encode()).hexdigest(),
        'line_endings_normalized': '\r' in source,
        'curated_umbrella_import_overridden':umbrella_override_count > 0,
        'curated_umbrella_import_override_count':umbrella_override_count,
        'curated_umbrella_import_replacements':curated_imports.get(module, []),
        'harness_additional_imports':additional_imports.get(module, []),
        'transformed_body_sha256':hashlib.sha256(transformed_body.encode()).hexdigest(),
        'explicit_eof_scope_names':[name for _,name in reversed(scopes)],
        'explicit_eof_closures':len(scopes),
        'legacy_private_visibility_compatibility':legacy_visibility,
        'legacy_public_proof_elaboration_compatibility':legacy_visibility,
        'qualify_periodic_fourier_for_consolidated_imports':qualified_fourier,
        'qualified_identifiers': ['fourier', 'fourier_zero'] if qualified_fourier else [],
        'qualified_identifier_occurrences':qualification_counts,
        'qualified_identifier_namespace':'HeckeGeneral.Arithmetic.PeriodicFourier' if qualified_fourier else None,
        'mark_legacy_command_helper_meta':meta_command_helper,
        'export_legacy_private_lemma_for_public_proof':exported_private_helper})

private_body_imports = ['Mathlib.RingTheory.DedekindDomain.AdicValuation'] if 'FLTReuse.M5960be08a50663ff' in order else []
header = ('module\n\n' + '\n'.join('public import '+m for m in sorted(imports)) +
    ''.join('\nimport all ' + m for m in private_body_imports) +
    '\n\n@[expose] public section\n' +
    f'/-! Actual-source combined verification; see {args.manifest.name}. -/\n')
audit_names = args.audit or ['ThetaGlobal.ReflectedAbsoluteProject.marked_reflected_absolute',
    'ThetaGlobal.ReflectedArithmetic.norm_reflectedCoefficient_le']
audit = '\n' + '\n'.join('#print axioms ' + name for name in audit_names) + '\n'
audit += ('\nopen Lean Elab Command in\nrun_cmd do\n'
    '  for name in #[' + ', '.join('`' + name for name in audit_names) + '] do\n'
    '    unless ((← getEnv).find? name).isSome do\n'
    '      throwError "QA target {name} was not defined"\n'
    '    let axioms ← Lean.collectAxioms name\n'
    '    for axiomName in axioms do\n'
    '      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do\n'
    '        throwError "QA target {name} depends on forbidden axiom {axiomName}"\n'
    '    logInfo m!"THETA_GLOBAL_PROJECT_QA_AXIOMS|{name}|{String.intercalate "," (axioms.toList.map toString)}"\n')
out = header + ''.join(blocks) + audit
dest = args.output or REPO / 'verification/theta_global' / (args.name + '.lean')
dest.parent.mkdir(parents=True, exist_ok=True)
dest.write_text(out)
report = {
    'lean':'4.35.0-rc3','mathlib':'0493595ecd5da8ef14742febab99728f98e948e8',
    'expected_lean_commit':'470d5ce1400764999581fd26d5d72b00d990b0f4',
    'version_fields_kind':'required versions; actual observations recorded only when --check runs',
    'verification_kind':'transformed combined source-body QA; not native project import verification',
    'transformations':['consolidate imports and module headers',
        'replace applicable original umbrella Mathlib imports only in this QA header using the recorded ten-module curated map; see per-module records and total count',
        'add one modern module header and a global @[expose] public section for the consolidated declaration environment',
        'add public header imports Mathlib.Algebra.BigOperators.Ring.Nat for the original cardinality lemma and Lean.Util.CollectAxioms for the strict axiom audit',
        'supply recorded additional Lie.OfAssociative imports for definitions previously re-exported by the original umbrellas',
        'normalize source line endings to LF in the generated bundle',
        'isolate every source file in its own section',
        'close explicitly the original scopes left open at EOF',
        'preserve legacy visibility with scoped backward.privateInPublic',
        'import all AdicValuation when needed to retain private definition bodies used by an original legacy proof',
        'preserve legacy proof elaboration with scoped backward.proofsInPublic',
        'mark the legacy p2mOpenCore command elaborator helper meta in the modern bundle',
        'export the unchanged private rightActions_smul_eq_one_tmul_mul lemma for a legacy public definition proof',
        'qualify bare fourier and fourier_zero in ProductResidueFourier and ResidueGaussSums to the actual PeriodicFourier declarations to resolve consolidated-import ambiguity'],
    'foundation_module':args.foundation_module,
    'external_public_imports':sorted(imports),
    'curated_import_replacement_count':sum(item['curated_umbrella_import_override_count'] for item in manifest),
    'audit_targets':audit_names,
    'allowed_axioms':['propext', 'Classical.choice', 'Quot.sound'],
    'curated_imports_snapshot_sha256':hashlib.sha256(curated_raw).hexdigest(),
    'private_body_imports':private_body_imports,
    'bundle_sha256':hashlib.sha256(out.encode()).hexdigest(),
    'modules':manifest}
args.manifest.parent.mkdir(parents=True, exist_ok=True)
print(f'Generated {len(manifest)} actual modules, {len(imports)} external imports, '
      f'{len(out.splitlines())} lines: {dest}')

if args.check:
    toolchain_pin = (REPO / 'lean-toolchain').read_text().strip()
    lake_manifest = json.loads((REPO / 'lake-manifest.json').read_text())
    mathlib_pin = next(package['rev'] for package in lake_manifest['packages']
        if package['name'] == 'mathlib')
    if toolchain_pin != 'leanprover/lean4:v4.35.0-rc3' or mathlib_pin != report['mathlib']:
        raise SystemExit('Repository Lean/Mathlib pins differ from the required verification versions.')
    observed_version = subprocess.run(['lake', 'env', 'lean', '--version'], cwd=REPO,
        check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT).stdout.strip()
    if '4.35.0-rc3' not in observed_version or report['expected_lean_commit'][:7] not in observed_version:
        raise SystemExit('Observed Lean version differs from the pinned compiler: ' + observed_version)
    mathlib_git_root = subprocess.run(['git', '-C', str(args.mathlib_source),
        'rev-parse', '--show-toplevel'], check=True, text=True, stdout=subprocess.PIPE).stdout.strip()
    if Path(mathlib_git_root).resolve() != args.mathlib_source.resolve():
        raise SystemExit('--check requires --mathlib-source to be the actual pinned Mathlib Git checkout.')
    observed_mathlib_rev = subprocess.run(['git', '-C', str(args.mathlib_source),
        'rev-parse', 'HEAD'], check=True, text=True, stdout=subprocess.PIPE).stdout.strip()
    if observed_mathlib_rev != report['mathlib']:
        raise SystemExit('Observed Mathlib source revision differs from the required pin.')
    report['observed_versions'] = {'lean_version':observed_version,
        'repository_lean_toolchain':toolchain_pin, 'repository_mathlib_pin':mathlib_pin,
        'mathlib_source_git_revision':observed_mathlib_rev}
    if not dest.is_relative_to(REPO):
        raise SystemExit('--check output must be inside the repository so the module path is unambiguous.')
    artifact = REPO / '.lake/build/lib/lean' / dest.relative_to(REPO).with_suffix('.olean')
    artifact.parent.mkdir(parents=True, exist_ok=True)
    report['artifact_output'] = str(artifact.relative_to(REPO))
    report['compiler_options'] = {'autoImplicit':False, 'relaxedAutoImplicit':False,
        'source_options_preserved':True}
    report['artifact_path_policy'] = 'Canonical Lake project library directory; foundation imports need no custom LEAN_PATH.'
    command = ['lake', 'env', 'lean', '-j2', '-DautoImplicit=false',
        '-DrelaxedAutoImplicit=false', '-R', str(REPO), '-o', str(artifact), str(dest)]
    started = time.monotonic()
    result = subprocess.run(command, cwd=REPO, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT)
    unchanged = all(hashlib.sha256(path.read_bytes()).hexdigest() == item['sha256']
        for path, item in zip(source_paths, manifest))
    bundle_unchanged = hashlib.sha256(dest.read_bytes()).hexdigest() == report['bundle_sha256']
    audit_markers = [line for line in result.stdout.splitlines()
        if line.startswith('THETA_GLOBAL_PROJECT_QA_AXIOMS|')]
    audit_complete = len(audit_markers) == len(audit_names)
    log_path = dest.with_suffix('.build.log')
    log_path.write_text(result.stdout)
    report.update({'command': command, 'exit_code': result.returncode,
        'source_unchanged': unchanged, 'bundle_unchanged': bundle_unchanged,
        'audit_complete':audit_complete, 'audit_markers':audit_markers,
        'reported_sorryAx': 'sorryAx' in result.stdout,
        'utc': datetime.now(timezone.utc).isoformat(),
        'elapsed_seconds': time.monotonic() - started, 'build_log': str(log_path)})
    print(result.stdout)
args.manifest.write_text(json.dumps(report, indent=2) + '\n')
if args.check:
    raise SystemExit(result.returncode if unchanged and bundle_unchanged and audit_complete else 2)
