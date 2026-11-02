#!/usr/bin/env python3
"""Prepare complete Dual temporary copies with the same raw-helper fix.

Both variants start from frozen tracked e3e and apply the same 114-byte
pointwise-lambda instantiation fix. The control alone adds one 45-byte scoped
unusedSectionVars setting to the public phase sum declaration. The original
108 marker lines and their order are unchanged. This module launches no
process and does not modify tracked source or any imported guard.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

SOURCE = Path('HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualGaussHybridTerminal.lean')
TRACKED_SOURCE_SHA = 'e3e2453aff96995252298f97c9ee85074252d4cb937a118e40411f5e760eb6ac'
TRACKED_SOURCE_BYTES = 17905
BASE_MARKER = Path('.github/scripts/mom-engine-step-a2-dual-candidate-diagnostic.py')
BASE_MARKER_SHA = '3d736c13349b589ac227c69260fad27ec872d772dbfa9cff2b86d36deb24cd81'
BASE_MARKED_SHA = 'd2b4ed2cb225ce4baa610ea4a98960cc6ca11730ce28c083bd79ff24c9ad8d4f'
BASE_MARKED_BYTES = 26850
PREFIX = 'A2_DUAL_E3E2453_DIAGNOSTIC '
PARENT_HEAD = '1d8375a7b6c05f6c30c2b1523b195dc072d574b2'
PARENT_TREE = 'b5bddfe7f9bb663212dd9d459e14322b46e9b48c'
SCOPE_TARGET = 'HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualTerminalCalibration.phase_cost_eq_budgets_leaves'
OPTION = b'set_option linter.unusedSectionVars false in\n'
ANCHOR = b'/-- Exact terminal and nonzero separation on the original second\nsource.  Neither terminal budget is a new assumed aggregate estimate. -/\ntheorem phase_cost_eq_budgets_leaves\n'
OLD_RW = b'  rw [integral_const_mul,\n    integral_add ((integrable_const zeroTerm).add hf) (integrable_const tailTerm),\n    integral_add (integrable_const zeroTerm) hf, integral_const, integral_const]\n'
NEW_RW = b'  rw [integral_const_mul,\n    integral_add (f := fun x : X => zeroTerm + f x) (g := fun _ : X => tailTerm)\n      ((integrable_const zeroTerm).add hf) (integrable_const tailTerm),\n    integral_add (f := fun _ : X => zeroTerm) (g := f)\n      (integrable_const zeroTerm) hf, integral_const, integral_const]\n'
VARIANTS = {
    'default': {
        'candidate_sha256': '770bf81e8c634ac7a49c5eb00f179eec0ebf87fd764ccfbf115ed84d441ddac2',
        'candidate_bytes': 18019,
        'marked_sha256': '4a4fcf23ae76a9933c61bb76c45f94738dd75cf0a0a5461a37cec81e4f507538',
        'marked_bytes': 26964,
        'module': 'MomEngineDualCorrectedDefault',
        'warning_scope_count': 0,
    },
    'phase_warning_control': {
        'candidate_sha256': '21118c1b1c69084e625ba068b4501ab76997c11967a468fc0d9c46124e14157e',
        'candidate_bytes': 18064,
        'marked_sha256': 'c11c76f0fb7b2f2b2fa4b36441338121efe18c09241f98081938dd8375ac49a9',
        'marked_bytes': 27009,
        'module': 'MomEngineDualCorrectedPhaseWarning',
        'warning_scope_count': 1,
    },
}
FALSE_FLAGS = {
    'acceptance_evidence': False, 'original_module_native_was_run': False,
    'original_module_acceptance': False, 'complete_target_module_compiled': False,
    'complete_module_within_five_minutes': False, 'full_task_acceptance': False,
    'compiler_outputs_can_be_restored_as_project_cache': False,
    'production_approval': False, 'candidate_native_validation_performed': False,
    'fresh_axiom_audit_performed': False, 'owner_adoption_performed': False,
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load_marker_script(path: Path):
    assert sha256(path.read_bytes()) == BASE_MARKER_SHA, 'Frozen marker script differs'
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('a2_frozen_dual_e3e108_marker', path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def prepare(original: bytes, marker_module, variant: str):
    """Pure: return baseline108, candidate, marked108, manifest108, checks."""
    assert variant in VARIANTS, 'Unknown fixed diagnostic variant'
    info = VARIANTS[variant]
    assert len(original) == TRACKED_SOURCE_BYTES and sha256(original) == TRACKED_SOURCE_SHA
    assert marker_module.EXPECTED_SOURCE == TRACKED_SOURCE_SHA
    assert marker_module.EXPECTED_MARKED_SHA256 == BASE_MARKED_SHA
    assert marker_module.PREFIX + ' ' == PREFIX
    baseline, base_manifest, base_checks = marker_module.instrument(original)
    assert len(baseline) == BASE_MARKED_BYTES and sha256(baseline) == BASE_MARKED_SHA
    assert len(base_manifest) == base_checks['marker_count'] == 108
    assert base_checks['command_marker_count'] == 41 and base_checks['tactic_marker_count'] == 67
    assert base_checks['all_original_linters_default'] and base_checks['warning_scope_count'] == 0
    assert len(NEW_RW) - len(OLD_RW) == 114 and original.count(OLD_RW) == baseline.count(OLD_RW) == 1
    fixed = original.replace(OLD_RW, NEW_RW, 1)
    fixed_marked = baseline.replace(OLD_RW, NEW_RW, 1)
    assert sha256(fixed) == VARIANTS['default']['candidate_sha256'] and len(fixed) == 18019
    assert sha256(fixed_marked) == VARIANTS['default']['marked_sha256'] and len(fixed_marked) == 26964
    assert fixed.count(ANCHOR) == fixed_marked.count(ANCHOR) == 1 and len(OPTION) == 45
    candidate, marked = fixed, fixed_marked
    if variant == 'phase_warning_control':
        candidate = fixed.replace(ANCHOR, OPTION + ANCHOR, 1)
        marked = fixed_marked.replace(ANCHOR, OPTION + ANCHOR, 1)
    assert len(candidate) == info['candidate_bytes'] and sha256(candidate) == info['candidate_sha256']
    assert len(marked) == info['marked_bytes'] and sha256(marked) == info['marked_sha256']
    assert candidate.count(b'set_option ') == info['warning_scope_count']
    assert marked.count(b'set_option ') == info['warning_scope_count']
    assert candidate.count(OPTION) == info['warning_scope_count']
    if variant == 'phase_warning_control':
        assert candidate.replace(OPTION, b'', 1) == fixed
        assert marked.replace(OPTION, b'', 1) == fixed_marked
        before_header = b'run_cmd IO.eprintln "' + PREFIX.encode() + b'BEFORE_HEADER_phase_cost_eq_budgets_leaves"\n'
        assert (before_header + OPTION + ANCHOR) in marked
    assert fixed.replace(NEW_RW, OLD_RW, 1) == original
    assert fixed_marked.replace(NEW_RW, OLD_RW, 1) == baseline
    assert b'as_aux_lemma' not in candidate
    marker_lines = {m['inserted_line'].encode(): m for m in base_manifest}
    assert len(marker_lines) == 108
    lines = marked.splitlines(keepends=True)
    assert b''.join(line for line in lines if line not in marker_lines) == candidate
    manifest = []
    candidate_line = 1
    for marked_line, line in enumerate(lines, 1):
        if line in marker_lines:
            old = marker_lines[line]
            entry = copy.deepcopy(old)
            entry['e3e_insert_before_line'] = old['original_insert_before_line']
            entry['original_insert_before_line'] = candidate_line
            entry['instrumented_line'] = marked_line
            manifest.append(entry)
        else:
            candidate_line += 1
    assert len(manifest) == 108
    assert [m['label'] for m in manifest] == [m['label'] for m in base_manifest]
    assert [m['inserted_line'] for m in manifest] == [m['inserted_line'] for m in base_manifest]
    reverse = marked
    for m in reversed(manifest):
        line = m['inserted_line'].encode()
        assert reverse.count(line) == 1
        reverse = reverse.replace(line, b'', 1)
    assert reverse == candidate
    forward = []
    for n, line in enumerate(candidate.splitlines(keepends=True), 1):
        forward.extend(m['inserted_line'].encode() for m in manifest if m['original_insert_before_line'] == n)
        forward.append(line)
    forward.extend(m['inserted_line'].encode() for m in manifest if m['original_insert_before_line'] == len(candidate.splitlines()) + 1)
    assert b''.join(forward) == marked
    for start, count in [(b'import ', 3), (b'#print axioms ', 5)]:
        original_lines = [l for l in original.splitlines() if l.startswith(start)]
        assert len(original_lines) == count
        assert original_lines == [l for l in candidate.splitlines() if l.startswith(start)]
        assert original_lines == [l for l in marked.splitlines() if l.startswith(start)]
    # The only original proof edit lies before all ambient variables and public declarations.
    proof_position = original.index(OLD_RW)
    assert original.index(b'private theorem dual_scalar_integral_const_nonzero_const') < proof_position < original.index(b'private theorem dual_scalar_weighted_terminal_sum')
    assert original.index(b'variable {K : Type}') > proof_position
    checks = {
        **FALSE_FLAGS,
        'variant': variant, 'tracked_source_sha256': TRACKED_SOURCE_SHA,
        'tracked_source_bytes': TRACKED_SOURCE_BYTES,
        'baseline_marked_sha256': BASE_MARKED_SHA,
        'fixed_source_sha256': VARIANTS['default']['candidate_sha256'],
        'candidate_source_sha256': info['candidate_sha256'],
        'candidate_source_bytes': info['candidate_bytes'],
        'diagnostic_source_sha256': info['marked_sha256'],
        'diagnostic_source_bytes': info['marked_bytes'],
        'marker_count': 108, 'command_marker_count': 41, 'tactic_marker_count': 67,
        'declaration_count': 17, 'original_import_count': 3, 'original_print_axioms_count': 5,
        'all108_marker_lines_labels_order_byte_preserved': True,
        'candidate_recovered_after_marker_removal_both_ways': True,
        'corrected770bf_recovered_after_optional45_removal': True,
        'tracked_e3e_recovered_after_all_reversals': True,
        'raw_helper_private_proof_edit_count': 1, 'raw_helper_fix_delta_bytes': 114,
        'raw_helper_fix_native_validation_claimed': False,
        'public_heads_data_instances_imports_prints_unchanged': True,
        'doccomment_association_preserved': True,
        'warning_scope_count': info['warning_scope_count'],
        'new_warning_scope_count': info['warning_scope_count'],
        'target_warning_option_override': None if variant == 'default' else {'option': 'linter.unusedSectionVars', 'value': False, 'declaration': SCOPE_TARGET, 'bytes': 45},
        'all_original_linters_default': variant == 'default',
        'all_other_declarations_linters_default': True,
        'global_warning_option_override': None, 'heartbeat_override': None,
        'lean_async_override': None, 'profiler_override': None,
        'full_original_module_copy_used': True,
        'tracked_source_modified': False, 'imported_guard_rebound': False,
        'source_candidate_not_adopted_as_owner_production': True,
    }
    return baseline, candidate, marked, manifest, checks


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--evidence', type=Path, required=True)
    parser.add_argument('--variant', choices=tuple(VARIANTS), required=True)
    args = parser.parse_args()
    repo, evidence = args.repo.resolve(), args.evidence.resolve()
    assert '.lake' not in evidence.parts
    evidence.mkdir(parents=True, exist_ok=True)
    assert not (evidence / 'prepare-result.json').exists(), 'Use fresh evidence'
    original = (repo / SOURCE).read_bytes()
    marker = load_marker_script(repo / BASE_MARKER)
    baseline, candidate, marked, manifest, checks = prepare(original, marker, args.variant)
    (evidence / 'DualGaussHybridTerminal.tracked-e3e.lean').write_bytes(original)
    (evidence / 'DualGaussHybridTerminal.corrected-candidate.lean').write_bytes(candidate)
    (evidence / 'baseline-e3e.marked108.lean').write_bytes(baseline)
    (evidence / (VARIANTS[args.variant]['module'] + '.lean')).write_bytes(marked)
    (evidence / 'marker-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    checks.update(no_process_started=True, source_unchanged=(repo / SOURCE).read_bytes() == original)
    (evidence / 'prepare-result.json').write_text(json.dumps(checks, indent=2) + '\n')
    print(json.dumps({'variant': args.variant, 'no_process_started': True, 'source_unchanged': checks['source_unchanged'], 'acceptance_evidence': False}))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
