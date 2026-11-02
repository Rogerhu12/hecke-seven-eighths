#!/usr/bin/env python3
"""Temporary single-declaration warning comparison for complete Pool65fb.

Read the unchanged pending candidate source and SHA-pinned Pool1d72 marker
module. Call its instrument/execute functions without modifying any guard.
Only a full temporary copy gains one45-byte unusedSectionVars scope before
the phase_cost_eq_budgets_leaves doccomment. All60 original marker lines,
headers, proofs, data, imports and prints remain; the integral declaration
and every other declaration keep default linting. This is not a production
exception or normal/fresh acceptance. Execution preserves150s/10s, strict-j2,
and the original heartbeat and async defaults.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys

sys.dont_write_bytecode = True

BASE_PATH = Path('.github/scripts/mom-engine-step-a2-pool-candidate-diagnostic.py')
BASE_SHA256 = '1d72d98d679ce39be1aa69f676f017c76b19158ba26c0a734e5a9a271c6da17a'
BASE_BYTES = 31925
SOURCE = Path('HeckeSkeleton/Moments/MOM_ENGINE_STEP/PoolFiniteLeaves.lean')
ORIGINAL_SHA256 = '65fbf1b00c8f754277ee04dafb60296549fd630cc6dfa5d1445309ce91718ca1'
ORIGINAL_BYTES = 13433
ORIGINAL_MARKED_SHA256 = '6950559e2cbb0665259b7e3251fad000d5978c8c5934a67e8b72c324de0e8139'
ORIGINAL_MARKED_BYTES = 18167
CANDIDATE_SHA256 = '9a50f4c822c979bc26c6c89cb34e43e0cd9f23b8b34a3ef1f7f0b62c43015b03'
CANDIDATE_BYTES = 13478
CANDIDATE_BLOB = '2236af198e46cb1ddea5d4e0a5751b553dba3325'
MARKED_SHA256 = '16f0d3e8190e36aecab9e11135fb3563473025fd1d6d44ff282de12090534fb8'
MARKED_BYTES = 18212
MARKED_BLOB = '61100bfb51d6e3af84fe4d7533728306d915c332'
DECLARATION = 'HeckeSkeleton.Moments.EngineStep.ActualPoolStages.TerminalCalibration.phase_cost_eq_budgets_leaves'
OPTION = b'set_option linter.unusedSectionVars false in\n'
ANCHOR = b'/-- Exact one-pool source separation, before integrating the common\nfirst Fourier variable.  All local error weights remain literal. -/\ntheorem phase_cost_eq_budgets_leaves\n'
BEFORE_MARKER = b'run_cmd IO.eprintln "A2_OWNER_POOL_DIAGNOSTIC BEFORE_HEADER_phase_cost_eq_budgets_leaves"\n'
FALSE_FLAGS = {
    'acceptance_evidence': False,
    'original_module_native_was_run': False,
    'original_module_acceptance': False,
    'complete_target_module_compiled': False,
    'complete_module_within_five_minutes': False,
    'full_task_acceptance': False,
    'compiler_outputs_can_be_restored_as_project_cache': False,
    'production_approval': False,
    'candidate_native_validation_performed': False,
    'fresh_axiom_audit_performed': False,
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def load_base(path: Path):
    data = path.read_bytes()
    assert len(data) == BASE_BYTES and sha(data) == BASE_SHA256
    spec = importlib.util.spec_from_file_location('pool_frozen_1d72', path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    assert module.EXPECTED_SOURCE == ORIGINAL_SHA256
    assert module.EXPECTED_BYTES == ORIGINAL_BYTES
    assert module.SOURCE == SOURCE
    assert module.EXPECTED_MARKED_SHA256 == ORIGINAL_MARKED_SHA256
    assert module.EXPECTED_MARKED_BYTES == ORIGINAL_MARKED_BYTES
    assert module.TIMEOUT_SECONDS == 150 and module.KILL_AFTER_SECONDS == 10
    assert module.EXPECTED_LEAN_COMMIT == '470d5ce1400764999581fd26d5d72b00d990b0f4'
    assert module.EXPECTED_MATHLIB == '0493595ecd5da8ef14742febab99728f98e948e8'
    return module


def remove_option(source: bytes) -> bytes:
    assert len(OPTION) == 45 and source.count(OPTION) == 1
    assert source.count(OPTION + ANCHOR) == 1
    return source.replace(OPTION + ANCHOR, ANCHOR, 1)


def remove_markers(source: bytes, manifest: list[dict]) -> bytes:
    restored = source
    for entry in manifest:
        marker = entry['inserted_line'].encode()
        assert restored.count(marker) == 1
        restored = restored.replace(marker, b'', 1)
    return restored


def prepare(original: bytes, base_module) -> tuple[bytes, bytes, list[dict], dict]:
    """Pure preparation. No toolchain, subprocess, project edit, or guard mutation."""
    assert len(original) == ORIGINAL_BYTES and sha(original) == ORIGINAL_SHA256
    assert b'set_option ' not in original
    original_marked, old_manifest, old_checks = base_module.instrument(original)
    assert len(original_marked) == ORIGINAL_MARKED_BYTES
    assert sha(original_marked) == ORIGINAL_MARKED_SHA256
    assert len(old_manifest) == 60
    assert original.count(ANCHOR) == original_marked.count(ANCHOR) == 1
    assert original_marked.count(BEFORE_MARKER + ANCHOR) == 1
    candidate = original.replace(ANCHOR, OPTION + ANCHOR, 1)
    marked = original_marked.replace(ANCHOR, OPTION + ANCHOR, 1)
    assert len(candidate) == CANDIDATE_BYTES and sha(candidate) == CANDIDATE_SHA256
    assert len(marked) == MARKED_BYTES and sha(marked) == MARKED_SHA256
    assert marked.count(BEFORE_MARKER + OPTION + ANCHOR) == 1
    assert candidate.count(b'set_option ') == marked.count(b'set_option ') == 1

    # The marker preceding the declaration stays outside the scoped command.
    # The original doccomment and theorem header remain one contiguous block.
    marker_lines = [entry['inserted_line'].encode() for entry in old_manifest]
    marked_lines = marked.splitlines(keepends=True)
    assert len(set(marker_lines)) == 60
    assert [line for line in marked_lines if line in marker_lines] == marker_lines
    manifest = []
    for entry in old_manifest:
        item = dict(entry)
        item['original_instrumented_line'] = item['instrumented_line']
        item['instrumented_line'] = marked_lines.index(item['inserted_line'].encode()) + 1
        manifest.append(item)
    assert remove_option(candidate) == original
    assert remove_option(marked) == original_marked
    assert remove_markers(marked, manifest) == candidate
    assert remove_option(remove_markers(marked, manifest)) == original
    assert remove_markers(remove_option(marked), old_manifest) == original
    assert candidate.replace(OPTION, b'', 1).splitlines(keepends=True) == original.splitlines(keepends=True)
    for prefix in (b'import ', b'#print axioms '):
        assert [line for line in marked_lines if line.startswith(prefix)] == [
            line for line in original.splitlines(keepends=True) if line.startswith(prefix)]
    # The entire remaining theorem and original end-of-file prints are unchanged.
    assert candidate[candidate.index(ANCHOR):] == original[original.index(ANCHOR):]
    assert candidate[:candidate.index(OPTION)] == original[:original.index(ANCHOR)]

    checks = dict(old_checks)
    checks.update({
        'all_original_linters_default': False,
        'all_other_linters_default': True,
        'all_other_declarations_all_linters_default': True,
        'new_warning_scope_count': 1,
        'warning_scope_count': 1,
        'temporary_warning_scopes': [DECLARATION],
        'temporary_warning_option': 'linter.unusedSectionVars',
        'temporary_warning_value': False,
        'warning_scope_is_before_original_doccomment': True,
        'scope_does_not_cover_before_header_marker': True,
        'all_original_marker_lines_and_order_preserved': True,
        'both_reversal_orders_verified': True,
        'candidate_source_sha256': sha(candidate),
        'candidate_source_bytes': len(candidate),
        'candidate_git_blob': CANDIDATE_BLOB,
        'original_diagnostic_source_sha256': sha(original_marked),
        'original_diagnostic_source_bytes': len(original_marked),
        'diagnostic_source_sha256': sha(marked),
        'diagnostic_source_bytes': len(marked),
        'diagnostic_source_git_blob': MARKED_BLOB,
        'option_inserted_bytes': 45,
        'option_inserted_original_byte': original.index(ANCHOR),
        'original_1d72_guard_mutations': False,
        'original_1d72_executor_reused_unchanged': True,
    })
    return candidate, marked, manifest, checks


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--evidence', type=Path, required=True)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    repo, evidence = args.repo.resolve(), args.evidence.resolve()
    assert '.lake' not in evidence.parts
    evidence.mkdir(parents=True, exist_ok=True)
    assert not (evidence / 'result.json').exists(), 'Use a fresh evidence directory'
    original = (repo / SOURCE).read_bytes()
    base_path = repo / BASE_PATH
    base_bytes = base_path.read_bytes()
    base = load_base(base_path)
    candidate, marked, manifest, checks = prepare(original, base)
    owner_source = base.restore_owner_source(original)
    assert len(owner_source) == 8576 and sha(owner_source) == '7fafdf5687b18cf53f9e6f4792e999198a0ab875396376690e1c625f0a718c01'
    (evidence / 'PoolFiniteLeaves.owner-original.lean').write_bytes(owner_source)
    (evidence / 'PoolFiniteLeaves.original-candidate.lean').write_bytes(original)
    (evidence / 'PoolFiniteLeaves.temporary-phase-warning.lean').write_bytes(candidate)
    (evidence / (base.MODULE + '.lean')).write_bytes(marked)
    write_json(evidence / 'marker-manifest.json', manifest)
    result = {
        **FALSE_FLAGS, **checks,
        'scope': 'Diagnostic-only single phase-declaration warning comparison in the complete temporary Pool65fb source',
        'production_source_and_proof_owner': 'A2/owner',
        'production_warning_exception_approved': False,
        'candidate_source_accepted_by_owner': False,
        'fintype_cache_owner_approval_comment': 6567091453,
        'source_path': str(SOURCE),
        'source_sha256': sha(original), 'source_bytes': len(original),
        'source_base_head': '1d8375a7b6c05f6c30c2b1523b195dc072d574b2',
        'source_base_tree': 'b5bddfe7f9bb663212dd9d459e14322b46e9b48c',
        'source_git_blob': base.SOURCE_BLOB,
        'diagnostic_script_sha256': sha(Path(__file__).read_bytes()),
        'base_diagnostic_script_sha256': sha(base_bytes),
        'executor_base_script_sha256': base.EXECUTOR_BASE_SCRIPT_SHA256,
        'executor_adapted_function_sha256': base.EXECUTOR_ADAPTED_FUNCTION_SHA256,
        'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'heartbeat_override': None, 'lean_async_override': None,
        'profiler_override': None, 'stderr_option_override': False,
        'stderr_option_reason': 'Original Pool1d72 diagnostic marker transport only',
        'warning_option_override': {
            'option': 'linter.unusedSectionVars', 'value': False,
            'declaration': DECLARATION, 'diagnostic_only': True,
        },
        'other_warning_option_override': None,
        'global_warning_option_override': None,
        'timeout_seconds': base.TIMEOUT_SECONDS,
        'kill_after_seconds': base.KILL_AFTER_SECONDS,
        'lean_job_count': 2,
        'started': False, 'status': 'prepared_only', 'timed_out': False,
        'marker_times_are_observed_arrival_only': True,
        'marker_interpretation': 'Actual arrivals only: command continuation can follow error recovery; inspect the full compiler output and raw GDB MI before inferring proof completion.',
    }
    write_json(evidence / 'result.json', result)
    try:
        if args.run:
            assert os.environ.get('LEAN_NUM_THREADS') == '2'
            base.execute(repo, evidence, marked, result)
    except BaseException as exc:
        result.update(status='diagnostic_harness_error', harness_error=repr(exc))
        raise
    finally:
        result['original_source_unchanged'] = (repo / SOURCE).read_bytes() == original
        result['frozen_base_script_unchanged'] = base_path.read_bytes() == base_bytes
        assert result['original_source_unchanged'] and result['frozen_base_script_unchanged']
        result.update(FALSE_FLAGS)
        write_json(evidence / 'result.json', result)
    print(json.dumps({key: result[key] for key in [
        'status', 'source_sha256', 'candidate_source_sha256',
        'diagnostic_source_sha256', 'marker_count', 'both_reversal_orders_verified',
        'original_source_unchanged', 'frozen_base_script_unchanged',
        'acceptance_evidence', 'production_approval',
    ]}, ensure_ascii=False), flush=True)
    if args.run and result.get('timed_out'):
        return 124
    code = result.get('diagnostic_exit_code', 0)
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
