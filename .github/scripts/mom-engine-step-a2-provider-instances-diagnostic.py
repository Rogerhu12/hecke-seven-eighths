#!/usr/bin/env python3
"""Prepare or run the reversible 15faa explicit-provider, 63-marker diagnostic.

The frozen 0858 executor and 625e two-warning preparation module are reused
unchanged. Both temporary warning options are removed before transformation.
Only the private phase/provider parameter organization and the public phase
proof packaging change. All acceptance flags remain false.
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

SOURCE = Path('HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualGaussFiniteLeaves.lean')
TWO_SCRIPT = Path('.github/scripts/mom-engine-step-a2-two-private-warnings.py')
TWO_SHA = '625e9615dee0c1385d403089dcf6830c537ec97f08e9cf58793528cbdf7a2699'
MARKER_SCRIPT = Path('.github/scripts/mom-engine-step-a2-diagnostic.py')
MARKER_SHA = '0858bc9e93b1ba60a6d45ae39e694149001689fa29bfd1928ffcaa9696e95ed3'
SOURCE_SHA = 'cc98c8a2c5c3c3f6c59695935245f463c84e6e7f7c8292b5062e2d1813d94c87'
BASELINE_SHA = '0d1704b1dd1c539ca1aa0d44cd54aa37c8b01a04dc0e2e7b1722b68f33b33d3c'
CANDIDATE_SHA = '15faa083030a9edd0af1ba7dcbfb91e43044b902f8bdabd88bbf69ad765c13de'
CANDIDATE_BLOB = '4191dc119bc491d4055c6a580d16cc140f80d6ca'
MARKED_SHA = 'd4fab1e84c9f408c2ca8d05f996549cff532fe6e4918ff7598de0856e5a6a0ec'
OPTION = b'set_option linter.unusedSectionVars false in\n'
OMIT = 'omit [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] in\n'.encode()
BINDER = '    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]\n'.encode()
PHASE_HEADER = b'private theorem phase_class_eq_fixed_fullCorrelation\n'
PROVIDER_HEADER = b'private theorem fixed_fullCorrelation_eq_leaf_sum\n'
PHASE_LAST = b'    hkernel hrows hrowCoefficient hleftCoefficient hrightCoefficient hleftPoint hrightPoint\n'
PUBLIC_PROOF = (
    '  exact (v.phase_class_eq_fixed_fullCorrelation exceptional x ξ).trans\n'
    '    (v.fixed_fullCorrelation_eq_leaf_sum exceptional F x ξ)\n').encode()
NEW_LABELS = ['PHASE_AFTER_EXACT_SEVEN_ARGUMENT_CONGR',
              'AFTER_PUBLIC_PHASE_EXACT', 'AFTER_PUBLIC_PHASE_AUX']
FALSE_FLAGS = {
    'acceptance_evidence': False,
    'original_module_native_was_run': False,
    'original_module_acceptance': False,
    'complete_target_module_compiled': False,
    'complete_module_within_five_minutes': False,
    'full_task_acceptance': False,
    'compiler_outputs_can_be_restored_as_project_cache': False,
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def write_json(path: Path, data) -> None:
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')


def load_frozen(repo: Path):
    path = repo / TWO_SCRIPT
    assert sha(path.read_bytes()) == TWO_SHA
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('a2_frozen_two_warning_prepare', path)
    assert spec is not None and spec.loader is not None
    two = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(two)
    module = two.load_marker_script(repo / MARKER_SCRIPT)
    assert sha((repo / MARKER_SCRIPT).read_bytes()) == MARKER_SHA
    assert two.FALSE_FLAGS == module.ACCEPTANCE == FALSE_FLAGS
    return two, module


def guard_snapshot(module):
    return (module.EXPECTED_SOURCE, module.EXPECTED_BYTES, module.TIMEOUT_SECONDS,
            module.KILL_AFTER_SECONDS, module.MODULE, module.PREFIX,
            json.dumps(module.ACCEPTANCE, sort_keys=True))


def wrap_public(proof: bytes) -> bytes:
    assert proof.endswith(b'\n')
    return b'  as_aux_lemma =>\n' + b''.join(
        b'  ' + line for line in proof.splitlines(keepends=True))


def organize_headers(data: bytes) -> bytes:
    assert data.count(PHASE_HEADER) == data.count(PROVIDER_HEADER) == 1
    assert OMIT not in data and BINDER not in data
    return data.replace(PHASE_HEADER, OMIT + PHASE_HEADER, 1).replace(
        PROVIDER_HEADER, OMIT + PROVIDER_HEADER + BINDER, 1)


def undo_headers(data: bytes) -> bytes:
    assert data.count(OMIT + PHASE_HEADER) == 1
    assert data.count(OMIT + PROVIDER_HEADER + BINDER) == 1
    return data.replace(OMIT + PHASE_HEADER, PHASE_HEADER, 1).replace(
        OMIT + PROVIDER_HEADER + BINDER, PROVIDER_HEADER, 1)


def prepare(original: bytes, two, module):
    """Pure: return old_two_warning60, candidate15faa, marked63, manifest, checks."""
    assert len(original) == 40282 and sha(original) == SOURCE_SHA
    assert len(OMIT) == 69 and len(BINDER) == 65 and len(OPTION) == 45
    assert OPTION not in original and original.count(PUBLIC_PROOF) == 1
    guards = guard_snapshot(module)
    assert guards[:4] == (SOURCE_SHA, 40282, 150, 10)
    _, _, baseline, old_manifest, _ = two.prepare(original, module)
    assert guard_snapshot(module) == guards
    assert len(baseline) == 45756 and sha(baseline) == BASELINE_SHA
    assert len(old_manifest) == 60 and baseline.count(OPTION) == 2

    def marker(label: str, indent: int) -> bytes:
        return (' ' * indent + 'run_tac IO.eprintln ' +
                json.dumps(module.PREFIX + ' ' + label) + '\n').encode()

    before_public = marker('PHASE_PUBLIC_BEFORE_EXACT', 2)
    additions = [marker(NEW_LABELS[0], 2), marker(NEW_LABELS[1], 4),
                 marker(NEW_LABELS[2], 2)]
    assert baseline.count(before_public + PUBLIC_PROOF) == 1
    assert baseline.count(PHASE_LAST) == 1
    assert all(line not in baseline for line in additions)
    candidate = organize_headers(original).replace(PUBLIC_PROOF, wrap_public(PUBLIC_PROOF), 1)
    assert len(candidate) == 40507 and sha(candidate) == CANDIDATE_SHA
    assert blob(candidate) == CANDIDATE_BLOB
    marked = organize_headers(baseline.replace(OPTION, b'', 2))
    marked = marked.replace(PHASE_LAST, PHASE_LAST + additions[0], 1)
    marked = marked.replace(before_public + PUBLIC_PROOF,
                            wrap_public(before_public + PUBLIC_PROOF) +
                            additions[1] + additions[2], 1)
    assert len(marked) == 46132 and sha(marked) == MARKED_SHA
    assert b'set_option' not in candidate and b'set_option' not in marked
    assert marked.count(OMIT) == 2 and marked.count(BINDER) == 1
    assert marked.count(b'  as_aux_lemma =>\n') == 1

    # Both omit commands follow the existing before-header marker. The provider's
    # three explicit binders belong to its own telescope before exceptional.
    for header, label in [(PHASE_HEADER, 'phase_class_eq_fixed_fullCorrelation'),
                          (PROVIDER_HEADER, 'fixed_fullCorrelation_eq_leaf_sum')]:
        command = ('run_cmd IO.eprintln ' + json.dumps(
            module.PREFIX + ' BEFORE_HEADER_' + label) + '\n').encode()
        assert marked.count(command + OMIT + header) == 1
    assert marked.count(OMIT + PROVIDER_HEADER + BINDER +
                        b'    (exceptional : s.CoverHybridPredicates LC RC)\n') == 1

    manifest = []
    for entry in old_manifest:
        updated = dict(entry)
        previous = entry['inserted_line'].encode()
        current = b'  ' + previous if entry['label'] == 'PHASE_PUBLIC_BEFORE_EXACT' else previous
        assert marked.count(current) == 1
        updated.update(
            prior_two_warning_instrumented_line=entry['instrumented_line'],
            prior_inserted_line=entry['inserted_line'],
            inserted_line=current.decode(),
            instrumented_line=marked[:marked.index(current)].count(b'\n') + 1,
            is_added_explicit_provider_marker=False,
            public_aux_indent_changed=(current != previous))
        manifest.append(updated)
    for label, line, original_line, boundary in zip(
            NEW_LABELS, additions, [434, 516, 516],
            ['phase exact returned', 'public exact returned inside auxiliary proof',
             'public as_aux_lemma returned']):
        assert marked.count(line) == 1
        manifest.append({
            'label': label, 'inserted_line': line.decode(), 'kind': 'tactic',
            'original_insert_before_line': original_line,
            'instrumented_line': marked[:marked.index(line)].count(b'\n') + 1,
            'origin': 'explicit_provider_63_extension',
            'is_added_explicit_provider_marker': True, 'boundary': boundary})
    manifest.sort(key=lambda entry: entry['instrumented_line'])
    assert len(manifest) == 63
    assert [entry['label'] for entry in manifest if not entry['is_added_explicit_provider_marker']] == \
        [entry['label'] for entry in old_manifest]
    marker_lines = {entry['inserted_line'].encode() for entry in manifest}
    assert len(marker_lines) == 63
    lines = marked.splitlines(keepends=True)
    assert all(lines[entry['instrumented_line'] - 1] == entry['inserted_line'].encode()
               for entry in manifest)
    assert sum(module.PREFIX.encode() in line for line in lines) == 63
    remove_markers = lambda data: b''.join(
        line for line in data.splitlines(keepends=True) if line not in marker_lines)
    assert remove_markers(marked) == candidate
    assert undo_headers(candidate.replace(wrap_public(PUBLIC_PROOF), PUBLIC_PROOF, 1)) == original

    # Independently reverse source changes while keeping the old markers, then
    # recover the exact previous 0d1704 input and the original cc98 source.
    back = marked
    for line in additions:
        back = back.replace(line, b'', 1)
    back = back.replace(wrap_public(before_public + PUBLIC_PROOF), before_public + PUBLIC_PROOF, 1)
    back = undo_headers(back)
    old_marker_lines = {entry['inserted_line'].encode() for entry in old_manifest}
    assert b''.join(line for line in back.splitlines(keepends=True)
                    if line not in old_marker_lines) == original
    assert back.replace(PHASE_HEADER, OPTION + PHASE_HEADER, 1).replace(
        PROVIDER_HEADER, OPTION + PROVIDER_HEADER, 1) == baseline
    for prefix in [b'import ', b'#print axioms ']:
        assert [line for line in lines if line.startswith(prefix)] == \
            [line for line in original.splitlines(keepends=True) if line.startswith(prefix)]
    assert guard_snapshot(module) == guards
    checks = {
        'marker_count': 63, 'frozen_original_marker_count': 59,
        'previous_marker_count': 60, 'additional_markers_beyond_previous': 3,
        'all_previous_60_labels_preserved': True, 'new_marker_labels': NEW_LABELS,
        'public_before_marker_indented_inside_aux': True,
        'provider_original_exact_not_wrapped': True,
        'two_way_reversal_verified': True,
        'marker_removal_recovers_candidate': True,
        'candidate_reverse_recovers_original': True,
        'reverse_source_changes_recovers_previous_60_marker_input': True,
        'phase_omit_bytes': 69, 'provider_omit_bytes': 69,
        'provider_explicit_binder_bytes': 65, 'warning_override': None,
        'warning_option_override': None, 'global_warning_option_override': None,
        'module_guards_unchanged': True, 'all_existing_public_headers_defs_preserved': True,
    }
    return baseline, candidate, marked, manifest, checks


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True, type=Path)
    parser.add_argument('--evidence', required=True, type=Path)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    repo, evidence = args.repo.resolve(), args.evidence.resolve()
    assert '.lake' not in evidence.parts
    evidence.mkdir(parents=True, exist_ok=True)
    assert not (evidence / 'result.json').exists(), 'Use a fresh evidence directory'
    original = (repo / SOURCE).read_bytes()
    two, module = load_frozen(repo)
    guards = guard_snapshot(module)
    baseline, candidate, marked, manifest, checks = prepare(original, two, module)
    for name, data in [
        ('ActualGaussFiniteLeaves.original.lean', original),
        ('ActualGaussFiniteLeaves.explicit-provider-candidate.lean', candidate),
        ('previous-two-warning60.lean', baseline),
        (module.MODULE + '.lean', marked)]:
        (evidence / name).write_bytes(data)
    write_json(evidence / 'marker-manifest.json', manifest)
    result = {
        **FALSE_FLAGS, **checks,
        'scope': 'Full temporary 15faa copy with 63 markers; diagnostic only',
        'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_path': str(SOURCE), 'source_sha256': sha(original), 'source_bytes': len(original),
        'two_wrapper_path': str(TWO_SCRIPT), 'two_wrapper_sha256': TWO_SHA,
        'marker_script_path': str(MARKER_SCRIPT), 'marker_script_sha256': MARKER_SHA,
        'previous_60_marker_sha256': sha(baseline),
        'candidate_sha256': sha(candidate), 'candidate_bytes': len(candidate),
        'candidate_git_blob': blob(candidate),
        'diagnostic_source_sha256': sha(marked), 'diagnostic_source_bytes': len(marked),
        'heartbeat_override': None, 'lean_async_override': None, 'profiler_override': None,
        'stderr_option_override': False, 'other_warning_option_override': None,
        'production_approval': False, 'candidate_native_validation_performed': False,
        'timeout_seconds': 150, 'kill_after_seconds': 10, 'lean_job_count': 2,
        'started': False, 'status': 'prepared_only', 'timed_out': False,
        'marker_times_are_observed_arrival_only': True,
    }
    write_json(evidence / 'result.json', result)
    try:
        if args.run:
            assert os.environ.get('LEAN_NUM_THREADS') == '2'
            assert guard_snapshot(module) == guards
            module.execute(repo, evidence, marked, result)
    except BaseException as exc:
        result.update(status='diagnostic_harness_error', harness_error=repr(exc))
        raise
    finally:
        result['original_source_unchanged'] = (repo / SOURCE).read_bytes() == original
        result['two_wrapper_unchanged'] = sha((repo / TWO_SCRIPT).read_bytes()) == TWO_SHA
        result['marker_script_unchanged'] = sha((repo / MARKER_SCRIPT).read_bytes()) == MARKER_SHA
        result['module_guards_unchanged'] = guard_snapshot(module) == guards
        result.update(FALSE_FLAGS)
        write_json(evidence / 'result.json', result)
    print(json.dumps({key: result[key] for key in [
        'status', 'source_sha256', 'candidate_sha256', 'diagnostic_source_sha256',
        'marker_count', 'two_way_reversal_verified', 'warning_override',
        'original_source_unchanged', 'module_guards_unchanged', 'acceptance_evidence']},
        ensure_ascii=False), flush=True)
    if args.run and result.get('timed_out'):
        return 124
    code = result.get('diagnostic_exit_code', 0)
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())

