#!/usr/bin/env python3
"""Prepare/run the reversible full 309ee provider-alias diagnostic (65 markers).

The frozen cd734 preparation and 0858 execution modules remain unchanged.
This changes only the proposed private scalar alias, the private provider LHS,
and the public phase proof's explicit transitivity middle term. Every runtime
option and acceptance restriction is inherited from the frozen executor.
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
PREVIOUS_SCRIPT = Path('.github/scripts/mom-engine-step-a2-provider-instances-diagnostic.py')
PREVIOUS_SHA = 'cd7347b54d162d3d9039d6875bf307bb120c30d8479f865e99ba9341f8b87c26'
SOURCE_SHA = 'cc98c8a2c5c3c3f6c59695935245f463c84e6e7f7c8292b5062e2d1813d94c87'
PREVIOUS_CANDIDATE_SHA = '15faa083030a9edd0af1ba7dcbfb91e43044b902f8bdabd88bbf69ad765c13de'
PREVIOUS_MARKED_SHA = 'd4fab1e84c9f408c2ca8d05f996549cff532fe6e4918ff7598de0856e5a6a0ec'
CANDIDATE_SHA = '309ee42e606a08446937299a01e198b75936aafa6f60f629f24de74981b7e610'
CANDIDATE_BLOB = '981a98f24b0b7db7958d73f9524f6960b878a020'
MARKED_SHA = '9d63df8e75aed37db3913d650bd4f0c90e5e4206a70972f158a7b6242bc63009'
LHS_SHA = '38ccec121d7c2341ce6a955954ce70c6bbd8d08b43a387ddcdb64f624c56256a'
PROVIDER_HEADER = b'private theorem fixed_fullCorrelation_eq_leaf_sum\n'
ALIAS_HEADER = (
    'private def fixedClassFullCorrelation\n'
    '    (exceptional : s.CoverHybridPredicates LC RC)\n'
    '    (x : ι → W) (ξ : W) : ℝ :=\n').encode()
ALIAS_CALL = '    v.fixedClassFullCorrelation exceptional x ξ'.encode()
OLD_INNER_PROOF = (
    '    exact (v.phase_class_eq_fixed_fullCorrelation exceptional x ξ).trans\n'
    '      (v.fixed_fullCorrelation_eq_leaf_sum exceptional F x ξ)\n').encode()
NEW_INNER_PROOF = (
    '    exact Eq.trans\n'
    '      (b := v.fixedClassFullCorrelation exceptional x ξ)\n'
    '      (v.phase_class_eq_fixed_fullCorrelation exceptional x ξ)\n'
    '      (v.fixed_fullCorrelation_eq_leaf_sum exceptional F x ξ)\n').encode()
NEW_LABELS = ['BEFORE_HEADER_fixedClassFullCorrelation',
              'COMMAND_CONTINUED_AFTER_fixedClassFullCorrelation']
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
    path = repo / PREVIOUS_SCRIPT
    assert sha(path.read_bytes()) == PREVIOUS_SHA
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('a2_frozen_explicit_provider_prepare', path)
    assert spec is not None and spec.loader is not None
    previous = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(previous)
    two, module = previous.load_frozen(repo)
    assert previous.FALSE_FLAGS == two.FALSE_FLAGS == module.ACCEPTANCE == FALSE_FLAGS
    return previous, two, module


def guard_snapshot(previous, two, module):
    return (previous.guard_snapshot(module),
            previous.SOURCE_SHA, previous.CANDIDATE_SHA, previous.MARKED_SHA,
            previous.PREVIOUS_SHA if hasattr(previous, 'PREVIOUS_SHA') else None,
            previous.TWO_SHA, previous.MARKER_SHA,
            json.dumps(two.FALSE_FLAGS, sort_keys=True))


def provider_lhs(data: bytes) -> bytes:
    assert data.count(PROVIDER_HEADER) == 1
    begin = data.index(PROVIDER_HEADER)
    start = data.index(b'    fullCorrelationHybridCost\n', begin)
    end = data.index(' =\n      ∑ j : v.AllocationKey,'.encode(), start)
    lhs = data[start:end]
    assert len(lhs) == 2048 and sha(lhs) == LHS_SHA
    return lhs


def replace_provider_lhs(data: bytes, before: bytes, after: bytes) -> bytes:
    start = data.index(PROVIDER_HEADER)
    pos = data.index(before, start)
    assert pos < data.index(b':= by\n', start)
    return data[:pos] + after + data[pos + len(before):]


def prepare(original: bytes, previous, two, module):
    """Pure: previous_candidate, previous63, candidate309, marked65, manifest, checks."""
    guards = guard_snapshot(previous, two, module)
    assert guards[0][:4] == (SOURCE_SHA, 40282, 150, 10)
    baseline60, old_candidate, old_marked, old_manifest, _ = previous.prepare(original, two, module)
    assert guard_snapshot(previous, two, module) == guards
    assert len(old_candidate) == 40507 and sha(old_candidate) == PREVIOUS_CANDIDATE_SHA
    assert len(old_marked) == 46132 and sha(old_marked) == PREVIOUS_MARKED_SHA
    assert len(old_manifest) == 63
    lhs = provider_lhs(old_candidate)
    assert provider_lhs(old_marked) == lhs
    alias = ALIAS_HEADER + lhs + b'\n\n'
    assert len(alias) == 2175 and len(ALIAS_CALL) == 48
    assert alias not in old_candidate and alias not in old_marked
    anchor = previous.OMIT + PROVIDER_HEADER
    assert old_candidate.count(anchor) == 1
    assert old_candidate.count(OLD_INNER_PROOF) == old_marked.count(OLD_INNER_PROOF) == 1
    candidate = old_candidate.replace(anchor, alias + anchor, 1)
    candidate = replace_provider_lhs(candidate, lhs, ALIAS_CALL)
    candidate = candidate.replace(OLD_INNER_PROOF, NEW_INNER_PROOF, 1)
    assert len(candidate) == 40749 and sha(candidate) == CANDIDATE_SHA
    assert blob(candidate) == CANDIDATE_BLOB

    def command(label: str) -> bytes:
        return ('run_cmd IO.eprintln ' + json.dumps(module.PREFIX + ' ' + label) + '\n').encode()

    additions = [command(label) for label in NEW_LABELS]
    provider_before = command('BEFORE_HEADER_fixed_fullCorrelation_eq_leaf_sum')
    marked_anchor = provider_before + anchor
    assert old_marked.count(marked_anchor) == 1
    assert all(line not in old_marked for line in additions)
    marked = old_marked.replace(marked_anchor,
        additions[0] + alias + additions[1] + marked_anchor, 1)
    marked = replace_provider_lhs(marked, lhs, ALIAS_CALL)
    marked = marked.replace(OLD_INNER_PROOF, NEW_INNER_PROOF, 1)
    assert len(marked) == 46560 and sha(marked) == MARKED_SHA
    assert b'set_option' not in candidate and b'set_option' not in marked
    assert marked.count(previous.OMIT) == 2 and marked.count(previous.BINDER) == 1
    assert marked.count(provider_before + previous.OMIT + PROVIDER_HEADER) == 1
    assert marked.count(additions[0] + alias + additions[1]) == 1
    assert marked.count(b'  as_aux_lemma =>\n') == 1

    manifest = []
    for entry in old_manifest:
        line = entry['inserted_line'].encode()
        assert marked.count(line) == 1
        updated = dict(entry)
        updated.update(prior_63_instrumented_line=entry['instrumented_line'],
            instrumented_line=marked[:marked.index(line)].count(b'\n') + 1,
            is_added_provider_alias_marker=False)
        manifest.append(updated)
    for label, line, boundary in zip(NEW_LABELS, additions,
            ['before new private scalar alias header',
             'command continues after checking new private scalar alias']):
        manifest.append({
            'label': label, 'inserted_line': line.decode(), 'kind': 'command',
            'instrumented_line': marked[:marked.index(line)].count(b'\n') + 1,
            'origin': 'provider_alias_65_extension',
            'is_added_provider_alias_marker': True, 'boundary': boundary})
    manifest.sort(key=lambda entry: entry['instrumented_line'])
    assert len(manifest) == 65
    assert [entry['label'] for entry in manifest if not entry['is_added_provider_alias_marker']] == \
        [entry['label'] for entry in old_manifest]
    marker_lines = {entry['inserted_line'].encode() for entry in manifest}
    assert len(marker_lines) == 65
    lines = marked.splitlines(keepends=True)
    assert sum(module.PREFIX.encode() in line for line in lines) == 65
    assert all(lines[entry['instrumented_line'] - 1] == entry['inserted_line'].encode()
               for entry in manifest)
    remove_markers = lambda data: b''.join(
        line for line in data.splitlines(keepends=True) if line not in marker_lines)
    assert remove_markers(marked) == candidate

    def undo_alias(data: bytes) -> bytes:
        assert data.count(alias) == data.count(NEW_INNER_PROOF) == 1
        data = data.replace(alias, b'', 1)
        data = replace_provider_lhs(data, ALIAS_CALL, lhs)
        return data.replace(NEW_INNER_PROOF, OLD_INNER_PROOF, 1)

    assert undo_alias(candidate) == old_candidate
    back = marked
    for line in additions:
        assert back.count(line) == 1
        back = back.replace(line, b'', 1)
    assert undo_alias(back) == old_marked
    undo_to_original = lambda data: previous.undo_headers(data.replace(
        previous.wrap_public(previous.PUBLIC_PROOF), previous.PUBLIC_PROOF, 1))
    assert undo_to_original(undo_alias(candidate)) == original
    assert undo_to_original(undo_alias(remove_markers(marked))) == original
    for prefix in [b'import ', b'#print axioms ']:
        assert [line for line in lines if line.startswith(prefix)] == \
            [line for line in original.splitlines(keepends=True) if line.startswith(prefix)]
    assert guard_snapshot(previous, two, module) == guards
    checks = {
        'marker_count': 65, 'previous_marker_count': 63,
        'additional_markers_beyond_previous': 2, 'new_marker_labels': NEW_LABELS,
        'all_previous_63_labels_and_marker_lines_preserved': True,
        'new_markers_are_command_boundaries': True,
        'alias_body_equals_previous_provider_lhs': True, 'alias_definition_bytes': len(alias),
        'provider_old_lhs_bytes': len(lhs), 'provider_alias_call_bytes': len(ALIAS_CALL),
        'provider_original_exact_not_wrapped': True,
        'marker_removal_recovers_candidate': True,
        'candidate_reverse_recovers_previous_candidate': True,
        'candidate_reverse_recovers_original': True,
        'reverse_source_changes_recovers_previous_63_marker_input': True,
        'two_way_reversal_verified': True,
        'phase_omit_bytes': 69, 'provider_omit_bytes': 69,
        'provider_explicit_binder_bytes': 65,
        'warning_override': None, 'warning_option_override': None,
        'global_warning_option_override': None, 'module_guards_unchanged': True,
    }
    return old_candidate, old_marked, candidate, marked, manifest, checks


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
    previous, two, module = load_frozen(repo)
    guards = guard_snapshot(previous, two, module)
    old_candidate, old_marked, candidate, marked, manifest, checks = prepare(
        original, previous, two, module)
    for name, data in [
        ('ActualGaussFiniteLeaves.original.lean', original),
        ('ActualGaussFiniteLeaves.previous-15faa-candidate.lean', old_candidate),
        ('ActualGaussFiniteLeaves.provider-alias-candidate.lean', candidate),
        ('previous-explicit-provider63.lean', old_marked),
        (module.MODULE + '.lean', marked)]:
        (evidence / name).write_bytes(data)
    write_json(evidence / 'marker-manifest.json', manifest)
    result = {
        **FALSE_FLAGS, **checks,
        'scope': 'Full temporary 309ee copy with 65 markers; diagnostic only',
        'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_path': str(SOURCE), 'source_sha256': sha(original), 'source_bytes': len(original),
        'previous_wrapper_path': str(PREVIOUS_SCRIPT), 'previous_wrapper_sha256': PREVIOUS_SHA,
        'two_wrapper_path': str(previous.TWO_SCRIPT), 'two_wrapper_sha256': previous.TWO_SHA,
        'marker_script_path': str(previous.MARKER_SCRIPT), 'marker_script_sha256': previous.MARKER_SHA,
        'previous_63_marker_sha256': sha(old_marked),
        'previous_candidate_sha256': sha(old_candidate),
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
            assert guard_snapshot(previous, two, module) == guards
            module.execute(repo, evidence, marked, result)
    except BaseException as exc:
        result.update(status='diagnostic_harness_error', harness_error=repr(exc))
        raise
    finally:
        result['original_source_unchanged'] = (repo / SOURCE).read_bytes() == original
        result['previous_wrapper_unchanged'] = sha((repo / PREVIOUS_SCRIPT).read_bytes()) == PREVIOUS_SHA
        result['two_wrapper_unchanged'] = sha((repo / previous.TWO_SCRIPT).read_bytes()) == previous.TWO_SHA
        result['marker_script_unchanged'] = sha((repo / previous.MARKER_SCRIPT).read_bytes()) == previous.MARKER_SHA
        result['module_guards_unchanged'] = guard_snapshot(previous, two, module) == guards
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
