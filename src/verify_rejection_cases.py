#!/usr/bin/env python3
"""Regression checks at the proof-package trust boundaries.

Every corruption is made in a temporary copy. The delivered certificates and
data are never edited. These tests establish fail-closed behavior for concrete
failure modes; they neither replace the exact verifier nor prove its code free
of every possible bug.
"""
from __future__ import annotations

import _bootstrap  # local CLI module paths only

import argparse
from contextlib import contextmanager
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)


def run():
    if not __debug__:
        raise RuntimeError('The rejection tests require assertions and refuse optimized Python.')
    from rationalize_certificate import verify_certificate
    from verify_certificate_independent import verify as independent
    from generate_equality_spans import verify_spans
    from verify_combinatorial_inputs import verify as recount
    from verify_stored_artifacts import verify_structural_views, verify_finite_views, StoredArtifactMismatch
    from verify_finite import run as finite
    from verify_profiles import run as profiles
    from release_integrity import VERIFIED_STATUS, VerificationStateError, fingerprints, verify_current

    cases = []
    def reject(name, callback, errors=(AssertionError, ValueError), contains=None):
        try:
            callback()
        except errors as exc:
            if contains is not None and contains not in str(exc):
                raise RuntimeError(f'{name}: failed for an unexpected reason: {exc}') from exc
            cases.append({'case': name, 'status': 'rejected_as_required',
                          'exception_type': type(exc).__name__, 'detail': str(exc)[:350]})
        else:
            raise RuntimeError(f'{name}: a deliberately invalid input was accepted')

    with tempfile.TemporaryDirectory(prefix='pentagon-rejection-') as temporary:
        work = Path(temporary)
        data = work / 'certificates'
        data.mkdir()
        for path in (ROOT / 'certificates').iterdir():
            if path.is_file() and not path.name.startswith('symmetry_blocks'):
                shutil.copy2(path, data / path.name)
        cert = data / 'all_graph_exact_certificate.json'
        triangle = data / 'all_graph_path3_triangle_domination_span.json'
        degree = data / 'all_graph_tf_degree_codegree_spans.json'
        finite_result, profile_result = finite(), profiles()
        offsets = json.loads((data / 'eventual_polynomials_small_offsets.json').read_text())
        # Positive controls rule out a missing dependency or broken fixture as
        # the explanation for the intended rejection of a later mutation.
        verify_certificate(cert, data)
        independent(cert, data)
        verify_spans(cert, triangle, degree, data_dir=data)
        recount(data)
        verify_structural_views(data)
        verify_finite_views(data, finite_result, profile_result, offsets)

        @contextmanager
        def json_mutation(path, mutate):
            original = path.read_bytes()
            obj = json.loads(original)
            mutate(obj)
            path.write_text(json.dumps(obj) + '\n')
            try:
                yield
            finally:
                path.write_bytes(original)

        def bad_slack(obj):
            obj['slacks'][0]['coefficient'] = str(Fraction(obj['slacks'][0]['coefficient']) + 1)
        with json_mutation(cert, bad_slack):
            reject('main host identity: altered slack (primary checker)', lambda: verify_certificate(cert, data))
            reject('main host identity: altered slack (independent checker)', lambda: independent(cert, data))
        with json_mutation(cert, lambda x: x['squares'][0].update(coefficient='0')):
            reject('retained square must be strictly positive', lambda: verify_certificate(cert, data))
        with json_mutation(cert, lambda x: x.update(schema='unrecognized-proof-schema')):
            reject('main schema: primary checker', lambda: verify_certificate(cert, data))
            reject('main schema: independent checker', lambda: independent(cert, data))
        original = cert.read_bytes()
        try:
            cert.write_bytes(b'{"schema":"duplicate-key-must-be-rejected",' + original.lstrip()[1:])
            reject('duplicate JSON key: primary checker', lambda: verify_certificate(cert, data), errors=(ValueError,))
            reject('duplicate JSON key: independent checker', lambda: independent(cert, data), errors=(ValueError,))
        finally:
            cert.write_bytes(original)
        def float_coefficient(obj):
            next(item for item in obj['positive_columns'] if item['name']=='Ji0')['coefficient'] = 0.0
        with json_mutation(cert, float_coefficient):
            reject('binary float cannot replace an exact rational field: primary checker',
                   lambda: verify_certificate(cert, data), errors=(ValueError,))
            reject('binary float cannot replace an exact rational field: independent checker',
                   lambda: independent(cert, data), errors=(ValueError,))
        with json_mutation(triangle, lambda x: x.update(certificate_sha256='0' * 64)):
            reject('span witness binds its actual main certificate',
                   lambda: verify_spans(cert, triangle, degree, data_dir=data))
        with json_mutation(triangle, lambda x: x.pop('schema')):
            reject('triangle witness requires the declared schema',
                   lambda: verify_spans(cert, triangle, degree, data_dir=data))
        with json_mutation(degree, lambda x: x.update(schema='wrong-degree-schema')):
            reject('degree/codegree witness requires the declared schema',
                   lambda: verify_spans(cert, triangle, degree, data_dir=data))
        with json_mutation(triangle, lambda x: x['combination'][0].update(coefficient=1.0)):
            reject('span coefficients must be exact rational fields',
                   lambda: verify_spans(cert, triangle, degree, data_dir=data), errors=(ValueError,))
        with json_mutation(data / 'pattern_columns.json',
                           lambda x: x['patterns'][0].update(denominator=43)):
            reject('saved metadata cannot redefine a mathematical denominator', lambda: recount(data))
        pattern_path = data / 'pattern_columns.npz'
        original = pattern_path.read_bytes()
        with np.load(pattern_path, allow_pickle=False) as archive:
            arrays = {key: archive[key].copy() for key in archive.files}
        arrays['pattern_counts'][0, 0] += 1
        try:
            np.savez_compressed(pattern_path, **arrays)
            reject('independent recount detects an altered primitive integer count', lambda: recount(data))
        finally:
            pattern_path.write_bytes(original)
        with json_mutation(data / 'profile_envelope.json',
                           lambda x: x['counts_by_mask'].__setitem__(12345, x['counts_by_mask'][12345] + 1)):
            reject('published profile table must equal freshly checked values',
                   lambda: verify_finite_views(data, finite_result, profile_result, offsets),
                   errors=(StoredArtifactMismatch,), contains='profile_envelope.json.counts_by_mask[12345]')
        def corrupt_candidate(obj):
            record = obj['offsets']['-2']['presentations'][0]
            record['polynomial_index'] = (record['polynomial_index'] + 1) % 8
        with json_mutation(data / 'eventual_polynomials_small_offsets.json', corrupt_candidate):
            reject('every published candidate-to-polynomial mapping is bound',
                   lambda: verify_finite_views(data, finite_result, profile_result, offsets),
                   errors=(StoredArtifactMismatch,), contains='eventual_polynomials_small_offsets.json.offsets.-2.presentations[0]')
        def corrupt_polynomial(obj):
            obj['offsets']['-2']['polynomials'][0]['ascending_coefficients'][0] += 1
        with json_mutation(data / 'eventual_polynomials_small_offsets.json', corrupt_polynomial):
            reject('every published polynomial coefficient is bound, including nonwinners',
                   lambda: verify_finite_views(data, finite_result, profile_result, offsets),
                   errors=(StoredArtifactMismatch,), contains='eventual_polynomials_small_offsets.json.offsets.-2.polynomials[0]')
        with json_mutation(data / 'graph_atlas_7.json', lambda x: x['hosts'][0].update(mask=1)):
            reject('published atlas is bound to the recounted host order',
                   lambda: verify_structural_views(data), errors=(StoredArtifactMismatch, AssertionError))

        # The real driver's missing-file branch, in an isolated minimal tree.
        driver_root = work / 'missing-certificate-project'
        (driver_root / 'src').mkdir(parents=True)
        (driver_root / 'certificates').mkdir()
        for name in ('verify_project.py', 'release_integrity.py', '_bootstrap.py'):
            shutil.copy2(ROOT / 'src' / name, driver_root / 'src' / name)
        missing_report = driver_root / 'results' / 'verification_manifest.json'
        result = subprocess.run([sys.executable, str(driver_root / 'src' / 'verify_project.py')],
                                capture_output=True, text=True)
        record = json.loads(missing_report.read_text())
        if result.returncode != 2 or record['status'] != 'incomplete' or len(record['missing_certificates']) != 3:
            raise RuntimeError('Missing certificates did not produce the required nonzero incomplete result')
        cases.append({'case': 'missing exact certificates cannot yield a partial PASS',
                      'status': 'rejected_as_required', 'exit_code': result.returncode})

        # Fingerprint regression: the control represents a completed check;
        # its status alone must not survive subsequent changes or additions.
        integrity_root = work / 'integrity-fixture'
        (integrity_root / 'src').mkdir(parents=True)
        bound = integrity_root / 'src' / 'example.py'
        bound.write_text('original verified bytes\n')
        report = {'status': VERIFIED_STATUS, 'sha256': fingerprints(integrity_root)}
        verify_current(integrity_root, report)
        bound.write_text('modified after verification\n')
        reject('verified release refuses a changed bound source',
               lambda: verify_current(integrity_root, report), errors=(VerificationStateError,), contains='stale')
        bound.write_text('original verified bytes\n')
        (integrity_root / 'src' / 'new.py').write_text('unverified new source\n')
        reject('verified release refuses an unverified added source',
               lambda: verify_current(integrity_root, report), errors=(VerificationStateError,), contains='file set is stale')

        for optimization in ('-O', '-OO'):
            result = subprocess.run([sys.executable, optimization, str(ROOT / 'src' / 'verify_project.py')],
                                    capture_output=True, text=True)
            if result.returncode == 0 or 'requires assertions' not in result.stderr:
                raise RuntimeError(f'{optimization}: project verifier failed to reject disabled assertions')
            cases.append({'case': f'project verification refuses Python {optimization}',
                          'status': 'rejected_as_required', 'exit_code': result.returncode})
    return {'schema': 'induced-pentagons.rejection-regression.v1', 'status': 'PASS',
            'scope': 'Concrete corruption and stale-verdict rejection checks, with valid positive controls; no claim of exhaustive software verification.',
            'original_project_files_modified': False, 'positive_controls': 'all required valid-input checkers passed',
            'rejection_cases': len(cases), 'cases': cases,
            'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'audit' / 'rejection_cases.json')
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix('.pending.json')
    temporary.write_text(json.dumps(result, indent=2) + '\n')
    os.replace(temporary, args.output)
    print(json.dumps({k: result[k] for k in ('status', 'rejection_cases', 'original_project_files_modified')}, indent=2))


if __name__ == '__main__':
    main()
