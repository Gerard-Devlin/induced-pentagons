#!/usr/bin/env python3
"""Audit equality-target normalization and rejection of an invalid main SOS.

No proof certificate is constructed. The deliberate invalid-certificate test
uses a temporary directory that is removed on completion. Exact conditional
flag distributions are independently enumerated on a fractional step graphon.
"""
from __future__ import annotations

import _bootstrap  # local CLI module paths only

import hashlib
import json
import tempfile
import traceback
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path

import numpy as np

import generate_equality_spans as spans


ROOT = Path(__file__).resolve().parents[1]
PAIRS = list(combinations(range(5), 2))
BIT = {p: i for i, p in enumerate(PAIRS)}


def has_edge(mask, u, v):
    return bool(mask & (1 << BIT[tuple(sorted((u, v)))]))


def has_triangle(mask):
    return any(all(has_edge(mask, u, v) for u, v in combinations(triple, 2))
               for triple in combinations(range(5), 3))


def swap_extensions(mask):
    perm = (0, 1, 2, 4, 3)
    return sum(1 << BIT[tuple(sorted((perm[u], perm[v])))]
               for u, v in PAIRS if has_edge(mask, u, v))


def degree_target(mask, root):
    return 24 * sum(has_edge(mask, root, j) for j in (3, 4)) - 5


def codegree_target(mask, root):
    return (5 * sum(has_edge(mask, root, j) and has_edge(mask, 2, j)
                    for j in (3, 4))
            - 2 * sum(has_edge(mask, 2, j) for j in (3, 4)))


def conditional_distribution(masks, root_edges, roots):
    # Three latent classes, weights (3,2,1)/6; symmetric fractional W / 60.
    weights = [3, 2, 1]
    W = [[15, 40, 30], [40, 20, 36], [30, 36, 12]]
    free = [p for p in PAIRS if p[1] >= 3]
    rootmask = sum(1 << BIT[tuple(p)] for p in root_edges)
    index = {m: i for i, m in enumerate(masks)}
    numerators = [0] * len(masks)
    denominator = 6**2 * 60**len(free)
    for a, b in product(range(3), repeat=2):
        latents = list(roots) + [a, b]
        for choices in product((0, 1), repeat=len(free)):
            probability_num = weights[a] * weights[b]
            mask = rootmask
            for (u, v), present in zip(free, choices):
                edge_num = W[latents[u]][latents[v]]
                probability_num *= edge_num if present else 60-edge_num
                if present:
                    mask |= 1 << BIT[(u, v)]
            numerators[index[min(mask, swap_extensions(mask))]] += probability_num
    assert sum(numerators) == denominator
    degrees = [Fraction(sum(weights[j]*W[r][j] for j in range(3)), 6*60)
               for r in roots]
    codegrees = [Fraction(sum(weights[j]*W[roots[r]][j]*W[roots[2]][j]
                               for j in range(3)), 6*60**2) for r in (0, 1)]
    return numerators, denominator, degrees, codegrees


def dot(left, right):
    return sum(int(a)*int(b) for a, b in zip(left, right))


def audit():
    if not __debug__:
        raise RuntimeError('Equality-span audit refuses disabled assertions.')
    flags = np.load(ROOT/'certificates/flag_basis.npz')
    patterns = np.load(ROOT/'certificates/pattern_columns.npz')
    path_masks = flags['flag_masks_path3'].tolist()
    edge_masks = flags['flag_masks_edge_isolate'].tolist()
    edge, triangle = spans.mask_functions()
    assert all(bool(triangle(m)) == has_triangle(m) for m in range(1024))
    assert all(bool(edge(m, u, v)) == has_edge(m, u, v)
               for m in range(1024) for u, v in PAIRS)
    assert sum(not has_triangle(m) for m in path_masks) == 24
    assert sum(not has_triangle(m) for m in edge_masks) == 32
    triangle_row = [int(has_triangle(m)) for m in path_masks]
    degree_row = [degree_target(m, 1) for m in path_masks]
    codegree_rows = [[codegree_target(m, r) for m in edge_masks] for r in (0, 1)]
    extra_degree_rows = [[degree_target(m, r) for m in edge_masks] for r in (0, 1)]
    for target in (triangle_row, degree_row):
        assert all(dot(q, target) == 0 for q in flags['Q_path3'])
    for target in codegree_rows + extra_degree_rows:
        assert all(dot(q, target) == 0 for q in flags['Q_edge_isolate'])
    cases = []
    for roots in ((0, 1, 2), (1, 1, 0), (2, 0, 2)):
        for name, masks, root_edges in (
                ('path3', path_masks, ((0, 1), (1, 2))),
                ('edge_isolate', edge_masks, ((0, 1),))):
            q, den, degrees, codegrees = conditional_distribution(masks, root_edges, roots)
            for r in (0, 1, 2):
                expectation = Fraction(dot(q, [degree_target(m, r) for m in masks]), den)
                assert expectation == 48*degrees[r]-5
            for r in (0, 1):
                expectation = Fraction(dot(q, [codegree_target(m, r) for m in masks]), den)
                assert expectation == 10*codegrees[r]-4*degrees[2]
            cases.append({'block': name, 'root_latent_classes': roots})
    # A fake SOS containing genuine target vectors would satisfy the old span
    # checker alone. Its host identity is deliberately false and must be rejected.
    invalid = {
        'schema': 'induced-pentagons.exact-certificate.v1',
        'constants': {'pstar': '5/144', 'tau': '5/663552'},
        'host_masks': flags['host_masks'].tolist(),
        'free_columns': [{'name': str(n), 'coefficient': str(c)}
                         for n, c in zip(patterns['free_names'], [-1, 312, -1] + [0]*34)],
        'positive_columns': [{'name': str(n), 'coefficient': '0'}
                             for n in patterns['positive_names']],
        'squares': [
            {'id': 'triangle', 'block': 'path3', 'vector': triangle_row, 'coefficient': '1'},
            {'id': 'degree', 'block': 'path3', 'vector': degree_row, 'coefficient': '1'},
            {'id': 'codegree0', 'block': 'edge_isolate', 'vector': codegree_rows[0], 'coefficient': '1'},
            {'id': 'codegree1', 'block': 'edge_isolate', 'vector': codegree_rows[1], 'coefficient': '1'}
        ],
        'slacks': [{'host_index': h, 'host_mask': int(m), 'coefficient': '0'}
                   for h, m in enumerate(flags['host_masks'])]
    }
    triangle_witness = {
        'flag_masks': path_masks,
        'combination': [{'source_id': 'triangle', 'coefficient': '1'}],
        'result_vector': [str(x) for x in triangle_row]
    }
    degree_witness = {
        'degree': {'flag_indices': [i for i, m in enumerate(path_masks) if not has_triangle(m)],
                   'combination': [{'source_id': 'degree', 'coefficient': '1'}]},
        'codegree': [{'root': r, 'flag_indices': [i for i, m in enumerate(edge_masks) if not has_triangle(m)],
                     'combination': [{'source_id': f'codegree{r}', 'coefficient': '1'}]} for r in (0, 1)]
    }
    with tempfile.TemporaryDirectory(prefix='pentagon-span-audit-') as tmp:
        tmp = Path(tmp)
        certfile = tmp/'deliberately_invalid.json'
        certfile.write_text(json.dumps(invalid))
        digest = hashlib.sha256(certfile.read_bytes()).hexdigest()
        triangle_witness['certificate_sha256'] = digest
        degree_witness['certificate_sha256'] = digest
        trfile, dgfile = tmp/'triangle.json', tmp/'degree.json'
        trfile.write_text(json.dumps(triangle_witness))
        dgfile.write_text(json.dumps(degree_witness))
        try:
            spans.verify_spans(certfile, trfile, dgfile)
        except AssertionError as exc:
            last = traceback.extract_tb(exc.__traceback__)[-1]
            assert last.name == 'verify_certificate'
            assert 'exact host identity failed' in str(exc)
            rejected_at = 'exact host coefficient identity in verify_certificate'
        else:
            raise RuntimeError('An invalid main SOS was accepted by the span checker.')
    rational_solution = spans.exact_solve([[1, 0], [0, 1], [1, 1]],
                                            [Fraction(1, 3), Fraction(2, 5)])
    assert rational_solution == [Fraction(1, 3), Fraction(2, 5), Fraction(0)]
    assert spans.exact_solve([[1, 1]], [1, 2]) is None
    assert spans.exact_solve([], [0, 0]) == []
    actual_paths = [ROOT/'certificates'/name for name in (
        'all_graph_exact_certificate.json',
        'all_graph_path3_triangle_domination_span.json',
        'all_graph_tf_degree_codegree_spans.json')]
    actual_verification = (spans.verify_spans(*actual_paths)
                           if all(path.exists() for path in actual_paths) else None)
    return {
        'schema': 'induced-pentagons.equality-spans-independent-audit.v1',
        'status': ('target_normalization_verified; main_certificate_gate_tested; actual_main_and_spans_verified_exact'
                   if actual_verification else
                   'target_normalization_verified; main_certificate_gate_tested; actual_certificate_or_span_witness_unavailable'),
        'source_sha256': hashlib.sha256((ROOT/'src/generate_equality_spans.py').read_bytes()).hexdigest(),
        'manuscript_locators': ['Lemma 4.3', 'Lemma 4.4, equation (30)', 'Lemma 4.5, equation (31)', 'Proposition 7.1'],
        'conditional_expectations': {
            'g_or_h': '24(e(r,3)+e(r,4))-5 averages to 48 d(x_r)-5',
            'k': '5 sum_j e(r,j)e(2,j)-2 sum_j e(2,j) averages to 10 c(x_r,x_2)-4 d(x_2)',
            'sampling': 'Conditional on fixed root locations and the root type; root-type factor omitted. Both extension vertices are sampled independently. Passing to unordered extension flag orbits does not insert a factorial.'
        },
        'fractional_graphon_cases_checked': cases,
        'expectation_identities_checked': 30,
        'triangle_free_path_coordinates': 24,
        'triangle_free_edge_isolate_coordinates': 32,
        'equality_kernel_targets_checked': ['triangle_indicator', 'path_degree', 'edge_codegree_0', 'edge_codegree_1', 'edge_degree_0', 'edge_degree_1'],
        'exact_linear_solver_tests': ['rational underdetermined consistent system', 'inconsistent augmented system', 'empty zero system'],
        'fix': 'verify_spans now verifies the entire main SOS before checking any spans, including standalone --verify-only calls.',
        'invalid_main_certificate_rejected_at': rejected_at,
        'actual_certificate_verification': actual_verification,
        'remaining_limitations': [
            ('The current main certificate and both span files passed the exact checker. '
             'The independent normalization audit is supplementary; it is not a formalization of the analytic proof.'
             if actual_verification else
             'No complete actual SOS/span package is available, so the required positive-square spans remain unverified.'),
            'The LP fallback for a triangle-dominating vector is a discovery method; rational reconstruction may fail even if a witness exists. It checks final signs exactly and fails closed.',
            'The verifier uses Python assertions and must be run without -O; this matches the rest of the supplied exact-verification pipeline.'
        ]
    }


if __name__ == '__main__':
    report = audit()
    outfile = ROOT/'audit/equality_spans_independent_audit.json'
    outfile.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: report[k] for k in (
        'status', 'expectation_identities_checked', 'triangle_free_path_coordinates',
        'triangle_free_edge_isolate_coordinates', 'invalid_main_certificate_rejected_at')}, indent=2))
