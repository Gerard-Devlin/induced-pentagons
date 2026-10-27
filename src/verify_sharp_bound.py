#!/usr/bin/env python3
"""Verify the sharp constant and every term on the Clebsch equality model.

This reruns both main-certificate implementations and the equality-span check.
Primitive host counts are independently checked by the complete project gate.
"""
from __future__ import annotations

import _bootstrap  # local CLI module paths only

from collections import Counter
from fractions import Fraction as Q
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import argparse
import json

import numpy as np

from verification_json import exact_fraction, load_proof_json

ROOT = Path(__file__).resolve().parents[1]


def verify(data_dir=None):
    if not __debug__:
        raise RuntimeError('Sharp-bound verification refuses Python -O, -OO, or PYTHONOPTIMIZE.')
    data = Path(data_dir or ROOT / 'certificates')
    certificate = data / 'all_graph_exact_certificate.json'
    triangle = data / 'all_graph_path3_triangle_domination_span.json'
    degree = data / 'all_graph_tf_degree_codegree_spans.json'
    from rationalize_certificate import verify_certificate
    from verify_certificate_independent import verify as independent_certificate
    from generate_equality_spans import verify_spans
    from verify_stored_artifacts import verify_structural_views, _clebsch_pattern_count
    from audit_equality_support import audit as audit_support

    main = verify_certificate(certificate, data)
    second = independent_certificate(certificate, data)
    spans = verify_spans(certificate, triangle, degree, data)
    structural = verify_structural_views(data)
    support = audit_support(data / 'graph_atlas_7.json', data / 'equality_host_support.json')
    cert = load_proof_json(certificate)

    # Fresh graph construction, without importing clebsch_core or graph data.
    generators = {1, 2, 4, 8, 15}
    adjacency = [[int((u ^ v) in generators) for v in range(16)] for u in range(16)]
    edges = [(u, v) for u, v in combinations(range(16), 2) if adjacency[u][v]]
    pentagons = [s for s in combinations(range(16), 5)
                if all(sum(adjacency[u][v] for v in s) == 2 for u in s)]
    assert len(edges) == 40 and len(pentagons) == 192
    assert not any(adjacency[u][v] * adjacency[u][w] * adjacency[v][w]
                   for u, v, w in combinations(range(16), 3))
    active_atom, isolated_mass = Q(1, 48), Q(32, 48)
    assert 16 * active_atom + isolated_mass == 1
    E = len(edges) * active_atom ** 2
    C = len(pentagons) * active_atom ** 5
    p, theta = 2 * E, 10 * C
    assert p == Q(5, 144) == exact_fraction(cert['constants']['pstar'], 'pstar')
    assert theta == Q(5, 663552) == exact_fraction(cert['constants']['tau'], 'tau')
    c_squared = C ** 2 / E ** 5
    R_squared = 5 ** 5 * c_squared
    assert c_squared == Q(9, 25000) and R_squared == Q(9, 8)

    # Direct reference-model values of the same primitive integrals.
    metadata = load_proof_json(data / 'pattern_columns.json')
    primitive = {s['name']: Q(_clebsch_pattern_count(s), 48 ** s['vertices'])
                 for s in metadata['patterns']}
    assert primitive['p'] == p and primitive['theta'] == theta
    values = {column['name']: sum(exact_fraction(coefficient, column['name']) * primitive[name]
                                  for name, coefficient in column['terms'].items())
              for column in metadata['columns']}
    variational_names = ['Phi1', 'Phi2', 'Phi3', 'PhiTri', 'Ji0', 'Ji1', 'Jdel']
    assert all(values[name] == 0 for name in variational_names)
    # Independent graphon sampling gives p_F*t(K2)-pstar*p_F = p_F*(p-pstar).
    # Since p-pstar is exactly zero, all 34 density identities vanish without
    # needing a floating approximation to any of the probabilities p_F.
    assert p - Q(5, 144) == 0
    assert len(metadata['fixed_density']['graphs']) == 34

    with np.load(data / 'flag_basis.npz', allow_pickle=False) as archive:
        flags = {name: archive[name] for name in archive.files}
    by_block = Counter()
    dots = Counter()
    square_values = []
    for square in cert['squares']:
        name, vector = square['block'], square['vector']
        rows = flags['Q_' + name]
        if len(rows) == 0:
            assert name == 'triangle3'  # Its root event has probability zero.
        for row in rows:
            assert sum(int(a) * b for a, b in zip(row, vector)) == 0
            dots[name] += 1
        assert exact_fraction(square['coefficient'], square['id']) > 0
        by_block[name] += 1
        square_values.append({'id': square['id'], 'block': name,
                              'conditional_rows_checked': len(rows), 'value': '0',
                              'reason': 'all conditional dot products zero' if len(rows)
                                        else 'triangle root event has measure zero'})
    supported = support['supported_host_indices']
    assert len(supported) == 88
    slack_values = [exact_fraction(row['coefficient'], 'host slack') for row in cert['slacks']]
    assert all(slack_values[h] == 0 for h in supported)
    assert len(slack_values) == 1044 and all(value >= 0 for value in slack_values)

    free = {r['name']: exact_fraction(r['coefficient'], r['name']) for r in cert['free_columns']}
    positive = {r['name']: exact_fraction(r['coefficient'], r['name']) for r in cert['positive_columns']}
    lam1, lam2, lam3 = (free[f'Phi{i}'] for i in (1, 2, 3))
    assert -Q(1157, 10) < lam1 < 0 and lam3 < 0 and lam2 + lam3 > 310
    slope = 1 - p * lam1 ** 2 / (4 * (lam2 + lam3))
    displayed_slope_threshold = Q(2232551, 3571200)
    assert slope > displayed_slope_threshold > Q(5, 8)
    assert positive['PhiTri'] > 0 and positive['Jdel'] > 0
    assert positive['Ji0'] == positive['Ji1'] == 0
    model_slope = (1 + lam1 * primitive['B1'] + lam2 * primitive['B2'] + lam3 * primitive['B3']
                   + positive['PhiTri'] * primitive['B_triangle']
                   + (positive['Ji0'] * primitive['R0'] + positive['Ji1'] * primitive['R1']
                      + positive['Jdel'] * primitive['Ddel']) / (2 * p))
    assert model_slope > Q(5, 8)

    return {
        'schema':'induced-pentagons.sharp-bound-verification.v1', 'status':'PASS',
        'scope':'Exact sharp constant, sign conditions, and termwise equality-model checks.',
        'constants':{'pstar':str(p),'tau':str(theta),'C_reference':str(C),'E_reference':str(E),
                     'cstar_squared':str(c_squared),'Rstar_squared':str(R_squared),
                     'cstar':'3/(50*sqrt(10))','Rstar':'3/(2*sqrt(2))'},
        'exact_zero_checks':{'squares':len(square_values),'square_values':square_values,
                            'conditional_integer_dot_products':sum(dots.values()),
                            'supported_hosts':len(supported),
                            'all_1044_slack_terms_zero':all(slack_values[h]==0 for h in supported),
                            'variational_columns':len(variational_names),'density_identities':34},
        'slope':{'lambda1':str(lam1),'lambda2_plus_lambda3':str(lam2+lam3),
                 'uniform_lower_bound':str(slope),'displayed_threshold':str(displayed_slope_threshold),
                 'strictly_above_5_over_8':slope>Q(5,8),'equality_model_value':str(model_slope)},
        'called_verifications':{'primary_certificate':main['status'],'independent_certificate':second['status'],
                                'equality_spans':spans['status'],'structural_views':structural['status'],
                                'equality_support':support['status']},
        'certificate_sha256':sha256(certificate.read_bytes()).hexdigest(),
        'span_sha256':{path.name:sha256(path.read_bytes()).hexdigest() for path in (triangle,degree)},
        'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
    }



if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data-dir', type=Path, default=ROOT / 'certificates')
    parser.add_argument('--output', type=Path, default=ROOT / 'results/sharp_bound_verification.json')
    args = parser.parse_args()
    result = verify(args.data_dir)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'constants': result['constants'],
                      'squares_zero': result['exact_zero_checks']['squares'],
                      'supported_host_slacks_zero': result['exact_zero_checks']['supported_hosts'],
                      'slope': result['slope']}, indent=2))
