#!/usr/bin/env python3
"""Independent exact-rational checks of the analytic/certificate interface.

This imports no production counting or verification code.  It compares direct
finite-measure integral formulas and their derivatives with the declared pattern
specifications on two explicitly fractional step graphons.  The general analytic
proof is not formalized by these finite checks, nor are the 1044 certificate rows
reverified here.  Run from any directory with Python 3 (standard library only).
"""

import _bootstrap  # local CLI module paths only

from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CYCLE = ((0, 1), (1, 2), (2, 3), (3, 4), (0, 4))
CHORDS = tuple(p for p in combinations(range(5), 2) if p not in CYCLE)


def mul(values):
    result = F(1)
    for value in values:
        result *= value
    return result


def require(condition, label):
    if not condition:
        raise AssertionError(label)


def pattern_density(w, masses, order, edges, nonedges=()):
    result = F(0)
    for a in product(range(len(masses)), repeat=order):
        result += (
            mul(masses[i] for i in a)
            * mul(w[a[i]][a[j]] for i, j in edges)
            * mul(1 - w[a[i]][a[j]] for i, j in nonedges)
        )
    return result


def profile_link(w, masses, f):
    result = F(0)
    for a, b, c, d in product(range(len(masses)), repeat=4):
        result += (
            masses[a] * masses[b] * masses[c] * masses[d]
            * w[a][b] * w[b][c] * w[c][d]
            * (1 - w[a][c]) * (1 - w[a][d]) * (1 - w[b][d])
            * f[a] * f[d] * (1 - f[b]) * (1 - f[c])
        )
    return result / 2


def completion_kernels(w, masses):
    n = len(masses)
    aa = [[F(0) for _ in range(n)] for _ in range(n)]
    bb = [[F(0) for _ in range(n)] for _ in range(n)]
    for x, y, a, b, c in product(range(n), repeat=5):
        wt = masses[a] * masses[b] * masses[c]
        aa[x][y] += (
            wt * w[x][a] * w[a][b] * w[b][c] * w[c][y]
            * (1 - w[x][b]) * (1 - w[x][c])
            * (1 - w[y][a]) * (1 - w[y][b]) * (1 - w[a][c])
        )
        bb[x][y] += (
            wt * w[x][a] * w[a][y] * w[y][b] * w[b][c] * w[c][x]
            * (1 - w[x][b]) * (1 - w[a][b])
            * (1 - w[a][c]) * (1 - w[y][c])
        )
    return aa, bb


def check_case(w, masses, specs, columns):
    n = len(masses)
    counts = Counter()

    def same(left, right, label):
        require(left == right, label)
        counts[label.split(':')[0]] += 1

    require(sum(masses) == 1, 'probability masses')
    require(all(0 < w[i][j] < 1 and w[i][j] == w[j][i]
                for i, j in product(range(n), repeat=2)), 'fractional symmetric kernel')
    d = [sum(masses[j] * w[i][j] for j in range(n)) for i in range(n)]
    b = [sum(masses[j] * w[i][j] * d[j] for j in range(n)) for i in range(n)]
    codeg = [[sum(masses[k] * w[i][k] * w[j][k] for k in range(n))
              for j in range(n)] for i in range(n)]
    triangle = [sum(masses[j] * masses[k] * w[i][j] * w[i][k] * w[j][k]
                    for j, k in product(range(n), repeat=2)) for i in range(n)]
    links = [profile_link(w, masses, w[i]) for i in range(n)]
    aa, bb = completion_kernels(w, masses)
    edge = sum(masses[i] * d[i] for i in range(n)) / 2
    gradient = [F(0) for _ in range(n)]
    hessian = [[F(0) for _ in range(n)] for _ in range(n)]
    direction = [[F(i + j + 1, 13) * (-1 if (i + j) % 2 else 1)
                  for j in range(n)] for i in range(n)]
    pentagons = F(0)
    edge_derivative = F(0)
    for a in product(range(n), repeat=5):
        weights = mul(masses[i] for i in a)
        factors = ([w[a[i]][a[j]] for i, j in CYCLE]
                   + [1 - w[a[i]][a[j]] for i, j in CHORDS])
        changes = ([direction[a[i]][a[j]] for i, j in CYCLE]
                   + [-direction[a[i]][a[j]] for i, j in CHORDS])
        term = weights * mul(factors) / 10
        pentagons += term
        edge_derivative += term * sum(t / s for t, s in zip(changes, factors))
        multiplicity = Counter(a)
        for i in range(n):
            gradient[i] += term * multiplicity[i] / masses[i]
            for j in range(n):
                hessian[i][j] += (
                    term * multiplicity[i] * (multiplicity[j] - (i == j))
                    / (masses[i] * masses[j])
                )
    for i in range(n):
        same(gradient[i], links[i], 'vertex derivative: L')
        same(sum(masses[j] * w[i][j] * aa[i][j] for j in range(n)),
             2 * links[i], 'completion identity: integral WA')
        for j in range(n):
            same(hessian[i][j], w[i][j] * aa[i][j] + (1 - w[i][j]) * bb[i][j],
                 'vertex Hessian: WA+(1-W)B')
    same(edge_derivative,
         sum(masses[i] * masses[j] * (aa[i][j] - bb[i][j]) * direction[i][j]
             for i, j in product(range(n), repeat=2)) / 2,
         'edge derivative: half integral qH')

    # Independently select the terms containing exactly one new latent class.
    f = [F(i + 1, n + 5) for i in range(n)]
    enlarged = [row + [f[i]] for i, row in enumerate(w)] + [f + [F(0)]]
    insertion = F(0)
    for a in product(range(n + 1), repeat=5):
        if a.count(n) == 1:
            insertion += (
                mul(masses[i] for i in a if i != n)
                * mul(enlarged[a[i]][a[j]] for i, j in CYCLE)
                * mul(1 - enlarged[a[i]][a[j]] for i, j in CHORDS) / 10
            )
    same(insertion, profile_link(w, masses, f), 'profile insertion: first coefficient')

    raw = {s['name']: pattern_density(w, masses, s['vertices'], s['edges'], s['nonedges'])
           for s in specs}
    same(raw['p'], 2 * edge, 'pattern semantics: p')
    same(raw['theta'], 10 * pentagons, 'pattern semantics: theta')
    for j, multiplier in enumerate((d, [x * x for x in d], b), start=1):
        same(raw[f'L{j}'], 2 * sum(masses[i] * links[i] * multiplier[i] for i in range(n)),
             f'pattern semantics: L{j}')
        same(raw[f'B{j}'], sum(masses[i] * d[i] * multiplier[i] for i in range(n)),
             f'pattern semantics: B{j}')
    same(raw['L_triangle'], 2 * sum(masses[i] * links[i] * triangle[i] for i in range(n)),
         'pattern semantics: triangle link')
    same(raw['B_triangle'], sum(masses[i] * d[i] * triangle[i] for i in range(n)),
         'pattern semantics: triangle degree')
    removed = F(0)
    original_link = F(0)
    deleted_link = F(0)
    for u, v in product(range(n), repeat=2):
        root_weight = masses[u] * masses[v] * w[u][v]
        removed += root_weight * codeg[u][v] ** 2
        original_link += root_weight * codeg[u][v] * links[u]
        profile = [w[u][x] * (1 - w[v][x]) for x in range(n)]
        deleted_link += root_weight * codeg[u][v] * profile_link(w, masses, profile)
    same(raw['Ddel'], removed, 'pattern semantics: removed degree')
    same(raw['Jdel_Lg'] / 2, original_link, 'pattern semantics: profile Lg')
    same(sum(raw[f'Jdel_Lf{i}{j}'] for i, j in product((0, 1), repeat=2)) / 2,
         deleted_link, 'pattern semantics: fractional profile Lf expansion')
    same(raw['R0'] + raw['R1'], removed, 'pattern semantics: R0+R1')
    pstar, tau = F(5, 144), F(5, 663552)
    declared = {c['name']: sum(F(coefficient) * raw[name] for name, coefficient in c['terms'].items())
                for c in columns}
    same(declared['Jdel'], original_link - deleted_link - tau / (2 * pstar) * removed,
         'column semantics: Jdel')
    for variant in (0, 1):
        rr = F(0)
        ja = F(0)
        jb = F(0)
        for u, v in product(range(n), repeat=2):
            psi = sum(
                masses[x] * masses[y] * w[u][x] * w[v][x] * w[u][y] * w[v][y]
                * (w[x][y] if variant else 1 - w[x][y])
                for x, y in product(range(n), repeat=2)
            )
            weighted_psi = masses[u] * masses[v] * w[u][v] * psi
            rr += weighted_psi
            ja += weighted_psi * aa[u][v]
            jb += weighted_psi * bb[u][v]
        same(raw[f'R{variant}'], rr, 'pattern semantics: edge multiplier R')
        same(raw[f'J{variant}_A'], ja, 'pattern semantics: edge completion A')
        same(raw[f'J{variant}_B'], jb, 'pattern semantics: chord completion B')
        same(declared[f'Ji{variant}'], ja - jb - tau / (2 * pstar) * rr,
             'column semantics: Ji')

    # These illustrative inequality checks do not assert that the fixtures are maxima.
    for x in range(n):
        sx = sum(masses[u] * masses[v] * w[x][u] * (1 - w[x][v]) * w[u][v]
                 for u, v in product(range(n), repeat=2))
        eout = sum(masses[u] * masses[v] * (1 - w[x][u]) * (1 - w[x][v]) * w[u][v]
                   for u, v in product(range(n), repeat=2)) / 2
        same(eout, edge - (b[x] + sx) / 2, 'link identity: Eout')
        require(links[x] <= d[x] ** 2 * eout / 4 <= edge * d[x] ** 2 / 4,
                'universal link bound')
        require(links[x] <= sx ** 2 / 2, 'second universal link bound')
        counts['illustrative link inequalities'] += 2
    path = pattern_density(w, masses, 4, ((0, 1), (1, 2), (2, 3)),
                           ((0, 2), (0, 3), (1, 3)))
    require(path <= edge ** 2, 'induced P4 <= E squared')
    counts['illustrative path inequality'] += 1
    return {'types': n, 'masses': list(map(str, masses)),
            'kernel': [[str(t) for t in row] for row in w],
            'checks': dict(counts), 'checks_total': sum(counts.values())}


def main():
    if not __debug__:
        raise RuntimeError('Foundation checks refuse Python -O, -OO, or PYTHONOPTIMIZE.')
    pattern_path = ROOT / 'certificates/pattern_columns.json'
    certificate_path = ROOT / 'certificates/all_graph_exact_certificate.json'
    metadata = json.loads(pattern_path.read_text())
    for s in metadata['patterns']:
        edges, nonedges = list(map(tuple, s['edges'])), list(map(tuple, s['nonedges']))
        require(len(set(edges)) == len(edges) and len(set(nonedges)) == len(nonedges),
                'no repeated formal edge variable')
        require(not set(edges).intersection(nonedges), 'no conflicting edge requirements')
    fixtures = [
        ([[F(1, 5), F(2, 3)], [F(2, 3), F(3, 7)]], [F(2, 5), F(3, 5)]),
        ([[F(1, 4), F(2, 5), F(5, 7)],
          [F(2, 5), F(3, 8), F(1, 6)],
          [F(5, 7), F(1, 6), F(4, 9)]], [F(1, 6), F(1, 3), F(1, 2)]),
    ]
    cases = [check_case(w, masses, metadata['patterns'], metadata['columns'])
             for w, masses in fixtures]
    certificate = json.loads(certificate_path.read_text())
    lambdas = [F(row['coefficient']) for row in certificate['free_columns'][:3]]
    require(-F(1157, 10) < lambdas[0] < 0, 'lambda1 bound')
    require(lambdas[2] < 0 and lambdas[1] + lambdas[2] > 310, 'lambda2+lambda3 bounds')
    conservative_slope = 1 - F(5, 144) * F(1157, 10) ** 2 / (4 * 310)
    require(conservative_slope == F(2232551, 3571200) > F(5, 8), 'uniform slope')
    require(F(192) ** 2 / F(40) ** 5 == F(9, 25000), 'Clebsch sharp constant squared')
    require(F(5) ** 5 * F(9, 25000) == F(9, 8), 'R constant squared')
    require(F(16, 1000) * F(9, 8) == F(9, 500) > F(1, 80), 'initial density padding')
    require(F(80, 16 ** 2) / 9 == F(5, 144), 'reference edge density')
    require(F(1920, 16 ** 5) / 243 == F(5, 663552), 'reference pentagon density')
    require(F(5, 663552) / (2 * F(5, 144)) == F(1, 9216), 'reference kappa')
    p0, codegree = F(5, 16), F(1, 8)
    require((p0 ** 2 - (1 - p0) * codegree) / (p0 - codegree) == F(1, 16),
            'twin class mass')
    require(F(5, 144) / F(5, 48) == F(1, 3), 'active mass at reference density')
    require(11 ** 2 * 10 < 75 ** 2 * 2, 'strict active-density comparison')
    output = {
        'schema': 'referee-foundations-exact-interface-checks-v1',
        'status': 'verified_exact_finite_checks',
        'created_utc': datetime.now(timezone.utc).isoformat(),
        'scope': 'Derivative normalizations, fractional pattern semantics, and scalar constants',
        'limitations': [
            'Finite fixtures do not replace the general analytic proofs.',
            'This script does not reverify the full certificate rows or formalize measure theory.',
            'No maximality or variational sign assertion is made about the fractional fixtures.',
        ],
        'production_modules_imported': [],
        'cases': cases,
        'cases_checks_total': sum(case['checks_total'] for case in cases),
        'multilinear_pattern_specifications': len(metadata['patterns']),
        'conservative_slope': str(conservative_slope),
        'constant_checks': 12,
        'input_sha256': {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest()
                         for p in (pattern_path, certificate_path)},
    }
    destination = ROOT / 'audit/foundation_identities.json'
    destination.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps({'status': output['status'], 'fixture_checks': output['cases_checks_total'],
                      'constant_checks': output['constant_checks'],
                      'output': str(destination)}))


if __name__ == '__main__':
    main()
