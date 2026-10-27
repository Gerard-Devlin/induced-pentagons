#!/usr/bin/env python3
"""Generate and independently check the fixed-offset data.

The default run exhausts all 6,496 small-offset presentations with labeled
Clebsch types (j=-2,-1,0,1,2). The elementary branch census in Section 14.1
proves the totals 5,460 and 882 for j=-2 and j=2, independently of the
polynomial computations.
Only automorphisms of the wrong-pair graph are quotiented out: the endpoints
of K2, the two leaf vertices of P3, and the endpoints/components of 2K2.
No Clebsch automorphism reduction is used. Every distinct polynomial is checked by an independent
implementation of (75), and, by default, by actual graphs at k=3,4.

For any other fixed integer, --j J implements the finite labeled enumeration
in Theorem 14.1 with no truncation. Its cost grows very rapidly with |J|.
This verifies finite candidate computations only. The supplied global
sharp-bound certificate and equality-span witnesses are checked separately
by verify_project.py. Eventual global optimality also uses the structural
proofs in the manuscript. No global extremality threshold k_0(J) is computed.

All arithmetic and all output coefficients are exact integers. No external
packages are required. Active types are 0..15; isolated type is -1.
"""
from __future__ import annotations

import _bootstrap  # local CLI module paths only

import argparse
import json
from collections import Counter
from itertools import combinations, combinations_with_replacement, product
from math import isqrt
from pathlib import Path
from typing import Iterator, Sequence

from clebsch_core import (
    ADJ, EDGES, construct_graph, construction_polynomial,
    count_c5_by_paths, edge, edge_quadratic, evaluate,
)

ZERO = (0,) * 16
TYPES = tuple(range(-1, 16))
Datum = tuple[tuple[int, ...], tuple[int, ...], tuple[tuple[int, int], ...]]
EXPECTED_COUNTS = {-2: 5460, -1: 120, 0: 1, 1: 33, 2: 882}
FINITE_SCOPE = (
    'Exact finite candidate enumeration and construction counts. '
    'The supplied global sharp-bound certificate and equality-span '
    'witnesses are checked separately by verify_project.py; this enumeration '
    'does not itself check them. Eventual global extremality also uses the '
    'structural proofs in the manuscript.'
)


def certificate_context() -> dict:
    """Record availability and separate checking commands, not a proof verdict."""
    data_dir = Path(__file__).resolve().parents[1] / 'certificates'
    return {
        'global_certificate_available': (data_dir / 'all_graph_exact_certificate.json').is_file(),
        'global_certificate_checked_in_this_run': False,
        'global_certificate_verification_command': 'python3 src/rationalize_certificate.py --verify-only',
        'equality_span_verification_command': 'python3 src/generate_equality_spans.py --verify-only',
        'complete_verification_command': 'python3 src/verify_project.py',
    }


EXPECTED_POLYNOMIALS = {
    -2: {
        (0, 0, 0, -48, 0, 192), (0, 2, 0, -48, 0, 192),
        (0, 0, 6, -48, 0, 192), (0, 0, -6, -48, 0, 192),
        (0, 2, -2, -48, 0, 192), (0, 2, 2, -48, 0, 192),
        (0, 0, -2, -48, 0, 192), (0, 0, 2, -48, 0, 192),
    },
    -1: {(0, 0, 0, -24, 0, 192)},
    0: {(0, 0, 0, 0, 0, 192)},
    1: {(0, 0, 0, 0, 0, 192)},
    2: {(0, 0, 0, 0, 0, 192), (0, 0, 6, 0, 0, 192)},
}


def toggle_statistics(types: Sequence[int], flips: Sequence[tuple[int, int]]) -> tuple[int, int, int]:
    """Return numbers of additions, deletions, and nonneighbor additions."""
    plus = minus = tn = 0
    for u, v in flips:
        a, b = types[u], types[v]
        if a >= 0 and b >= 0 and edge(a, b):
            minus += 1
        else:
            plus += 1
            if a >= 0 and b >= 0 and a != b:
                tn += 1
    return plus, minus, tn


def valid_datum(j: int, h: tuple[int, ...], types: tuple[int, ...],
                flips: tuple[tuple[int, int], ...], lam: int | None = None) -> bool:
    """The two exact admissibility equations (74)."""
    if lam is None:
        if abs(j) > 2:
            raise ValueError('Lambda must be specified outside the small-offset family')
        lam = 12 * abs(j)
    plus, minus, tn = toggle_statistics(types, flips)
    return (sum(h) == 0 and edge_quadratic(h) + plus - minus == j
            and 6 * sum(a * a for a in h) + 12 * len(flips) + 6 * tn == lam)


def small_candidates(j: int) -> Iterator[Datum]:
    """Complete small-offset family, using the stated presentation convention."""
    if j not in (-2, -1, 0, 1, 2):
        raise ValueError('Small-offset enumeration requires -2 <= j <= 2')
    if j == 0:
        yield ZERO, (), ()
        return

    # V=0, T=|j|. For T=2 the wrong-pair graph is P3 or 2K2.
    if abs(j) == 1:
        for a, b in combinations_with_replacement(TYPES, 2):
            types, flips = (a, b), ((0, 1),)
            if valid_datum(j, ZERO, types, flips):
                yield ZERO, types, flips
    else:
        for a in TYPES:
            for b, c in combinations_with_replacement(TYPES, 2):
                types, flips = (a, b, c), ((0, 1), (0, 2))
                if valid_datum(j, ZERO, types, flips):
                    yield ZERO, types, flips
        pairs = list(combinations_with_replacement(TYPES, 2))
        for e1, e2 in combinations_with_replacement(pairs, 2):
            types, flips = (*e1, *e2), ((0, 1), (2, 3))
            if valid_datum(j, ZERO, types, flips):
                yield ZERO, types, flips

    # V=2: all 240 ordered e_u-e_v vectors; do not quotient Clebsch types.
    for u in range(16):
        for v in range(16):
            if u == v:
                continue
            h_list = [0] * 16
            h_list[u], h_list[v] = 1, -1
            h = tuple(h_list)
            if abs(j) == 1:
                if valid_datum(j, h, (), ()):
                    yield h, (), ()
            else:
                for a, b in combinations_with_replacement(TYPES, 2):
                    types, flips = (a, b), ((0, 1),)
                    if valid_datum(j, h, types, flips):
                        yield h, types, flips

    # V=4: two +1 entries and two -1 entries; T=0.
    if abs(j) == 2:
        for pos in combinations(range(16), 2):
            for neg in combinations((v for v in range(16) if v not in pos), 2):
                h_list = [0] * 16
                for v in pos:
                    h_list[v] = 1
                for v in neg:
                    h_list[v] = -1
                h = tuple(h_list)
                if valid_datum(j, h, (), ()):
                    yield h, (), ()


def lattice_vectors(bound: int, n: int = 16) -> Iterator[tuple[int, ...]]:
    """Exhaust every zero-sum integer vector of squared norm <= bound.

    The Cauchy--Schwarz pruning test is necessary, not heuristic. The final
    coordinate is forced by the sum, so no feasible vector is discarded.
    """
    if bound < 0 or n < 1:
        return
    h = [0] * n

    def rec(i: int, remain: int, total: int) -> Iterator[tuple[int, ...]]:
        if total * total > (n - i) * remain:
            return
        if i == n - 1:
            h[i] = -total
            if total * total <= remain:
                yield tuple(h)
            return
        for a in range(-isqrt(remain), isqrt(remain) + 1):
            h[i] = a
            yield from rec(i + 1, remain - a * a, total + a)

    yield from rec(0, bound, 0)


def lambda_exact(j: int) -> tuple[int, list[tuple[int, ...]]]:
    """Exact finite optimization (68); no floating-point eigenvalue tests."""
    best, witnesses = 12 * abs(j), []
    for h in lattice_vectors(2 * abs(j)):
        val = 6 * sum(a * a for a in h) + 12 * abs(j - edge_quadratic(h))
        if val < best:
            best, witnesses = val, []
        if val == best:
            witnesses.append(h)
    return best, witnesses


def general_candidates(j: int, lam: int) -> Iterator[Datum]:
    """Literal finite labeled enumeration of Theorem 14.1, for any fixed j.

    Duplicate isomorphic presentations are intentionally allowed. All F have
    no isolated exceptional vertices. Capacity is imposed later through an
    explicit k threshold. This route is complete but exponential and is not
    used for the source's small-offset count convention.
    """
    for h in lattice_vectors(2 * abs(j)):
        vnorm = sum(a * a for a in h)
        if 6 * vnorm > lam:
            continue
        delta = j - edge_quadratic(h)
        for t in range(min(abs(j), (lam - 6 * vnorm) // 12) + 1):
            remain = lam - 6 * vnorm - 12 * t
            if remain % 6:
                continue
            tn = remain // 6
            if tn > t or abs(delta) > t or (t + delta) % 2:
                continue
            plus, minus = (t + delta) // 2, (t - delta) // 2
            if tn > plus:
                continue
            if t == 0:
                if valid_datum(j, h, (), (), lam):
                    yield h, (), ()
                continue
            for s in range(2, 2 * t + 1):
                pairs = tuple(combinations(range(s), 2))
                for flips in combinations(pairs, t):
                    touched = {x for e in flips for x in e}
                    if len(touched) != s:
                        continue
                    for types in product(TYPES, repeat=s):
                        if toggle_statistics(types, flips) == (plus, minus, tn):
                            yield h, types, flips


def direct_formula75_polynomial(h: Sequence[int], types: Sequence[int],
                                flips: Sequence[tuple[int, int]]) -> tuple[int, ...]:
    """Independent literal implementation of (75), not the delta routine.

    It sums each induced five-set of exceptional representatives and distinct
    ordinary types once. Polynomial multiplication is implemented here anew.
    """
    s = len(types)
    all_types = tuple(types) + tuple(range(16))
    flip_set = {frozenset(e) for e in flips}
    adj = [0] * (s + 16)
    for u, v in combinations(range(s + 16), 2):
        a, b = all_types[u], all_types[v]
        present = a >= 0 and b >= 0 and ((a ^ b) in (1, 2, 4, 8, 15))
        if frozenset((u, v)) in flip_set:
            present = not present
        if present:
            adj[u] |= 1 << v
            adj[v] |= 1 << u
    exceptional_counts = Counter(types)
    total = [0] * 6
    for chosen in combinations(range(s + 16), 5):
        mask = sum(1 << u for u in chosen)
        if any((adj[u] & mask).bit_count() != 2 for u in chosen):
            continue
        term = [1]
        for u in chosen:
            if u < s:
                continue
            i = u - s
            constant = h[i] - exceptional_counts[i]
            nxt = [0] * (len(term) + 1)
            for d, coefficient in enumerate(term):
                nxt[d] += coefficient * constant
                nxt[d + 1] += coefficient
            term = nxt
        for d, coefficient in enumerate(term):
            total[d] += coefficient
    return tuple(total)


def feasibility_k(h: Sequence[int], types: Sequence[int]) -> int:
    """Only the explicit class-capacity threshold, NOT global extremality."""
    counts = Counter(types)
    return max(1, max(counts[i] - h[i] for i in range(16)))


def datum_dict(h: Sequence[int], types: Sequence[int], flips: Sequence[tuple[int, int]]) -> dict:
    plus, minus, tn = toggle_statistics(types, flips)
    return {
        'h': list(h), 'types': list(types), 'toggles': [list(e) for e in flips],
        'class_variance': sum(a * a for a in h),
        'edge_quadratic': edge_quadratic(h),
        'additions': plus, 'deletions': minus, 'nonneighbor_additions': tn,
        'capacity_threshold_k': feasibility_k(h, types),
    }


def run(out: Path, brute: bool = True, offsets: Sequence[int] = (-2, -1, 0, 1, 2),
        force_general: bool = False, include_presentations: bool = True) -> dict:
    if not __debug__:
        raise RuntimeError('Exact offset verification refuses Python -O, -OO, or PYTHONOPTIMIZE.')
    records, actual_records = {}, []
    total_candidates = 0
    for j in offsets:
        lam, lattice_witnesses = lambda_exact(j)
        small = abs(j) <= 2 and not force_general
        if abs(j) <= 2:
            assert lam == 12 * abs(j), (j, lam)
        candidates = small_candidates(j) if small else general_candidates(j, lam)
        bypoly: dict[tuple[int, ...], dict] = {}
        multiplicities: Counter[tuple[int, ...]] = Counter()
        branch_counts: Counter[str] = Counter()
        all_presentations = []
        n = 0
        for h, types, flips in candidates:
            n += 1
            assert valid_datum(j, h, types, flips, lam)
            p = construction_polynomial(h, types, flips)
            assert len(p) == 6 and p[5] == 192 and p[4] == 0
            assert p[3] == 12 * j - lam, (j, h, types, flips, p)
            multiplicities[p] += 1
            key = 'V=%d,T=%d' % (sum(a * a for a in h), len(flips))
            branch_counts[key] += 1
            d = datum_dict(h, types, flips)
            if p not in bypoly:
                bypoly[p] = d
            if include_presentations:
                all_presentations.append({'datum': d, 'polynomial': p})
        assert n and bypoly, (j, 'Empty candidate family')
        total_candidates += n
        if small:
            assert n == EXPECTED_COUNTS[j], (j, n)
            assert set(bypoly) == EXPECTED_POLYNOMIALS[j], (j, set(bypoly))
        sorted_polys = sorted(bypoly, key=lambda p: tuple(reversed(p)))
        best = sorted_polys[-1]
        pindex = {p: i for i, p in enumerate(sorted_polys)}
        for rec in all_presentations:
            rec['polynomial_index'] = pindex[rec.pop('polynomial')]
        polynomial_records = []
        for p in sorted_polys:
            d = bypoly[p]
            literal = direct_formula75_polynomial(d['h'], d['types'], d['toggles'])
            assert literal == p, (j, p, literal)
            polynomial_records.append({
                'ascending_coefficients': list(p),
                'presentation_count': multiplicities[p],
                'eventual_maximum_within_candidate_family': p == best,
                'witness': d, 'independent_formula75_check': 'PASS',
            })
            if brute:
                # The source small-offset witnesses have capacity <=3. For
                # arbitrary j, use two feasible k values and record them.
                base = max(3, d['capacity_threshold_k'])
                for k in (base, base + 1):
                    graph = construct_graph(k, d['h'], d['types'], d['toggles'])
                    edges = sum(row.bit_count() for row in graph) // 2
                    actual = count_c5_by_paths(graph)
                    predicted = evaluate(p, k)
                    assert edges == 40 * k * k + j, (j, k, edges)
                    assert actual == predicted, (j, p, k, actual, predicted)
                    actual_records.append({
                        'offset': j, 'polynomial_index': pindex[p], 'k': k,
                        'vertices': len(graph), 'edges': edges,
                        'induced_pentagons': actual, 'polynomial_value': predicted,
                        'status': 'PASS',
                    })
        records[str(j)] = {
            'lambda': lam,
            'lattice_minimizers': [list(h) for h in lattice_witnesses],
            'candidate_presentations_checked': n,
            'branch_counts': dict(sorted(branch_counts.items())),
            'distinct_polynomials': len(bypoly),
            'best_ascending_coefficients': list(best),
            'eventual_maximum_presentation_count': multiplicities[best],
            'polynomials': polynomial_records,
            'presentation_convention': (
                'Clebsch types labeled; quotient only K2 endpoint swap, P3 leaf swap, '
                'and 2K2 endpoint/component swaps' if small else
                'All exceptional vertices labeled; duplicate isomorphic presentations retained'
            ),
        }
        if include_presentations:
            records[str(j)]['presentations'] = all_presentations
        print('offset', j, 'candidates', n, 'distinct', len(bypoly),
              'lambda', lam, 'best', best, flush=True)
    offset_polynomial_records = sum(len(record['polynomials']) for record in records.values())
    globally_distinct_polynomials = len({
        tuple(polynomial['ascending_coefficients'])
        for record in records.values()
        for polynomial in record['polynomials']
    })
    result = {
        'schema': 'pentagon-fixed-offset-enumeration-v2',
        'status': 'PASS',
        'scope': FINITE_SCOPE,
        **certificate_context(),
        'global_extremality_threshold_computed': False,
        'coefficient_order': 'ascending: constant,k,k^2,k^3,k^4,k^5',
        'active_type_labels': '0..15 (F_2^4 bit masks)',
        'isolated_type_label': -1,
        'total_candidate_presentations_checked': total_candidates,
        'offset_polynomial_records': offset_polynomial_records,
        'globally_distinct_polynomials': globally_distinct_polynomials,
        'independent_methods': [
            'Exact delta-of-five-set polynomial over the original template',
            'Literal equation (75), independently coded, for each distinct polynomial',
            'Actual-graph induced-cycle traversal at two feasible k values for each distinct polynomial'
            if brute else 'Actual-graph checks skipped by explicit command-line option',
        ],
        'actual_graph_checks': len(actual_records),
        'actual_graph_k_values': sorted({r['k'] for r in actual_records}),
        'actual_graph_results': actual_records,
        'offsets': records,
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path,
                        default=Path('certificates/eventual_polynomials_small_offsets.json'))
    parser.add_argument('--j', type=int, nargs='+', help='Fixed integer offset(s); default -2 -1 0 1 2')
    parser.add_argument('--general', action='store_true',
                        help='Use the expensive fully labeled enumeration even for small offsets')
    parser.add_argument('--skip-actual-graphs', action='store_true')
    parser.add_argument('--summary-only', action='store_true',
                        help='Check every presentation, but omit the complete presentation list from JSON')
    args = parser.parse_args()
    result = run(args.out, not args.skip_actual_graphs,
                 tuple(dict.fromkeys(args.j)) if args.j is not None else (-2, -1, 0, 1, 2),
                 args.general, not args.summary_only)
    print('Total presentations:', result['total_candidate_presentations_checked'])
    print('Actual graph checks:', result['actual_graph_checks'])
