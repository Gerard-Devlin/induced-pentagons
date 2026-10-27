#!/usr/bin/env python3
"""Independent arithmetic checks; no external dependencies.

This is an audit companion, not part of the production verification pipeline.
It independently enumerates all labeled exceptional graphs for |j| <= 2,
then compares their canonical images with the optimized production generator.
Its literal polynomial implementation checks EVERY production presentation.
"""
from __future__ import annotations

import _bootstrap  # local CLI module paths only

import json
import sys
from collections import Counter
from itertools import combinations, permutations, product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import verify_offsets as production
from clebsch_core import construction_polynomial

GENERATORS = {1, 2, 4, 8, 15}
TYPES = tuple(range(-1, 16))
ZERO = (0,) * 16


def adjacent(a, b):
    return a >= 0 and b >= 0 and (a ^ b) in GENERATORS


def qform(h):
    return sum(h[a] * h[b] for a, b in combinations(range(16), 2)
               if (a ^ b) in GENERATORS)


def deviations(v):
    if v == 0:
        yield ZERO
    elif v == 2:
        for a, b in permutations(range(16), 2):
            h = [0] * 16
            h[a], h[b] = 1, -1
            yield tuple(h)
    elif v == 4:
        for support in combinations(range(16), 4):
            for positive in combinations(support, 2):
                h = [0] * 16
                for a in support:
                    h[a] = 1 if a in positive else -1
                yield tuple(h)
    else:
        raise ValueError(v)


def statistics(types, flips):
    additions = deletions = nonneighbor_additions = 0
    for a, b in flips:
        ta, tb = types[a], types[b]
        if adjacent(ta, tb):
            deletions += 1
        else:
            additions += 1
            if ta >= 0 and tb >= 0 and ta != tb:
                nonneighbor_additions += 1
    return additions, deletions, nonneighbor_additions


def canonical(h, types, flips):
    images = []
    for order in permutations(range(len(types))):
        inverse = {old: new for new, old in enumerate(order)}
        new_pairs = tuple(sorted(tuple(sorted((inverse[a], inverse[b])))
                                 for a, b in flips))
        images.append((tuple(types[old] for old in order), new_pairs))
    return (h, *min(images))


def labeled_modifications(t):
    if t == 0:
        yield (), (), (0, 0, 0)
        return
    for s in range(2, 2 * t + 1):
        for flips in combinations(tuple(combinations(range(s), 2)), t):
            if set(x for pair in flips for x in pair) != set(range(s)):
                continue
            for types in product(TYPES, repeat=s):
                yield types, flips, statistics(types, flips)


def literal_polynomial(h, types, flips):
    """All five-subsets of X plus one formal representative per old type.

    This implementation neither calls the production delta routine nor its
    separately implemented equation-(75) routine.
    """
    labels = types + tuple(range(16))
    s = len(types)
    rows = [0] * len(labels)
    flips = set(flips)
    for a, b in combinations(range(len(labels)), 2):
        if adjacent(labels[a], labels[b]) != ((a, b) in flips):
            rows[a] |= 1 << b
            rows[b] |= 1 << a
    exceptional = Counter(types)
    constants = [h[a] - exceptional[a] for a in range(16)]
    result = [0] * 6
    for chosen in combinations(range(len(labels)), 5):
        mask = sum(1 << a for a in chosen)
        if not all((rows[a] & mask).bit_count() == 2 for a in chosen):
            continue
        coeffs = [1]
        for a in chosen:
            if a < s:
                continue
            c = constants[a - s]
            coeffs = [c * coeffs[0]] + [c * coeffs[i] + coeffs[i - 1]
                                      for i in range(1, len(coeffs))] + [coeffs[-1]]
        for i, coefficient in enumerate(coeffs):
            result[i] += coefficient
    return tuple(result)


def profile_checks():
    rows = [sum(1 << b for b in range(16) if (a ^ b) in GENERATORS)
            for a in range(16)]
    paths = []
    endpoint_pairs = Counter()
    for chosen in combinations(range(16), 4):
        mask = sum(1 << a for a in chosen)
        degrees = [(rows[a] & mask).bit_count() for a in chosen]
        if sorted(degrees) != [1, 1, 2, 2]:
            continue
        endpoints = tuple(a for a, d in zip(chosen, degrees) if d == 1)
        internal = tuple(a for a, d in zip(chosen, degrees) if d == 2)
        endpoint_pairs[endpoints] += 1
        paths.append((sum(1 << a for a in endpoints),
                      sum(1 << a for a in internal)))
    maxima = [-1] * 17
    equality = []
    for mask in range(1 << 16):
        count = sum(mask & ends == ends and mask & mids == 0 for ends, mids in paths)
        maxima[mask.bit_count()] = max(maxima[mask.bit_count()], count)
        if count == 60:
            equality.append(mask)
    expected_equality = {rows[a] for a in range(16)} | {
        rows[a] | (1 << a) for a in range(16)}
    assert len(paths) == 480
    assert endpoint_pairs == Counter({(a, b): 6 for a, b in combinations(range(16), 2)
                                      if (a ^ b) not in GENERATORS})
    assert maxima == [0, 0, 6, 18, 36, 60, 60, 54, 48, 44, 42, 35, 25, 18, 12, 0, 0]
    assert set(equality) == expected_equality
    c5 = []
    pair_counts = Counter()
    vertex_counts = Counter()
    for chosen in combinations(range(16), 5):
        mask = sum(1 << a for a in chosen)
        if all((rows[a] & mask).bit_count() == 2 for a in chosen):
            c5.append(chosen)
            vertex_counts.update(chosen)
            pair_counts.update(combinations(chosen, 2))
    assert len(c5) == 192
    assert set(vertex_counts.values()) == {60}
    assert all(pair_counts[a, b] == (24 if (a ^ b) in GENERATORS else 12)
               for a, b in combinations(range(16), 2))
    response_checks = 0
    for a, b, present in product(TYPES, TYPES, (False, True)):
        extended = rows[:] + [0, 0]
        for root, typ in ((16, a), (17, b)):
            for old in range(16):
                if adjacent(typ, old):
                    extended[root] |= 1 << old
                    extended[old] |= 1 << root
        if present:
            extended[16] |= 1 << 17
            extended[17] |= 1 << 16
        completions = 0
        for old_vertices in combinations(range(16), 3):
            chosen = old_vertices + (16, 17)
            mask = sum(1 << u for u in chosen)
            completions += all((extended[u] & mask).bit_count() == 2 for u in chosen)
        expected = (0 if a < 0 or b < 0 or a == b else
                    (24 if present else 0) if adjacent(a, b) else
                    (6 if present else 12))
        assert completions == expected, (a, b, present, completions, expected)
        response_checks += 1
    return {"paths": len(paths), "boolean_profiles": 65536,
            "degreewise_maxima": maxima, "maximizers": len(equality),
            "c5_templates": len(c5), "pair_counts": "24 on edges; 12 on nonedges",
            "two_vertex_response_checks_including_isolated_types": response_checks,
            "status": "PASS"}


def main():
    if not __debug__:
        raise RuntimeError("Run this exact audit without Python optimization (-O/-OO).")
    report = {"scope": "Independent exhaustive coverage and every-presentation polynomial audit for |j|<=2; independent Boolean profile and Hessian input checks",
              "profiles": profile_checks(), "offsets": {}}
    print("Independent profile and template checks PASS", flush=True)
    modifications = {t: list(labeled_modifications(t)) for t in range(3)}
    for j in (-2, -1, 0, 1, 2):
        lam = 12 * abs(j)
        canonical_set = set()
        labeled_counts = Counter()
        for v in range(0, 2 * abs(j) + 1, 2):
            for t in range(abs(j) + 1):
                tn = (lam - 6 * v - 12 * t) // 6
                if not 0 <= tn <= t:
                    continue
                for h in deviations(v):
                    q = qform(h)
                    for types, flips, (plus, minus, actual_tn) in modifications[t]:
                        if actual_tn != tn or q + plus - minus != j:
                            continue
                        canonical_set.add(canonical(h, types, flips))
                        labeled_counts[f"V={v},T={t}"] += 1
        source = list(production.small_candidates(j))
        source_canonical = {canonical(*datum) for datum in source}
        assert len(source) == len(source_canonical), (j, "Duplicate optimized presentation")
        assert canonical_set == source_canonical, (j, "Coverage mismatch")
        branch_counts = Counter(f"V={sum(x*x for x in h)},T={len(flips)}"
                               for h, types, flips in source)
        polys = Counter()
        for index, (h, types, flips) in enumerate(source):
            own = literal_polynomial(h, types, flips)
            recorded = construction_polynomial(h, types, flips)
            assert own == recorded, (j, index, h, types, flips, own, recorded)
            assert own[5] == 192 and own[4] == 0 and own[3] == 12 * j - lam
            polys[own] += 1
        report["offsets"][str(j)] = {
            "fully_labeled_presentations": sum(labeled_counts.values()),
            "fully_labeled_branch_counts": dict(sorted(labeled_counts.items())),
            "canonical_presentations": len(canonical_set),
            "canonical_branch_counts": dict(sorted(branch_counts.items())),
            "independent_formula75_checks": len(source),
            "distinct_polynomials": len(polys),
            "polynomials": [{"ascending_coefficients": list(p), "multiplicity": n}
                            for p, n in sorted(polys.items())],
            "coverage_status": "PASS", "polynomial_status": "PASS"}
        print("j=", j, "fully labeled=", sum(labeled_counts.values()),
              "canonical=", len(canonical_set), "polynomials=", len(polys), "PASS", flush=True)
    report["status"] = "PASS"
    report["total_independent_polynomial_checks"] = sum(
        item["independent_formula75_checks"] for item in report["offsets"].values())
    report["offset_polynomial_records"] = sum(
        len(item["polynomials"]) for item in report["offsets"].values())
    report["globally_distinct_polynomials"] = len({
        tuple(polynomial["ascending_coefficients"])
        for item in report["offsets"].values() for polynomial in item["polynomials"]})
    output = ROOT / "audit" / "offset_polynomial_checks.json"
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(output, flush=True)


if __name__ == "__main__":
    main()
