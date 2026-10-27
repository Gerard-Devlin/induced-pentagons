#!/usr/bin/env python3
"""Independent finite checks for the stability referee review.

This program reconstructs the Clebsch graph directly from its five F_2^4
generators. It does not import the project's graph data, certificate, or
verification modules. Its output checks finite inputs, not the analytic
graphon stability theorem.
"""

from __future__ import annotations

import _bootstrap  # local CLI module paths only

from fractions import Fraction as Q
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import json
import random


ROOT = Path(__file__).resolve().parents[1]
GEN = {1, 2, 4, 8, 15}
A = [[int((i ^ j) in GEN) for j in range(16)] for i in range(16)]
FULL = (1 << 16) - 1
NEIGHBORS = [sum(A[i][j] << j for j in range(16)) for i in range(16)]


def degree_list(vertices, adjacency):
    return [sum(adjacency(u, v) for v in vertices if v != u) for u in vertices]


def induced_c5(vertices, adjacency):
    # A simple graph on five vertices with all degrees two must be C_5.
    return len(vertices) == 5 and degree_list(vertices, adjacency) == [2] * 5


def main():
    if not __debug__:
        raise RuntimeError('Exact referee stability checks refuse Python -O, -OO, or PYTHONOPTIMIZE.')
    adjacency = lambda i, j: A[i][j]
    cycles = [s for s in combinations(range(16), 5) if induced_c5(s, adjacency)]
    paths = []
    for s in combinations(range(16), 4):
        deg = degree_list(s, adjacency)
        if sorted(deg) != [1, 1, 2, 2]:
            continue
        endpoints = tuple(s[i] for i, d in enumerate(deg) if d == 1)
        internal = tuple(s[i] for i, d in enumerate(deg) if d == 2)
        # The degree pattern alone could also describe a triangle and an
        # isolated vertex only if the isolated degree were zero; it is not.
        paths.append((endpoints, internal))

    c = [0] * (1 << 16)
    for endpoints, internal in paths:
        em = sum(1 << i for i in endpoints)
        im = sum(1 << i for i in internal)
        free = FULL ^ (em | im)
        sub = free
        while True:
            c[em | sub] += 1
            if not sub:
                break
            sub = (sub - 1) & free
    deficits = [12 * n.bit_count() - c[n] for n in range(1 << 16)]
    zero_masks = [n for n, d in enumerate(deficits) if d == 0]
    expected_zero_masks = sorted([0] + NEIGHBORS)
    assert min(deficits) == 0
    assert zero_masks == expected_zero_masks

    pair_counts = [[sum(i in s and j in s for s in cycles) if i != j else 0
                    for j in range(16)] for i in range(16)]
    vertex_counts = [sum(i in s for s in cycles) for i in range(16)]
    assert len(cycles) == 192
    assert set(vertex_counts) == {60}
    assert all(pair_counts[i][j] == (24 if A[i][j] else 12)
               for i in range(16) for j in range(16) if i != j)

    two_vertex = {}
    for label, i, j in [("equal", 0, 0), ("adjacent", 0, 1), ("nonadjacent", 0, 3)]:
        values = []
        for edge in [0, 1]:
            def extended(u, v):
                if u < 16 and v < 16:
                    return A[u][v]
                if {u, v} == {16, 17}:
                    return edge
                if u >= 16:
                    u, v = v, u
                return A[i if v == 16 else j][u]
            values.append(sum(induced_c5((16, 17) + old, extended)
                              for old in combinations(range(16), 3)))
        two_vertex[label] = values
    assert two_vertex == {"equal": [0, 0], "adjacent": [0, 24], "nonadjacent": [12, 6]}

    hessian = []
    for i in range(16):
        row = []
        for j in range(16):
            actual = (Q(pair_counts[i][j], 192) - Q(60 * 60, 192 ** 2)
                      - Q(5, 2) * (Q(A[i][j], 40) - Q(25, 40 ** 2)))
            expected = Q(1 - 16 * (i == j), 256)
            assert actual == expected
            row.append(str(actual))
        hessian.append(row)

    prototypes = [[Q((m >> i) & 1) for i in range(16)] for m in expected_zero_masks]
    profiles = []
    for proto in prototypes:
        for i in range(16):
            for t in [Q(1, 32), Q(1, 2)]:
                p = proto.copy()
                p[i] = (1 - t) * p[i] + t * (1 - p[i])
                profiles.append(p)
    rng = random.Random(20261027)
    profiles += [[Q(rng.randrange(17), 16) for _ in range(16)] for _ in range(64)]
    min_profile_margin = None
    for p in profiles:
        cp = sum(p[e[0]] * p[e[1]] * (1 - p[q[0]]) * (1 - p[q[1]])
                 for e, q in paths)
        lhs = 12 * sum(p) - cp
        distance = min(sum(abs(x - y) for x, y in zip(p, r)) for r in prototypes)
        margin = lhs - distance / 272
        assert margin >= 0
        min_profile_margin = margin if min_profile_margin is None else min(min_profile_margin, margin)

    # The row-separation and rounding constants used in Sections 8 and 9.
    distances = sorted({(x ^ y).bit_count() for x, y in combinations(expected_zero_masks, 2)})
    assert distances == [5, 6, 10]
    assert 1 + Q(140, 1) / Q(5, 32) == 897

    # Exact integer-offset arithmetic checks, including negative offsets.
    psi_trials = 0
    for k in range(1, 101):
        trial_offsets = {k * 5 // 2, -1, 0, 1}
        for j in trial_offsets:
            m = 40 * k * k + j
            def energy(n):
                r = n % 16
                return abs(Q(m) - Q(5 * n * n, 32)) + Q(r * (16 - r), 16)
            values = [energy(n) for n in range(16 * k + 17)]
            assert min(values) == abs(j)
            assert values.index(min(values)) == 16 * k
            psi_trials += 1

    source_files = ["paper/sections06-10.tex", "paper/appendixA.tex",
                    "paper/sections01-05.tex"]
    result = {
        "status": "PASS",
        "scope": "Independent exact finite checks only; not a machine verification of analytic stability.",
        "construction": "Vertices 0,...,15, adjacency iff xor is in {1,2,4,8,15}.",
        "induced_pentagons": len(cycles),
        "induced_P4s": len(paths),
        "boolean_profiles_checked": len(deficits),
        "boolean_profile_zero_masks": zero_masks,
        "minimum_positive_boolean_profile_deficit": min(d for d in deficits if d > 0),
        "two_vertex_completion_counts_absent_present": two_vertex,
        "log_ratio_hessian_exact_entries_checked": 256,
        "fractional_profiles_checked_exactly": len(profiles),
        "minimum_sampled_fractional_profile_margin": str(min_profile_margin),
        "prototype_Hamming_distances": distances,
        "balanced_rounding_constant": 897,
        "arithmetic_psi_trials": psi_trials,
        "source_sha256": {f: sha256((ROOT / f).read_bytes()).hexdigest() for f in source_files},
        "checker_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    out = ROOT / "audit/stability_input_checks.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
