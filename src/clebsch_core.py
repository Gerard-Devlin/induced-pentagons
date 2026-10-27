"""Exact finite computations for induced pentagons under an edge constraint.

No external libraries are required. These routines certify finite combinatorial
identities only; they do not prove the manuscript's global extremal inequality.
"""
from __future__ import annotations

import _bootstrap  # local CLI module paths only
from itertools import combinations, permutations
from typing import Iterable, Sequence

GENERATORS = (1, 2, 4, 8, 15)
N = 16
FULL = (1 << N) - 1
ADJ = tuple(sum(1 << (u ^ s) for s in GENERATORS) for u in range(N))
EDGES = tuple((u, v) for u in range(N) for v in range(u + 1, N) if ADJ[u] >> v & 1)


def edge(u: int, v: int) -> bool:
    return bool(ADJ[u] >> v & 1)


def is_induced_c5(vertices: Sequence[int], adj: Sequence[int]) -> bool:
    if len(vertices) != 5 or len(set(vertices)) != 5:
        return False
    mask = sum(1 << v for v in vertices)
    # A simple 2-regular graph on five vertices can only be C5.
    return all((adj[v] & mask).bit_count() == 2 for v in vertices)


def pentagons(adj: Sequence[int] = ADJ) -> tuple[tuple[int, ...], ...]:
    return tuple(vs for vs in combinations(range(len(adj)), 5) if is_induced_c5(vs, adj))


CYCLES = pentagons()


def induced_p4s() -> tuple[tuple[int, int, int, int], ...]:
    """Return (endpoint1, endpoint2, internal1, internal2), once per four-set."""
    result = []
    for vs in combinations(range(N), 4):
        mask = sum(1 << v for v in vs)
        ds = {v: (ADJ[v] & mask).bit_count() for v in vs}
        if sorted(ds.values()) == [1, 1, 2, 2]:
            ends = sorted(v for v in vs if ds[v] == 1)
            mids = sorted(v for v in vs if ds[v] == 2)
            result.append((*ends, *mids))
    return tuple(result)


PATHS = induced_p4s()


def all_profile_counts() -> list[int]:
    """Subset-accumulation algorithm, independent of the direct checker."""
    counts = [0] * (1 << N)
    for u, v, a, b in PATHS:
        required = (1 << u) | (1 << v)
        excluded = (1 << a) | (1 << b)
        free = FULL ^ (required | excluded)
        sub = free
        while True:
            counts[required | sub] += 1
            if not sub:
                break
            sub = (sub - 1) & free
    return counts


def profile_count_direct(mask: int) -> int:
    return sum((mask >> u & 1) and (mask >> v & 1)
               and not (mask >> a & 1) and not (mask >> b & 1)
               for u, v, a, b in PATHS)


def edge_quadratic(h: Sequence[int]) -> int:
    return sum(h[u] * h[v] for u, v in EDGES)


def poly_add(a: Sequence[int], b: Sequence[int]) -> tuple[int, ...]:
    n = max(len(a), len(b))
    return tuple((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n))


def poly_mul_linear(p: Sequence[int], constant: int) -> tuple[int, ...]:
    q = [0] * (len(p) + 1)
    for i, v in enumerate(p):
        q[i] += constant * v
        q[i + 1] += v
    return tuple(q)


def template_polynomial(h: Sequence[int]) -> tuple[int, ...]:
    """Ascending coefficients of P(k*1+h)."""
    total: tuple[int, ...] = (0,) * 6
    for vs in CYCLES:
        p = (1,)
        for v in vs:
            p = poly_mul_linear(p, h[v])
        total = poly_add(total, p)
    return total


def evaluate(p: Sequence[int], k: int) -> int:
    value = 0
    for a in reversed(p):
        value = value * k + a
    return value


def construction_polynomial(h: Sequence[int], types: Sequence[int],
                            toggles: Sequence[tuple[int, int]]) -> tuple[int, ...]:
    """Exact count for a template plus exceptional vertices and toggled pairs.

    Active types are 0..15, isolated type is -1. Active exceptional vertices
    already belong to the k+h_i vertices of their class. The only modified
    pairs have BOTH endpoints in the exceptional list.
    """
    if len(h) != 16 or any(t < -1 or t >= 16 for t in types):
        raise ValueError('Invalid class deviations or exceptional types')
    s = len(types)
    flips = {tuple(sorted(e)) for e in toggles}
    if any(a == b or a < 0 or b >= s for a, b in flips):
        raise ValueError('Invalid exceptional edge')
    ecounts = [types.count(i) for i in range(16)]
    all_types = list(types) + list(range(16))
    oldadj = [0] * (s + 16)
    newadj = [0] * (s + 16)
    for u, v in combinations(range(s + 16), 2):
        a, b = all_types[u], all_types[v]
        before = a >= 0 and b >= 0 and edge(a, b)
        after = before ^ ((u, v) in flips)
        if before:
            oldadj[u] |= 1 << v
            oldadj[v] |= 1 << u
        if after:
            newadj[u] |= 1 << v
            newadj[v] |= 1 << u
    total = template_polynomial(h)
    candidates: set[tuple[int, ...]] = set()
    for a, b in flips:
        other = [v for v in range(s + 16) if v != a and v != b]
        for rest in combinations(other, 3):
            candidates.add(tuple(sorted((a, b, *rest))))
    for vs in candidates:
        delta = int(is_induced_c5(vs, newadj)) - int(is_induced_c5(vs, oldadj))
        if not delta:
            continue
        p = (delta,)
        for v in vs:
            if v >= s:
                i = v - s
                p = poly_mul_linear(p, h[i] - ecounts[i])
        total = poly_add(total, p)
    return total


def construct_graph(k: int, h: Sequence[int], types: Sequence[int],
                    toggles: Sequence[tuple[int, int]]) -> tuple[int, ...]:
    """Build an actual graph, independently of the symbolic count routine."""
    if k < 0 or len(h) != 16:
        raise ValueError('Invalid k or deviations')
    labels = list(types)
    for i in range(16):
        remainder = k + h[i] - types.count(i)
        if remainder < 0:
            raise ValueError('Class capacity exceeded')
        labels.extend([i] * remainder)
    adj = [0] * len(labels)
    for u, v in combinations(range(len(labels)), 2):
        a, b = labels[u], labels[v]
        if a >= 0 and b >= 0 and edge(a, b):
            adj[u] |= 1 << v
            adj[v] |= 1 << u
    for u, v in toggles:
        adj[u] ^= 1 << v
        adj[v] ^= 1 << u
    return tuple(adj)


def count_c5_by_paths(adj: Sequence[int]) -> int:
    """Induced-cycle traversal, not the five-subset implementation.

    Use the unique smallest vertex as root and break reversal by first<last.
    """
    ans = 0
    n = len(adj)
    neighbors = [tuple(v for v in range(n) if adj[u] >> v & 1) for u in range(n)]
    for a in range(n):
        for b in neighbors[a]:
            if b <= a:
                continue
            for c in neighbors[b]:
                if c <= a or adj[a] >> c & 1:
                    continue
                for d in neighbors[c]:
                    if d <= a or d == b or adj[a] >> d & 1 or adj[b] >> d & 1:
                        continue
                    candidates = adj[d] & adj[a] & ~adj[b] & ~adj[c]
                    while candidates:
                        bit = candidates & -candidates
                        candidates -= bit
                        e = bit.bit_length() - 1
                        if e > a and e > b and e not in (c, d):
                            ans += 1
    return ans
