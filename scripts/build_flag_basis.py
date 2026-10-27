#!/usr/bin/env python3
"""Generate the complete order-seven atlas and five exact flag spaces.

This file regenerates the combinatorial inputs used by the replacement
certificate. The separate rational identity and equality-span checkers verify
the proof witnesses; counting the inputs alone does not prove the inequality.

Dependencies: Python >=3.10, numpy, networkx, sympy; a C++17 compiler.
All output graph-mask bits follow itertools.combinations(range(n), 2).
"""
from __future__ import annotations

import _bootstrap  # local CLI module paths only

import argparse
import ctypes
import hashlib
import itertools
import json
import math
from pathlib import Path
import subprocess
import sys
import tempfile

import networkx as nx
import numpy as np
import sympy as sp


BLOCKS = (
    ("one_root", 1, 4, (), 20),
    ("independent3", 3, 5, (), 72),
    ("edge_isolate", 3, 5, ((0, 1),), 72),
    ("path3", 3, 5, ((0, 1), (1, 2)), 72),
    ("triangle3", 3, 5, ((0, 1), (0, 2), (1, 2)), 72),
)


def edges(mask: int, n: int) -> list[list[int]]:
    return [[i, j] for bit, (i, j) in enumerate(itertools.combinations(range(n), 2))
            if (int(mask) >> bit) & 1]


def mask_of_edges(edge_list, n: int) -> int:
    lookup = {pair: i for i, pair in enumerate(itertools.combinations(range(n), 2))}
    return sum(1 << lookup[tuple(sorted(pair))] for pair in edge_list)


def relabel(mask: int, permutation: tuple[int, ...]) -> int:
    n = len(permutation)
    return mask_of_edges(((permutation[i], permutation[j])
                          for i, j in edges(mask, n)), n)


def flag_data(roots: int, n: int, root_edges, dimension: int):
    pairs = list(itertools.combinations(range(n), 2))
    root_pairs = {(i, j) for i, j in pairs if j < roots}
    required = set(root_edges)
    permutations = [tuple(range(roots)) + p
                    for p in itertools.permutations(range(roots, n))]
    canonical = {}
    for mask in range(1 << len(pairs)):
        actual = {pair for bit, pair in enumerate(pairs)
                  if pair in root_pairs and (mask >> bit) & 1}
        if actual != required:
            continue
        canonical[mask] = min(relabel(mask, p) for p in permutations)
    masks = sorted(set(canonical.values()))
    assert len(masks) == dimension, (roots, n, len(masks), dimension)
    index = {mask: i for i, mask in enumerate(masks)}
    lookup = np.full(1 << len(pairs), -1, dtype=np.int32)
    for raw, canonical_mask in canonical.items():
        lookup[raw] = index[canonical_mask]
    flags = []
    for i, mask in enumerate(masks):
        edge_set = {tuple(pair) for pair in edges(mask, n)}
        triangle_free = not any(all(tuple(sorted(pair)) in edge_set
                                    for pair in itertools.combinations(triple, 2))
                                for triple in itertools.combinations(range(n), 3))
        flags.append({"index": i, "mask": mask, "edges": edges(mask, n),
                      "triangle_free": triangle_free})
    return masks, lookup, flags


def load_accelerator(source: Path, build_dir: Path, compiler: str):
    shared = build_dir / "flag_basis_accelerator.so"
    subprocess.run([compiler, "-O3", "-std=c++17", "-fPIC", "-shared",
                    str(source), "-o", str(shared)], check=True)
    lib = ctypes.CDLL(str(shared))
    u32 = np.ctypeslib.ndpointer(dtype=np.uint32, flags="C_CONTIGUOUS")
    i32 = np.ctypeslib.ndpointer(dtype=np.int32, flags="C_CONTIGUOUS")
    i64 = np.ctypeslib.ndpointer(dtype=np.int64, flags="C_CONTIGUOUS")
    lib.canonical7.argtypes = [u32, ctypes.c_int, u32, u32]
    lib.canonical7.restype = None
    lib.host_flag_counts.argtypes = [u32, ctypes.c_int, ctypes.c_int,
                                    ctypes.c_int, ctypes.c_int, i32, i32]
    lib.host_flag_counts.restype = None
    lib.equality_flag_rows.argtypes = [ctypes.c_int, ctypes.c_int,
                                      ctypes.c_int, i32, i64, i32]
    lib.equality_flag_rows.restype = ctypes.c_int
    return lib


def primitive_integer_basis(rows: np.ndarray, dimension: int):
    matrix = sp.Matrix(rows.tolist()) if len(rows) else sp.zeros(0, dimension)
    vectors = matrix.nullspace()
    cols = []
    for v in vectors:
        denominator = sp.ilcm(*[entry.q for entry in v])
        integers = [int(entry * denominator) for entry in v]
        gcd = math.gcd(*integers)
        integers = [value // gcd for value in integers]
        if next(value for value in integers if value) < 0:
            integers = [-value for value in integers]
        cols.append(integers)
    B = np.array(cols, dtype=np.int64).T if cols else np.empty((dimension, 0), np.int64)
    # Exact SymPy check avoids silently trusting int64 products.
    assert matrix * sp.Matrix(B.tolist()) == sp.zeros(len(rows), B.shape[1])
    assert sp.Matrix(B.tolist()).rank() == B.shape[1]
    row_pivots = list(matrix.T.rref()[1])
    return B, row_pivots


def python_host_counts(mask: int, roots: int, n: int, root_edges,
                       lookup: np.ndarray, dimension: int) -> np.ndarray:
    """Independent, deliberately simple cross-check for selected hosts."""
    edge_set = {tuple(pair) for pair in edges(mask, 7)}
    result = np.zeros((dimension, dimension), np.int32)
    def adjacent(a, b):
        return tuple(sorted((a, b))) in edge_set
    def induced(vertices):
        return sum((1 << bit) for bit, (i, j) in
                   enumerate(itertools.combinations(range(n), 2))
                   if adjacent(vertices[i], vertices[j]))
    for root_tuple in itertools.permutations(range(7), roots):
        actual = {(i, j) for i, j in itertools.combinations(range(roots), 2)
                  if adjacent(root_tuple[i], root_tuple[j])}
        if actual != set(root_edges):
            continue
        remainder = sorted(set(range(7)) - set(root_tuple))
        for extension in itertools.combinations(remainder, n-roots):
            complement = tuple(v for v in remainder if v not in extension)
            first = int(lookup[induced(root_tuple + extension)])
            second = int(lookup[induced(root_tuple + complement)])
            result[first, second] += 1
    return result


def python_equality_counts(root_assignment, n: int, lookup, dimension: int):
    """Independent Python construction, with repeated latent classes allowed."""
    result = [0]*dimension
    for extension in itertools.product(range(17), repeat=n-len(root_assignment)):
        vertices = list(root_assignment)+list(extension)
        mask = sum(1 << bit for bit, (i, j) in
                   enumerate(itertools.combinations(range(n), 2))
                   if vertices[i] != 16 and vertices[j] != 16
                   and vertices[i] ^ vertices[j] in (1, 2, 4, 8, 15))
        weight = 32**sum(v == 16 for v in extension)
        result[int(lookup[mask])] += weight
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parents[1] / "certificates")
    parser.add_argument("--compiler", default="g++")
    parser.add_argument("--skip-independent-checks", action="store_true")
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    source = Path(__file__).with_name("flag_basis_accelerator.cpp")
    with tempfile.TemporaryDirectory(prefix="pentagon-flag-build-") as temporary:
        lib = load_accelerator(source, Path(temporary), args.compiler)
        raw_masks = np.array([mask_of_edges(g.edges(), 7)
                              for g in nx.graph_atlas_g() if len(g) == 7],
                             dtype=np.uint32)
        assert len(raw_masks) == 1044
        canonical = np.empty_like(raw_masks)
        automorphisms = np.empty_like(raw_masks)
        lib.canonical7(raw_masks, len(raw_masks), canonical, automorphisms)
        order = np.argsort(canonical)
        hosts = np.ascontiguousarray(canonical[order])
        aut = np.ascontiguousarray(automorphisms[order])
        assert len(np.unique(hosts)) == 1044
        orbit_sizes = np.array([5040//int(a) for a in aut], np.int32)
        assert all(5040 % int(a) == 0 for a in aut)
        assert int(orbit_sizes.sum()) == 1 << 21
        for edge_count in range(22):
            assert sum(int(orbit_sizes[i]) for i, mask in enumerate(hosts)
                       if int(mask).bit_count() == edge_count) == math.comb(21, edge_count)
        (args.output_dir / "host_masks.txt").write_text(
            "".join(f"{int(mask)}\n" for mask in hosts), encoding="utf-8")
        atlas = {"schema": "induced-pentagons.graph-atlas.v1", "order": 7,
                 "mask_convention": "lexicographic pairs (i,j), 0<=i<j<n; bit0=(0,1)",
                 "canonicalization": "minimum over all 7! vertex permutations",
                 "host_count": 1044, "labelled_graph_count": 1 << 21,
                 "hosts": [{"index": i, "mask": int(mask), "edges": edges(mask, 7),
                            "edge_count": int(mask).bit_count(),
                            "automorphism_order": int(aut[i]),
                            "orbit_size": int(orbit_sizes[i])}
                           for i, mask in enumerate(hosts)]}
        (args.output_dir / "graph_atlas_7.json").write_text(
            json.dumps(atlas, indent=2) + "\n", encoding="utf-8")
        print("Atlas complete: 1044 canonical hosts; orbit sum = 2097152.", flush=True)
        arrays = {"host_masks": hosts, "host_automorphism_orders": aut,
                  "host_orbit_sizes": orbit_sizes}
        spaces = {"schema": "induced-pentagons.flag-spaces.v1",
                  "status": "exact combinatorial inputs; no SOS inequality claimed",
                  "equality_model": {"classes": 17,
                                     "active_class_vertices": list(range(16)),
                                     "isolated_class_vertex": 16,
                                     "integer_class_weights": [1]*16+[32],
                                     "total_weight": 48,
                                     "clebsch_xor_generators": [1, 2, 4, 8, 15]},
                  "mask_convention": atlas["mask_convention"],
                  "flag_canonicalization": "minimum under extension permutations only",
                  "blocks": {}}
        for name, roots, n, root_edges, dimension in BLOCKS:
            masks, lookup, flags = flag_data(roots, n, root_edges, dimension)
            signature = mask_of_edges(root_edges, roots) if roots > 1 else 0
            counts = np.zeros((1044, dimension, dimension), np.int32)
            lib.host_flag_counts(hosts, len(hosts), roots, signature, dimension,
                                 lookup, counts)
            denominator = 140 if roots == 1 else 1260
            assert np.array_equal(counts, counts.transpose(0, 2, 1))
            assert np.all(counts >= 0)
            if roots == 1:
                assert np.all(counts.sum(axis=(1, 2)) == denominator)
            else:
                expected = []
                for host_mask in hosts:
                    edge_set = {tuple(pair) for pair in edges(int(host_mask), 7)}
                    root_count = 0
                    for assignment in itertools.permutations(range(7), roots):
                        actual = {(i, j) for i, j in itertools.combinations(range(roots), 2)
                                  if tuple(sorted((assignment[i],assignment[j]))) in edge_set}
                        root_count += actual == set(root_edges)
                    expected.append(6*root_count)
                assert np.array_equal(counts.sum(axis=(1,2)), np.array(expected))
            if not args.skip_independent_checks:
                for h in (0, 1, 97, 521, 912, 1043):
                    independent = python_host_counts(int(hosts[h]), roots, n,
                                                     root_edges, lookup, dimension)
                    assert np.array_equal(independent, counts[h]), (name, h)
            raw_rows = np.zeros((17**roots, dimension), np.int64)
            raw_roots = np.zeros((17**roots, roots), np.int32)
            row_count = lib.equality_flag_rows(roots, signature, dimension,
                                               lookup, raw_rows, raw_roots)
            raw_rows, raw_roots = raw_rows[:row_count], raw_roots[:row_count]
            q_denominator = 48**(n-roots)
            assert np.all(raw_rows.sum(axis=1) == q_denominator)
            unique_rows, first_indices = np.unique(raw_rows, axis=0, return_index=True)
            if not args.skip_independent_checks:
                for representative, expected_row in zip(raw_roots[first_indices], unique_rows):
                    actual_row = python_equality_counts(representative, n, lookup, dimension)
                    assert actual_row == expected_row.tolist(), (name, representative)
            B, row_pivots = primitive_integer_basis(unique_rows, dimension)
            rank = len(row_pivots)
            assert rank + B.shape[1] == dimension
            # Positive square vectors need not be linearly independent.
            # Their count need not equal the equality-kernel dimension.
            arrays["C_"+name] = counts
            arrays["B_"+name] = B
            arrays["Q_"+name] = unique_rows
            arrays["Q_basis_"+name] = unique_rows[row_pivots]
            arrays["flag_masks_"+name] = np.array(masks,np.uint32)
            arrays["denominator_"+name] = np.array(denominator,np.int32)
            spaces["blocks"][name] = {
                "roots": roots, "flag_order": n, "root_edges": list(root_edges),
                "dimension": dimension, "host_sampling_denominator": denominator,
                "flags": flags, "triangle_free_count": sum(f["triangle_free"] for f in flags),
                "equality_row_denominator": q_denominator,
                "compatible_root_assignments": row_count,
                "unique_equality_row_count": len(unique_rows),
                "equality_row_rank": rank, "kernel_dimension": B.shape[1],
                "unique_equality_rows": unique_rows.tolist(),
                "equality_row_representatives": raw_roots[first_indices].tolist(),
                "independent_equality_row_indices": row_pivots,
                "integer_kernel_basis_columns": B.T.tolist(),
                "kernel_basis_convention": "primitive integer columns, first nonzero entry positive",
            }
            print(f"{name}: {dimension} flags, {row_count} compatible roots, "
                  f"{len(unique_rows)} distinct q rows, rank {rank}, "
                  f"kernel dimension {B.shape[1]}", flush=True)
        np.savez_compressed(args.output_dir / "flag_basis.npz", **arrays)
        (args.output_dir / "flag_spaces.json").write_text(
            json.dumps(spaces, indent=2) + "\n", encoding="utf-8")
        print("Saved flag_basis.npz, flag_spaces.json, graph_atlas_7.json, host_masks.txt", flush=True)


if __name__ == "__main__":
    main()
