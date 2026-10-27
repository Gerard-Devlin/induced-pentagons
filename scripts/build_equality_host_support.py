#!/usr/bin/env python3
"""Find exactly which seven-vertex hosts occur in padded Clebsch graphons.

All computation uses integer bitsets. A host is supported precisely when its
adjacency matrix is realizable by seven latent classes in Clebsch plus an
isolated class. Repeated latent classes are permitted. Isolated host vertices
may be placed in class 16 without changing realizability. By vertex transitivity
the first nonisolated host vertex may be placed in Clebsch class 0. Exhaustive
constraint propagation searches every remaining assignment.
"""
from __future__ import annotations

import _bootstrap  # local CLI module paths only

import argparse
import json
from pathlib import Path


GENERATORS = (1, 2, 4, 8, 15)
NEIGHBORS = [sum(1 << (i ^ s) for s in GENERATORS) for i in range(16)]
FULL = (1 << 16) - 1


def find_witness(edge_list, order=7):
    adjacency = [0]*order
    for i, j in edge_list:
        adjacency[i] |= 1 << j
        adjacency[j] |= 1 << i
    active = [i for i in range(order) if adjacency[i]]
    assignment = [16]*order
    domains = {i: FULL for i in active}
    if active:
        first = max(active, key=lambda i: adjacency[i].bit_count())
        domains[first] = 1  # translate its active latent class to zero
    search_nodes = 0

    def visit(current):
        nonlocal search_nodes
        search_nodes += 1
        if not current:
            return assignment.copy()
        i = min(current, key=lambda v: (current[v].bit_count(),
                                       -adjacency[v].bit_count(), v))
        choices = current[i]
        while choices:
            bit = choices & -choices
            choices -= bit
            latent = bit.bit_length()-1
            assignment[i] = latent
            updated = {}
            for j, domain in current.items():
                if j == i:
                    continue
                allowed = (NEIGHBORS[latent] if (adjacency[i] >> j) & 1
                           else FULL ^ NEIGHBORS[latent])
                remaining = domain & allowed
                if not remaining:
                    break
                updated[j] = remaining
            else:
                result = visit(updated)
                if result is not None:
                    return result
        return None

    result = visit(domains)
    if result is not None:
        edge_set = {tuple(sorted(e)) for e in edge_list}
        for i in range(order):
            for j in range(i+1, order):
                realized = (result[i] != 16 and result[j] != 16
                            and result[i] ^ result[j] in GENERATORS)
                assert ((i, j) in edge_set) == realized
    return result, search_nodes


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--atlas", type=Path, default=root/"certificates/graph_atlas_7.json")
    parser.add_argument("--output", type=Path, default=root/"certificates/equality_host_support.json")
    args = parser.parse_args()
    atlas = json.loads(args.atlas.read_text(encoding="utf-8"))
    results = []
    total_nodes = 0
    for host in atlas["hosts"]:
        witness, nodes = find_witness(host["edges"])
        total_nodes += nodes
        results.append({"host_index": host["index"], "host_mask": host["mask"],
                        "supported": witness is not None,
                        "latent_assignment": witness, "search_nodes": nodes})
    supported = [r["host_index"] for r in results if r["supported"]]
    data = {"schema": "induced-pentagons.equality-host-support.v1",
            "status": "exact exhaustive realizability computation",
            "supported_host_count": len(supported),
            "supported_host_indices": supported,
            "total_search_nodes": total_nodes,
            "class_convention": "0..15 Clebsch vertices, 16 isolated; repetitions allowed",
            "hosts": results}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(f"Supported hosts: {len(supported)} / {len(results)}; search nodes: {total_nodes}")


if __name__ == "__main__":
    main()
