#!/usr/bin/env python3
"""Independently check seven-host support via false twins and induced embeddings.

This does not import the support builder or use its domain propagation. A
realizable host can identify only nonadjacent vertices having identical open
neighborhoods (false twins). Conversely, replacing every false-twin class by
one representative preserves realizability: copy the representative's latent
class back to every member. Distinct quotient vertices must use distinct
latent classes. Isolated vertices may all use the added isolated class.

Thus support is equivalent to an induced embedding of the nonisolated
false-twin quotient into Clebsch. Here Clebsch is constructed on even subsets
of a five-element set, adjacent when their symmetric difference has size four.
NetworkX VF2 checks induced subgraph isomorphism without fixing a target root.
"""
from __future__ import annotations

import _bootstrap  # local CLI module paths only

import argparse
import hashlib
import json
from itertools import combinations
from pathlib import Path

import networkx as nx


ROOT = Path(__file__).resolve().parents[1]


def independently_construct_clebsch():
    vertices = [x for x in range(32) if x.bit_count() % 2 == 0]
    graph = nx.Graph()
    graph.add_nodes_from(vertices)
    graph.add_edges_from((x, y) for x, y in combinations(vertices, 2)
                         if (x ^ y).bit_count() == 4)
    assert len(graph) == 16 and graph.number_of_edges() == 40
    assert set(dict(graph.degree()).values()) == {5}
    assert sum(nx.triangles(graph).values()) == 0
    # Explicit isomorphism to the data's four-bit Cayley convention.
    image = {}
    for x in range(16):
        value = 0
        for i in range(4):
            if (x >> i) & 1:
                value ^= 31 ^ (1 << i)
        image[x] = value
    assert len(set(image.values())) == 16
    assert all(graph.has_edge(image[x], image[y]) ==
               ((x ^ y) in (1, 2, 4, 8, 15))
               for x, y in combinations(range(16), 2))
    return graph, image


def quotient(graph):
    by_neighborhood = {}
    for v in graph:
        neighbors = frozenset(graph[v])
        if neighbors:
            by_neighborhood.setdefault(neighbors, []).append(v)
    classes = list(by_neighborhood.values())
    reduced = nx.Graph()
    reduced.add_nodes_from(range(len(classes)))
    for i, j in combinations(range(len(classes)), 2):
        value = graph.has_edge(classes[i][0], classes[j][0])
        assert all(graph.has_edge(a, b) == value
                   for a in classes[i] for b in classes[j])
        if value:
            reduced.add_edge(i, j)
    assert all(not graph.has_edge(a, b)
               for part in classes for a, b in combinations(part, 2))
    return reduced, classes


def audit(atlas_path, support_path):
    if not __debug__:
        raise RuntimeError('Equality-support verification refuses disabled assertions.')
    atlas = json.loads(atlas_path.read_text())
    supplied = json.loads(support_path.read_text())
    clebsch, image = independently_construct_clebsch()
    inverse_image = {b: a for a, b in image.items()}
    records = supplied["hosts"]
    assert len(atlas["hosts"]) == len(records) == 1044
    assert [r["host_index"] for r in records] == list(range(1044))
    supported = []
    triangle_free_excluded = []
    triangle_hosts = []
    independent_witnesses = []
    quotient_order_counts = {}
    pairs = list(combinations(range(7), 2))
    for h, (source, original) in enumerate(zip(atlas["hosts"], records)):
        assert source["index"] == h
        mask = source["mask"]
        assert original["host_mask"] == mask
        graph = nx.Graph()
        graph.add_nodes_from(range(7))
        graph.add_edges_from(pair for bit, pair in enumerate(pairs)
                             if (mask >> bit) & 1)
        assert {tuple(e) for e in source["edges"]} == set(graph.edges())
        if sum(nx.triangles(graph).values()):
            triangle_hosts.append(h)
            realized = False
            witness = None
        else:
            reduced, classes = quotient(graph)
            quotient_order_counts[len(reduced)] = quotient_order_counts.get(len(reduced), 0) + 1
            matcher = nx.algorithms.isomorphism.GraphMatcher(clebsch, reduced)
            mapping = next(matcher.subgraph_isomorphisms_iter(), None)
            realized = mapping is not None
            witness = None
            if realized:
                witness = [16] * 7
                quotient_to_latent = {v: inverse_image[u] for u, v in mapping.items()}
                for q, part in enumerate(classes):
                    for v in part:
                        witness[v] = quotient_to_latent[q]
                for i, j in pairs:
                    actual_edge = (witness[i] != 16 and witness[j] != 16 and
                                   clebsch.has_edge(image[witness[i]], image[witness[j]]))
                    assert actual_edge == graph.has_edge(i, j)
            else:
                triangle_free_excluded.append({
                    "host_index": h, "host_mask": mask,
                    "quotient_order": len(reduced),
                    "quotient_edges": [list(e) for e in reduced.edges()],
                    "false_twin_classes": classes
                })
        assert original["supported"] is realized, f"Support discrepancy at host {h}"
        if realized:
            supported.append(h)
            independent_witnesses.append({"host_index": h, "latent_assignment": witness})
            # Check the saved builder's witness using the independent 5-bit model.
            old = original["latent_assignment"]
            assert len(old) == 7 and all(type(x) is int and 0 <= x <= 16 for x in old)
            for i, j in pairs:
                present = (old[i] != 16 and old[j] != 16 and
                           clebsch.has_edge(image[old[i]], image[old[j]]))
                assert present == graph.has_edge(i, j)
        else:
            assert original["latent_assignment"] is None
    assert supplied["supported_host_indices"] == supported
    assert supplied["supported_host_count"] == len(supported)
    assert len(supported) + len(triangle_hosts) + len(triangle_free_excluded) == 1044
    return {
        "schema": "induced-pentagons.equality-support-independent-audit.v1",
        "status": "verified_exact_by_independent_algorithm",
        "method": "False-twin quotient and induced VF2 embedding into the even-five-bit Clebsch graph; no fixed target root or support-builder imports.",
        "networkx_version": nx.__version__,
        "atlas_sha256": hashlib.sha256(atlas_path.read_bytes()).hexdigest(),
        "support_sha256": hashlib.sha256(support_path.read_bytes()).hexdigest(),
        "host_count": 1044,
        "supported_host_count": len(supported),
        "excluded_host_count": 1044-len(supported),
        "triangle_free_host_count": 1044-len(triangle_hosts),
        "excluded_triangle_host_count": len(triangle_hosts),
        "excluded_triangle_free_host_count": len(triangle_free_excluded),
        "supported_host_indices": supported,
        "triangle_free_quotient_order_counts": quotient_order_counts,
        "triangle_free_excluded": triangle_free_excluded,
        "independent_witnesses": independent_witnesses,
        "zero_slack_distinction": "Support is a subset of zero-slack hosts in any nonnegative equality certificate. A certificate may have additional zero coefficients on unsupported hosts. Therefore 1044-795=249 zero slack coefficients does not imply 249 realizable hosts."
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-dir", type=Path, default=ROOT/"certificates")
    parser.add_argument("--output", type=Path,
                        default=ROOT/"audit/equality_support_independent_audit.json")
    args = parser.parse_args()
    report = audit(args.data_dir/"graph_atlas_7.json", args.data_dir/"equality_host_support.json")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({k: report[k] for k in (
        "status", "host_count", "supported_host_count", "excluded_host_count",
        "triangle_free_host_count", "excluded_triangle_host_count",
        "excluded_triangle_free_host_count")}, indent=2))


if __name__ == "__main__":
    main()
