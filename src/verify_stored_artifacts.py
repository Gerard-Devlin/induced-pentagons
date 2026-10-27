#!/usr/bin/env python3
"""Bind the published data views to independently checked computations.

The project driver first independently recounts the integer flag and pattern
arrays. This module then compares EVERY field of the published atlas, flag,
pattern, finite-Clebsch, profile, and small-offset views to that verified data
or to fresh finite results supplied by the caller. It additionally reconstructs
all conditional equality-model rows and their exact kernel bases.

No production generator is imported. The finite Clebsch objects/functions are
the same independently checked objects used by verify_finite/verify_profiles.
Float arrays are checked only as redundant discovery caches; no floating-point
value is used to establish a combinatorial or rational identity.
"""
from __future__ import annotations

import _bootstrap  # local CLI module paths only

from fractions import Fraction
from hashlib import sha256
from itertools import combinations, permutations, product
from math import comb, factorial, gcd, lcm
from pathlib import Path
import argparse
import json

import numpy as np
import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
PSTAR = Fraction(5, 144)
TAU = Fraction(5, 663552)
KAPPA = TAU / (2 * PSTAR)
MASK_CONVENTION = 'lexicographic pairs (i,j), 0<=i<j<n; bit0=(0,1)'
GENERATORS = (1, 2, 4, 8, 15)
BLOCKS = (
    ('one_root', 1, 4, (), 20),
    ('independent3', 3, 5, (), 72),
    ('edge_isolate', 3, 5, ((0, 1),), 72),
    ('path3', 3, 5, ((0, 1), (1, 2)), 72),
    ('triangle3', 3, 5, ((0, 1), (0, 2), (1, 2)), 72),
)


class StoredArtifactMismatch(ValueError):
    """A published view disagrees with the verified value at a named path."""


def _guard():
    if not __debug__:
        raise RuntimeError('Exact stored-artifact verification refuses Python -O, -OO, or PYTHONOPTIMIZE.')


def _plain(value):
    if isinstance(value, np.ndarray):
        return _plain(value.tolist())
    if isinstance(value, np.generic):
        return value.item()
    if isinstance(value, (list, tuple)):
        return [_plain(v) for v in value]
    if isinstance(value, dict):
        return {k: _plain(v) for k, v in value.items()}
    return value


def _brief(value):
    result = repr(value)
    return result if len(result) <= 180 else result[:177] + '...'


def _same(actual, expected, path):
    """Exact JSON semantics, including types and list order; reject extra keys."""
    expected = _plain(expected)
    if type(actual) is not type(expected):
        raise StoredArtifactMismatch(f'{path}: expected {type(expected).__name__}, got {type(actual).__name__}')
    if isinstance(expected, dict):
        if actual.keys() != expected.keys():
            missing = sorted(expected.keys() - actual.keys())
            extra = sorted(actual.keys() - expected.keys())
            raise StoredArtifactMismatch(f'{path}: missing keys {missing}; extra keys {extra}')
        for key in expected:
            _same(actual[key], expected[key], f'{path}.{key}')
    elif isinstance(expected, list):
        if len(actual) != len(expected):
            raise StoredArtifactMismatch(f'{path}: expected length {len(expected)}, got {len(actual)}')
        for i, (a, e) in enumerate(zip(actual, expected)):
            _same(a, e, f'{path}[{i}]')
    elif actual != expected:
        raise StoredArtifactMismatch(f'{path}: expected {_brief(expected)}, got {_brief(actual)}')


def _load_json(path):
    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise StoredArtifactMismatch(f'{path.name}: duplicate JSON key {key!r}')
            result[key] = value
        return result
    try:
        return json.loads(path.read_text(encoding='utf-8'), object_pairs_hook=unique_object)
    except (OSError, json.JSONDecodeError) as exc:
        raise StoredArtifactMismatch(f'{path.name}: {exc}') from exc


def _compare_file(data, name, expected):
    _same(_load_json(data / name), _plain(expected), name)


def _record(data, name, **counts):
    return {'status': 'PASS', 'sha256': sha256((data / name).read_bytes()).hexdigest(), **counts}


def _integer_array(archive, key, shape, filename):
    if key not in archive:
        raise StoredArtifactMismatch(f'{filename}.{key}: missing array')
    arr = archive[key]
    if arr.dtype.kind not in 'iu' or arr.shape != tuple(shape):
        raise StoredArtifactMismatch(f'{filename}.{key}: expected integer shape {tuple(shape)}, got {arr.dtype} {arr.shape}')
    return arr


def _array_equal(actual, expected, path):
    expected = np.asarray(expected)
    if actual.shape != expected.shape:
        raise StoredArtifactMismatch(f'{path}: expected shape {expected.shape}, got {actual.shape}')
    if not np.array_equal(actual, expected):
        index = tuple(int(v) for v in np.argwhere(actual != expected)[0])
        raise StoredArtifactMismatch(f'{path}{index}: expected {_brief(expected[index].item())}, got {_brief(actual[index].item())}')


def _edges(mask, n):
    return [[u, v] for bit, (u, v) in enumerate(combinations(range(n), 2)) if (int(mask) >> bit) & 1]


def _flag_description(roots, order, root_edges, dimension):
    pairs = tuple(combinations(range(order), 2))
    bits = {pair: bit for bit, pair in enumerate(pairs)}
    root_pairs = tuple(combinations(range(roots), 2))
    required = set(root_edges)
    maps = [tuple(bits[tuple(sorted((perm[u], perm[v])))] for u, v in pairs)
            for ext in permutations(range(roots, order))
            for perm in [tuple(range(roots)) + ext]]
    canonical = {}
    for mask in range(1 << len(pairs)):
        if {p for p in root_pairs if (mask >> bits[p]) & 1} != required:
            continue
        canonical[mask] = min(sum(((mask >> src) & 1) << dst for dst, src in enumerate(mp)) for mp in maps)
    masks = sorted(set(canonical.values()))
    _same(len(masks), dimension, 'independent flag dimension')
    index = {mask: i for i, mask in enumerate(masks)}
    lookup = np.full(1 << len(pairs), -1, dtype=np.int64)
    for raw, canonical_mask in canonical.items():
        lookup[raw] = index[canonical_mask]
    flags = []
    for i, mask in enumerate(masks):
        edge_set = {tuple(e) for e in _edges(mask, order)}
        triangle_free = not any(all(p in edge_set for p in combinations(triple, 2))
                                for triple in combinations(range(order), 3))
        flags.append({'index': i, 'mask': mask, 'edges': _edges(mask, order), 'triangle_free': triangle_free})
    return masks, lookup, flags


def _conditional_rows(roots, order, root_edges, dimension, lookup):
    """Recount every compatible latent root tuple, with repeated classes allowed."""
    adj = np.zeros((17, 17), dtype=np.int64)
    for u in range(16):
        for g in GENERATORS:
            adj[u, u ^ g] = 1
    extensions = np.array(list(product(range(17), repeat=order - roots)), dtype=np.int64)
    weights = np.prod(np.where(extensions == 16, 32, 1), axis=1, dtype=np.int64)
    pairs = tuple(combinations(range(order), 2))
    root_pairs = tuple(combinations(range(roots), 2))
    required = set(root_edges)
    ext_base = np.zeros(len(extensions), dtype=np.int64)
    for bit, (u, v) in enumerate(pairs):
        if u >= roots:
            ext_base |= adj[extensions[:, u - roots], extensions[:, v - roots]] << bit
    first = {}
    compatible = 0
    for root in product(range(17), repeat=roots):
        if {p for p in root_pairs if adj[root[p[0]], root[p[1]]]} != required:
            continue
        compatible += 1
        masks = ext_base.copy()
        for bit, (u, v) in enumerate(pairs):
            if v < roots:
                masks |= int(adj[root[u], root[v]]) << bit
            elif u < roots:
                masks |= adj[root[u], extensions[:, v - roots]] << bit
        indices = lookup[masks]
        if np.any(indices < 0):
            raise StoredArtifactMismatch('conditional equality row: sampled flag has the wrong root type')
        row = np.zeros(dimension, dtype=np.int64)
        np.add.at(row, indices, weights)
        if int(row.sum()) != 48 ** (order - roots):
            raise StoredArtifactMismatch('conditional equality row: total weight is incorrect')
        first.setdefault(tuple(map(int, row)), list(root))
    rows = sorted(first)
    return (np.array(rows, dtype=np.int64).reshape(len(rows), dimension),
            [first[row] for row in rows], compatible)


def _kernel_basis(rows, dimension):
    """Use the small exact row matrix; never row-reduce the large host matrices."""
    matrix = sp.Matrix(rows.tolist()) if len(rows) else sp.zeros(0, dimension)
    pivots = list(matrix.T.rref()[1])
    columns = []
    for vector in matrix.nullspace():
        den = lcm(*(int(value.q) for value in vector))
        column = [int(value * den) for value in vector]
        common = gcd(*column)
        column = [value // common for value in column]
        if next(value for value in column if value) < 0:
            column = [-value for value in column]
        columns.append(column)
    basis = np.array(columns, dtype=np.int64).reshape(len(columns), dimension).T
    if len(pivots) + basis.shape[1] != dimension:
        raise StoredArtifactMismatch('conditional equality kernel: rank-nullity failed')
    return basis, pivots


def _clebsch_pattern_count(spec):
    """Integer constraint backtracking, fixing one image by Cayley translation."""
    n = spec['vertices']
    edges = {tuple(e) for e in spec['edges']}
    nonedges = {tuple(e) for e in spec['nonedges']}
    if set(range(n)) != {v for e in edges for v in e}:
        raise StoredArtifactMismatch(f"pattern {spec['name']}: an isolated required-edge vertex needs weighted-model handling")
    adj = [sum(1 << (u ^ g) for g in GENERATORS) for u in range(16)]
    relation = [[0] * n for _ in range(n)]
    for u, v in edges:
        relation[u][v] = relation[v][u] = 1
    for u, v in nonedges:
        relation[u][v] = relation[v][u] = -1
    degrees = [sum(value == 1 for value in row) for row in relation]
    order = [max(range(n), key=lambda u: (degrees[u], -u))]
    while len(order) < n:
        remaining = set(range(n)) - set(order)
        order.append(max(remaining, key=lambda u: (sum(relation[u][v] == 1 for v in order),
                                                    sum(relation[u][v] != 0 for v in order), degrees[u], -u)))
    images = [-1] * n
    images[order[0]] = 0

    def recurse(depth):
        if depth == n:
            return 1
        u = order[depth]
        candidates = (1 << 16) - 1
        for v in order[:depth]:
            if relation[u][v] == 1:
                candidates &= adj[images[v]]
            elif relation[u][v] == -1:
                candidates &= ((1 << 16) - 1) ^ adj[images[v]]
        total = 0
        while candidates:
            bit = candidates & -candidates
            candidates -= bit
            images[u] = bit.bit_length() - 1
            total += recurse(depth + 1)
        return total
    return 16 * recurse(1)


def verify_structural_views(data_dir):
    """Check all published atlas/flag/pattern views after the primitive recount."""
    _guard()
    data = Path(data_dir)
    with np.load(data / 'flag_basis.npz', allow_pickle=False) as archive:
        f = {key: archive[key] for key in archive.files}
    with np.load(data / 'pattern_columns.npz', allow_pickle=False) as archive:
        p = {key: archive[key] for key in archive.files}
    meta = _load_json(data / 'pattern_columns.json')
    from proof_specification import verify_specification
    try:
        specification = verify_specification(meta, p, f)
    except (AssertionError, KeyError, TypeError, ValueError) as exc:
        raise StoredArtifactMismatch(f'pattern_columns.json / NPZ mathematical specification: {exc}') from exc
    files = {}
    host_masks = _integer_array(f, 'host_masks', (1044,), 'flag_basis.npz')
    hosts = [int(value) for value in host_masks]
    if hosts != sorted(set(hosts)) or hosts[0] != 0 or hosts[-1] != (1 << 21) - 1:
        raise StoredArtifactMismatch('flag_basis.npz.host_masks: invalid canonical host order')
    _array_equal(_integer_array(p, 'host_masks', (1044,), 'pattern_columns.npz'), host_masks, 'pattern_columns.npz.host_masks')
    aut = _integer_array(f, 'host_automorphism_orders', (1044,), 'flag_basis.npz')
    if any(a <= 0 or 5040 % int(a) for a in aut):
        raise StoredArtifactMismatch('flag_basis.npz.host_automorphism_orders: invalid group order')
    orbits = [5040 // int(a) for a in aut]
    _array_equal(_integer_array(f, 'host_orbit_sizes', (1044,), 'flag_basis.npz'), orbits, 'flag_basis.npz.host_orbit_sizes')
    if sum(orbits) != 1 << 21:
        raise StoredArtifactMismatch('flag_basis.npz.host_orbit_sizes: incomplete labeled-graph coverage')
    for e in range(22):
        _same(sum(size for mask, size in zip(hosts, orbits) if mask.bit_count() == e), comb(21, e), f'atlas edge layer {e}')
    try:
        text_masks = [int(value) for value in (data / 'host_masks.txt').read_text().split()]
    except ValueError as exc:
        raise StoredArtifactMismatch(f'host_masks.txt: {exc}') from exc
    _same(text_masks, hosts, 'host_masks.txt')
    files['host_masks.txt'] = _record(data, 'host_masks.txt', masks_checked=len(hosts))
    atlas = {
        'schema': 'induced-pentagons.graph-atlas.v1', 'order': 7,
        'mask_convention': MASK_CONVENTION,
        'canonicalization': 'minimum over all 7! vertex permutations',
        'host_count': 1044, 'labelled_graph_count': 1 << 21,
        'hosts': [{'index': i, 'mask': mask, 'edges': _edges(mask, 7),
                   'edge_count': mask.bit_count(), 'automorphism_order': int(aut[i]),
                   'orbit_size': orbits[i]} for i, mask in enumerate(hosts)],
    }
    _compare_file(data, 'graph_atlas_7.json', atlas)
    files['graph_atlas_7.json'] = _record(data, 'graph_atlas_7.json', hosts_checked=1044, labelled_graphs_covered=1 << 21)

    spaces = {
        'schema': 'induced-pentagons.flag-spaces.v1',
        'status': 'exact combinatorial inputs; no SOS inequality claimed',
        'equality_model': {'classes': 17, 'active_class_vertices': list(range(16)),
                           'isolated_class_vertex': 16, 'integer_class_weights': [1] * 16 + [32],
                           'total_weight': 48, 'clebsch_xor_generators': list(GENERATORS)},
        'mask_convention': MASK_CONVENTION,
        'flag_canonicalization': 'minimum under extension permutations only', 'blocks': {},
    }
    expected_flag_keys = {'host_masks', 'host_automorphism_orders', 'host_orbit_sizes'}
    block_reports = {}
    for name, roots, order, root_edges, dimension in BLOCKS:
        masks, lookup, flags = _flag_description(roots, order, root_edges, dimension)
        den = factorial(7) // factorial(7 - roots) * comb(7 - roots, order - roots)
        _array_equal(_integer_array(f, 'flag_masks_' + name, (dimension,), 'flag_basis.npz'), masks, f'flag_basis.npz.flag_masks_{name}')
        _same(int(_integer_array(f, 'denominator_' + name, (), 'flag_basis.npz')), den, f'flag_basis.npz.denominator_{name}')
        counts = _integer_array(f, 'C_' + name, (1044, dimension, dimension), 'flag_basis.npz')
        if np.any(counts < 0) or not np.array_equal(counts, counts.transpose(0, 2, 1)):
            raise StoredArtifactMismatch(f'flag_basis.npz.C_{name}: negative or asymmetric product counts')
        rows, representatives, compatible = _conditional_rows(roots, order, root_edges, dimension, lookup)
        basis, pivots = _kernel_basis(rows, dimension)
        _array_equal(_integer_array(f, 'Q_' + name, rows.shape, 'flag_basis.npz'), rows, f'flag_basis.npz.Q_{name}')
        _array_equal(_integer_array(f, 'Q_basis_' + name, (len(pivots), dimension), 'flag_basis.npz'), rows[pivots], f'flag_basis.npz.Q_basis_{name}')
        _array_equal(_integer_array(f, 'B_' + name, basis.shape, 'flag_basis.npz'), basis, f'flag_basis.npz.B_{name}')
        spaces['blocks'][name] = {
            'roots': roots, 'flag_order': order, 'root_edges': root_edges,
            'dimension': dimension, 'host_sampling_denominator': den,
            'flags': flags, 'triangle_free_count': sum(flag['triangle_free'] for flag in flags),
            'equality_row_denominator': 48 ** (order - roots),
            'compatible_root_assignments': compatible, 'unique_equality_row_count': len(rows),
            'equality_row_rank': len(pivots), 'kernel_dimension': basis.shape[1],
            'unique_equality_rows': rows.tolist(), 'equality_row_representatives': representatives,
            'independent_equality_row_indices': pivots, 'integer_kernel_basis_columns': basis.T.tolist(),
            'kernel_basis_convention': 'primitive integer columns, first nonzero entry positive',
        }
        expected_flag_keys.update(prefix + name for prefix in ('C_', 'B_', 'Q_', 'Q_basis_', 'flag_masks_', 'denominator_'))
        block_reports[name] = {'flags': dimension, 'compatible_root_tuples_recounted': compatible,
                               'unique_rows_recounted': len(rows), 'kernel_dimension': basis.shape[1]}
    _same(sorted(f), sorted(expected_flag_keys), 'flag_basis.npz.array_names')
    _compare_file(data, 'flag_spaces.json', spaces)
    files['flag_spaces.json'] = _record(data, 'flag_spaces.json', blocks=block_reports)
    files['flag_basis.npz'] = _record(data, 'flag_basis.npz', arrays_bound=len(f), conditional_rows_independently_recounted=True,
                                     primitive_host_product_counts='Independently recounted by verify_combinatorial_inputs before this binding step')

    specs = meta['patterns']
    names = [spec['name'] for spec in specs]
    npats = len(names)
    _same(p['pattern_names'].tolist(), names, 'pattern_columns.npz.pattern_names')
    counts = _integer_array(p, 'pattern_counts', (1044, npats), 'pattern_columns.npz')
    denominators = [factorial(7) // factorial(7 - spec['vertices']) for spec in specs]
    _array_equal(_integer_array(p, 'pattern_denominators', (npats,), 'pattern_columns.npz'), denominators, 'pattern_columns.npz.pattern_denominators')
    hom = [_clebsch_pattern_count(spec) for spec in specs]
    reference = {spec['name']: Fraction(h, 48 ** spec['vertices']) for spec, h in zip(specs, hom)}
    expected_specs = [{key: spec[key] for key in ('name', 'vertices', 'edges', 'nonedges')} |
                      {'denominator': denominators[i], 'injection_counts': counts[:, i].tolist(),
                       'clebsch_homomorphism_count': hom[i], 'clebsch_reference_density': str(reference[spec['name']])}
                      for i, spec in enumerate(specs)]
    column_names = [column['name'] for column in meta['columns']]
    _same(p['column_names'].tolist(), column_names, 'pattern_columns.npz.column_names')
    expected_columns = []
    column_numbers = []
    column_denominators = []
    reference_columns = {}
    for column in meta['columns']:
        terms = {name: Fraction(value) for name, value in column['terms'].items()}
        coefficients = [terms.get(name, Fraction(0)) / den for name, den in zip(names, denominators)]
        den = lcm(*(value.denominator for value in coefficients))
        nums = [sum(int(counts[row, i]) * int(value * den) for i, value in enumerate(coefficients)) for row in range(1044)]
        common = gcd(den, *nums)
        nums = [value // common for value in nums]
        den //= common
        ref = sum(terms.get(name, Fraction(0)) * reference[name] for name in names)
        reference_columns[column['name']] = ref
        expected_columns.append({'name': column['name'], 'terms': {k: str(v) for k, v in terms.items()},
                                 'numerators': nums, 'denominator': den, 'clebsch_reference_value': str(ref)})
        column_numbers.append(nums)
        column_denominators.append(den)
    column_numbers = np.array(column_numbers, dtype=np.int64).T
    column_denominators = np.array(column_denominators, dtype=np.int64)
    _array_equal(_integer_array(p, 'column_numerators', column_numbers.shape, 'pattern_columns.npz'), column_numbers, 'pattern_columns.npz.column_numerators')
    _array_equal(_integer_array(p, 'column_denominators', column_denominators.shape, 'pattern_columns.npz'), column_denominators, 'pattern_columns.npz.column_denominators')
    graph_masks = _integer_array(p, 'fixed_density_graph_masks', (34,), 'pattern_columns.npz')
    induced = _integer_array(p, 'fixed_density_induced_counts', (1044, 34), 'pattern_columns.npz')
    paired = _integer_array(p, 'fixed_density_complement_edge_counts', (1044, 34), 'pattern_columns.npz')
    if np.any(induced < 0) or np.any(paired < 0) or np.any(paired > induced):
        raise StoredArtifactMismatch('pattern_columns.npz.fixed_density_counts: invalid counts')
    _array_equal(induced.sum(axis=1), np.full(1044, 21), 'fixed-density subset totals')
    _array_equal(paired.sum(axis=1), [mask.bit_count() for mask in hosts], 'fixed-density edge totals')
    fixed_nums = 144 * paired - 5 * induced
    fixed_den = 3024
    _array_equal(_integer_array(p, 'fixed_density_numerators', (1044, 34), 'pattern_columns.npz'), fixed_nums, 'pattern_columns.npz.fixed_density_numerators')
    _same(int(_integer_array(p, 'fixed_density_denominator', (), 'pattern_columns.npz')), fixed_den, 'pattern_columns.npz.fixed_density_denominator')
    D = lcm(TAU.denominator, fixed_den, *map(int, column_denominators), 140, 1260)
    _same(int(_integer_array(p, 'common_denominator', (), 'pattern_columns.npz')), D, 'pattern_columns.npz.common_denominator')
    free_names = ['Phi1', 'Phi2', 'Phi3'] + [f'density_{int(mask)}' for mask in graph_masks]
    positive_names = ['PhiTri', 'Ji0', 'Ji1', 'Jdel']
    _same(p['free_names'].tolist(), free_names, 'pattern_columns.npz.free_names')
    _same(p['positive_names'].tolist(), positive_names, 'pattern_columns.npz.positive_names')
    cindex = {name: i for i, name in enumerate(column_names)}
    common_nums = column_numbers * (D // column_denominators)[None, :]
    free_nums = np.column_stack([common_nums[:, cindex[name]] for name in free_names[:3]] + [fixed_nums * (D // fixed_den)])
    positive_nums = np.column_stack([common_nums[:, cindex[name]] for name in positive_names])
    target_nums = int(TAU * D) - common_nums[:, cindex['theta']]
    for key, value in [('free_numerators', free_nums), ('positive_numerators', positive_nums), ('target_numerators', target_nums)]:
        _array_equal(_integer_array(p, key, value.shape, 'pattern_columns.npz'), value, 'pattern_columns.npz.' + key)
    _same(reference_columns['p'], PSTAR, 'reference p')
    _same(reference_columns['theta'], TAU, 'reference theta')
    if any(reference_columns[name] != 0 for name in column_names if name not in ('p', 'theta')):
        raise StoredArtifactMismatch('pattern_columns.json: a reference variational column is nonzero')
    _array_equal(counts[:, names.index('R0')] + counts[:, names.index('R1')], counts[:, names.index('Ddel')], 'R0+R1=Ddel')
    pychecks = [{'row': row, 'mask': hosts[row], 'patterns_checked': npats} for row in (0, 522, 1043)]
    expected_meta = {
        'schema': 'pentagon-pattern-columns-v1', 'status': 'exact_pattern_data; not a proof certificate',
        'source': 'Manuscript Sections 2.2, 2.3 and 4.1--4.2',
        'normalization': {'pstar': str(PSTAR), 'tau': str(TAU), 'kappa': str(KAPPA),
                          'pattern_density': 'injection_count/(7)_r', 'all_columns_common_denominator': D,
                          'common_denominator_also_clears_flag_140_and_1260': True},
        'host_order': {'count': 1044, 'mask_pairs': list(combinations(range(7), 2)), 'masks': hosts,
                       'host_masks_sha256': sha256((data / 'host_masks.txt').read_bytes()).hexdigest()},
        'patterns': expected_specs, 'columns': expected_columns,
        'fixed_density': {'description': 'p_F*t(K2)-pstar*p_F; five-set and complementary pair disjoint',
                           'graphs': [{'mask': int(mask), 'edges': _edges(mask, 5)} for mask in graph_masks],
                           'induced_counts': induced.tolist(), 'complement_edge_counts': paired.tolist(),
                           'subset_denominator': 21, 'column_denominator': fixed_den, 'column_numerators': fixed_nums.tolist(),
                           'basis_note': "34 five-graph density identities; their sum is p-pstar."},
        'checks': {'host_count': True, 'complete_and_empty_hosts': True, 'subset_count_21': True,
                    'paired_counts_sum_to_host_edges': True, 'R0_plus_R1_equals_Ddel': True,
                    'all_reference_variational_columns_zero': True, 'independent_python_crosscheck': pychecks},
    }
    _same(meta, _plain(expected_meta), 'pattern_columns.json')
    files['pattern_columns.json'] = _record(data, 'pattern_columns.json', hosts=1044, primitive_patterns=npats,
                                           exact_rational_columns=len(column_names), fixed_density_columns=34,
                                           reference_homomorphism_counts_independently_recounted=npats)
    lines = (data / 'pattern_counts.tsv').read_text().splitlines()
    _same(len(lines), 1046, 'pattern_counts.tsv.line_count')
    try:
        _same([int(x) for x in lines[0].split()], [1044, npats], 'pattern_counts.tsv.header')
        rows = [[int(x) for x in line.split()] for line in lines[1:1045]]
        expected_rows = np.column_stack([host_masks, counts, induced, paired]).tolist()
        _same(rows, expected_rows, 'pattern_counts.tsv.host_rows')
        final = lines[-1].split()
        _same(final[0], 'CLEBSCH', 'pattern_counts.tsv.final_marker')
        _same([int(x) for x in final[1:]], hom, 'pattern_counts.tsv.CLEBSCH')
    except (ValueError, IndexError) as exc:
        if isinstance(exc, StoredArtifactMismatch):
            raise
        raise StoredArtifactMismatch(f'pattern_counts.tsv: {exc}') from exc
    files['pattern_counts.tsv'] = _record(data, 'pattern_counts.tsv', host_rows=1044, integer_columns_per_host=1 + npats + 68,
                                         reference_counts=len(hom))
    validation = {
        'status': 'passed', 'host_rows': 1044, 'patterns': npats, 'free_columns': 37,
        'nonnegative_variational_columns': 4, 'reference_p': str(PSTAR), 'reference_theta': str(TAU),
        'independent_python_checks': pychecks,
        'missing': 'Positive flag-square certificate coefficients and span witnesses remain separate inputs.',
    }
    _compare_file(data, 'pattern_columns_validation.json', validation)
    files['pattern_columns_validation.json'] = _record(data, 'pattern_columns_validation.json', fields_checked=len(validation))

    # Exact float-cache consistency, not approximate mathematical verification.
    columns_float = column_numbers / column_denominators[None, :]
    fixed_float = fixed_nums / fixed_den
    float_views = {
        'columns': columns_float, 'fixed_density': fixed_float,
        'free_columns': np.column_stack([columns_float[:, cindex[name]] for name in free_names[:3]] + [fixed_float]),
        'positive_columns': np.column_stack([columns_float[:, cindex[name]] for name in positive_names]),
        'theta': columns_float[:, cindex['theta']], 'p': columns_float[:, cindex['p']],
        'target': float(TAU) - columns_float[:, cindex['theta']],
        'pstar': np.array(float(PSTAR)), 'tau': np.array(float(TAU)),
    }
    for key, value in float_views.items():
        if key not in p or p[key].dtype != np.dtype('float64'):
            raise StoredArtifactMismatch(f'pattern_columns.npz.{key}: expected a float64 discovery cache')
        _array_equal(p[key], value, 'pattern_columns.npz.' + key)
    expected_pattern_keys = {
        'host_masks', 'pattern_names', 'pattern_counts', 'pattern_denominators',
        'column_names', 'column_numerators', 'column_denominators', 'fixed_density_numerators',
        'fixed_density_denominator', 'fixed_density_graph_masks', 'fixed_density_induced_counts',
        'fixed_density_complement_edge_counts', 'free_names', 'positive_names', 'common_denominator',
        'free_numerators', 'positive_numerators', 'target_numerators', *float_views,
    }
    _same(sorted(p), sorted(expected_pattern_keys), 'pattern_columns.npz.array_names')
    files['pattern_columns.npz'] = _record(data, 'pattern_columns.npz', arrays_bound=len(p),
                                          rational_columns_checked=len(column_names), redundant_float_caches_checked=len(float_views),
                                          primitive_counts='Independently recounted by verify_combinatorial_inputs before this binding step')
    return {'status': 'PASS', 'scope': 'Published structural views bound to independently recounted integer arrays; conditional equality rows independently evaluated here',
            'mathematical_specification': specification, 'files': files}


def verify_finite_views(data_dir, finite_result, profile_result, offset_result):
    """Bind every published finite/profile/offset field to fresh caller results."""
    _guard()
    from clebsch_core import ADJ, CYCLES, EDGES, GENERATORS as CORE_GENERATORS, PATHS, all_profile_counts
    data = Path(data_dir)
    files = {}
    _same(finite_result['status'], 'PASS', 'fresh finite result status')
    _same(profile_result['status'], 'PASS', 'fresh profile result status')
    _same(offset_result['status'], 'PASS', 'fresh offset result status')
    _compare_file(data, 'finite_checks.json', finite_result)
    files['finite_checks.json'] = _record(data, 'finite_checks.json', all_fields_compared=True, hessian_entries=256)
    _compare_file(data, 'profile_checks.json', profile_result)
    files['profile_checks.json'] = _record(data, 'profile_checks.json', all_fields_compared=True, profiles=65536)
    graph = {
        'schema_version': 1, 'labeling': 'integers 0..15 represent F_2^4 bit vectors',
        'generators': CORE_GENERATORS, 'edges': EDGES, 'neighborhood_masks': ADJ,
        'induced_C5_vertex_subsets': CYCLES, 'induced_P4_records': PATHS,
        'P4_record_order': 'endpoint1, endpoint2, internal1, internal2',
    }
    _compare_file(data, 'clebsch_graph.json', graph)
    files['clebsch_graph.json'] = _record(data, 'clebsch_graph.json', explicit_edges=40, explicit_cycles=192,
                                         explicit_paths=480, all_fields_compared=True)
    counts = all_profile_counts()
    _same(sha256(bytes(counts)).hexdigest(), profile_result['counts_sha256'], 'fresh profile counts digest')
    envelope = {
        'schema_version': 1, 'mask_convention': 'bit i means vertex i belongs to the new-vertex neighborhood',
        'counts_by_mask': counts,
        'definition': 'Number of induced P4 subsets whose endpoints are in the neighborhood and whose internal vertices are outside it',
        'verification': 'verify_profiles.py independently scans all paths for every mask',
    }
    _compare_file(data, 'profile_envelope.json', envelope)
    files['profile_envelope.json'] = _record(data, 'profile_envelope.json', exact_counts_compared=len(counts), all_fields_compared=True)
    if set(offset_result['offsets']) != {'-2', '-1', '0', '1', '2'}:
        raise StoredArtifactMismatch('fresh offset result: complete small-offset family is required')
    for offset, record in offset_result['offsets'].items():
        if len(record.get('presentations', [])) != record['candidate_presentations_checked']:
            raise StoredArtifactMismatch(f'fresh offset result.offsets.{offset}: complete presentations are required')
    if offset_result.get('actual_graph_checks') != 26:
        raise StoredArtifactMismatch('fresh offset result: all 26 actual-graph checks are required')
    _compare_file(data, 'eventual_polynomials_small_offsets.json', offset_result)
    files['eventual_polynomials_small_offsets.json'] = _record(
        data, 'eventual_polynomials_small_offsets.json', all_fields_compared=True,
        presentations=sum(len(record['presentations']) for record in offset_result['offsets'].values()),
        offset_polynomial_records=sum(len(record['polynomials']) for record in offset_result['offsets'].values()),
        actual_graph_checks=offset_result['actual_graph_checks'])
    return {'status': 'PASS', 'scope': 'Every stored finite/profile/offset field compared with independently checked fresh results', 'files': files}


def verify(data_dir, finite_result, profile_result, offset_result):
    _guard()
    structural = verify_structural_views(data_dir)
    finite = verify_finite_views(data_dir, finite_result, profile_result, offset_result)
    files = {**structural['files'], **finite['files']}
    return {'status': 'PASS', 'scope': 'All published core data views bound to their checked mathematical objects; not a formalization of analytic proofs',
            'files_checked': len(files), 'files': files, 'ignored_json_fields': []}


if __name__ == '__main__':
    _guard()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data-dir', type=Path, default=ROOT / 'certificates')
    parser.add_argument('--structural-only', action='store_true', help='Check structural views; full independent primitive recount remains a separate prerequisite')
    args = parser.parse_args()
    if not args.structural_only:
        parser.error('Use verify(data_dir, finite_result, profile_result, offset_result) from verify_project.py for the full gate, or --structural-only.')
    print(json.dumps(verify_structural_views(args.data_dir), indent=2))
