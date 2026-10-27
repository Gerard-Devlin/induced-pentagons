#!/usr/bin/env python3
"""Block diagonalize equality-kernel flag SDPs by root-type automorphisms.

The permutation actions and host-matrix invariance are checked with exact
integers. Orthonormal bases/reduced matrices are floating point and are for
certificate DISCOVERY ONLY. The final inequality still needs an exact rational
certificate checker.

For S3, use the trivial and sign isotypic subspaces and split the standard
isotypic space into +/- eigenspaces of a transposition. A 3-cycle provides an
explicit isometric intertwiner between these standard copies. Corresponding
host matrices coincide, so compressed_groups can use one PSD matrix per
standard multiplicity space, with two full-flag embeddings.

There is no loss of feasible host coefficient vectors: Reynolds averaging a
PSD Gram matrix over the root automorphism group preserves PSD, its equality
kernel support, and every host coefficient. Schur's lemma gives the compressed
parameterization. Even without merging equivalent standard copies, all
off-diagonal host blocks vanish, so separate PSDs on subspaces are sufficient.
"""
from __future__ import annotations

import _bootstrap  # local CLI module paths only

import argparse
import itertools
import json
from pathlib import Path

import numpy as np


ORIGINAL_BLOCKS = (
    ('one_root', 1, 4),
    ('independent3', 3, 5),
    ('edge_isolate', 3, 5),
    ('path3', 3, 5),
    ('triangle3', 3, 5),
)


def parity(permutation: tuple[int, ...]) -> int:
    return -1 if sum(permutation[i] > permutation[j]
                     for i in range(len(permutation))
                     for j in range(i + 1, len(permutation))) % 2 else 1


def relabel(mask: int, permutation: tuple[int, ...]) -> int:
    pairs = tuple(itertools.combinations(range(len(permutation)), 2))
    lookup = {pair: bit for bit, pair in enumerate(pairs)}
    result = 0
    for bit, (u, v) in enumerate(pairs):
        if mask >> bit & 1:
            a, b = sorted((permutation[u], permutation[v]))
            result |= 1 << lookup[a, b]
    return result


def flag_action(masks: np.ndarray, roots: int, order: int,
                root_permutation: tuple[int, ...]) -> np.ndarray:
    """image[i] is the relabeled canonical flag index of source flag i."""
    extension_permutations = tuple(
        tuple(range(roots)) + p
        for p in itertools.permutations(range(roots, order))
    )
    root_map = root_permutation + tuple(range(roots, order))
    index = {int(mask): i for i, mask in enumerate(masks)}
    image = []
    for mask in masks:
        transformed = relabel(int(mask), root_map)
        canonical = min(relabel(transformed, p) for p in extension_permutations)
        if canonical not in index:
            raise AssertionError(('Root map fails to preserve type', root_permutation, canonical))
        image.append(index[canonical])
    if sorted(image) != list(range(len(masks))):
        raise AssertionError('Not a flag permutation')
    return np.array(image, dtype=np.int32)


def permutation_matrix(image: np.ndarray) -> np.ndarray:
    matrix = np.zeros((len(image), len(image)), dtype=np.int64)
    matrix[image, np.arange(len(image))] = 1
    return matrix


def range_basis(matrix: np.ndarray, tolerance: float = 1e-10) -> np.ndarray:
    if matrix.size == 0:
        return np.empty((matrix.shape[0], 0), dtype=float)
    u, singular, _ = np.linalg.svd(matrix, full_matrices=False)
    rank = int(np.count_nonzero(singular > tolerance))
    # Every nonzero projected singular value should be one: its source is an
    # orthonormal invariant subspace and this is an orthogonal projector.
    if rank and np.max(np.abs(singular[:rank] - 1)) > 1e-9:
        raise AssertionError(('Projector has nonunit singular values', singular))
    return u[:, :rank]


def exact_kernel_invariance(q: np.ndarray, b: np.ndarray,
                            image: np.ndarray) -> None:
    if not q.size:
        return
    bound = (int(np.max(np.abs(q))) * int(np.max(np.abs(b))) * b.shape[0]
             if b.size else 0)
    dtype = object if bound > np.iinfo(np.int64).max else np.int64
    product = q[:, image].astype(dtype) @ b.astype(dtype)
    if np.any(product != 0):
        raise AssertionError('The equality kernel is not invariant')


def maximum_abs(a: np.ndarray) -> float:
    return float(np.max(np.abs(a))) if a.size else 0.0


def build(input_path: Path, output_path: Path, tolerance: float = 1e-12) -> dict:
    f = np.load(input_path, allow_pickle=False)
    arrays: dict[str, np.ndarray] = {
        'schema': np.array('pentagon-root-symmetry-blocks-v1'),
        'host_masks': f['host_masks'],
        'discovery_only': np.array(True),
    }
    report = {
        'schema': 'pentagon-root-symmetry-validation-v1',
        'status': 'PASS',
        'scope': 'Exact permutation/invariance checks; numeric bases for SDP discovery only',
        'no_loss_argument': (
            'Reynolds averaging preserves PSD, equality-kernel support and every '
            'host coefficient. Inequivalent S3 isotypic blocks are orthogonal '
            'for each host matrix; standard +/- copies are canonically '
            'isometric and have identical host coefficients. Thus both '
            'unmerged and compressed SDP parameterizations lose no feasible '
            'host-coefficient vectors.'
        ),
        'tolerance': tolerance, 'owners': {},
    }
    block_names, owners, group_names, group_owners = [], [], [], []
    group_of_block = []
    total_old_variables = total_new_variables = total_compressed_variables = 0
    rng = np.random.default_rng(937)
    roundtrip_checks = {}

    for owner, roots, order in ORIGINAL_BLOCKS:
        masks = f['flag_masks_' + owner]
        counts = f['C_' + owner]
        denominator = int(f['denominator_' + owner])
        b = f['B_' + owner]
        q = f['Q_' + owner]
        full_dimension, kernel_dimension = b.shape
        u, r_factor = np.linalg.qr(b.astype(float), mode='reduced')
        arrays['original_B_' + owner] = b
        arrays['original_U_' + owner] = u
        root_perms = (
            list(itertools.permutations(range(3)))
            if owner in ('independent3', 'triangle3') else
            [(0, 1, 2), (1, 0, 2)] if owner == 'edge_isolate' else
            [(0, 1, 2), (2, 1, 0)] if owner == 'path3' else [(0,)]
        )
        actions = {}
        for perm in root_perms:
            image = flag_action(masks, roots, order, perm)
            if not np.array_equal(counts[:, image, :][:, :, image], counts):
                raise AssertionError((owner, perm, 'Exact host invariance failed'))
            exact_kernel_invariance(q, b, image)
            actions[perm] = permutation_matrix(image)
            arrays['action_' + owner + '_' + ''.join(map(str, perm))] = image
        identity = np.eye(full_dimension)
        sectors: list[tuple[str, np.ndarray, str]] = []
        standard_pair = None

        if owner in ('independent3', 'triangle3'):
            trivial_projector = sum(actions.values()) / 6.0
            sign_projector = sum(parity(p) * matrix for p, matrix in actions.items()) / 6.0
            standard_projector = identity - trivial_projector - sign_projector
            transposition = actions[(1, 0, 2)].astype(float)
            cycle = actions[(1, 2, 0)].astype(float)
            trivial = range_basis(trivial_projector @ u)
            sign = range_basis(sign_projector @ u)
            plus = range_basis((identity + transposition) @ standard_projector @ u / 2)
            # In the 2D standard representation a 3-cycle is a 120-degree
            # rotation. This maps every + vector to the matching - copy.
            minus = (2 / np.sqrt(3)) * (cycle @ plus + 0.5 * plus)
            if maximum_abs(transposition @ minus + minus) > tolerance:
                raise AssertionError((owner, 'Standard minus is not odd'))
            if maximum_abs(minus.T @ minus - np.eye(minus.shape[1])) > tolerance:
                raise AssertionError((owner, 'Standard-copy intertwiner is not isometric'))
            sectors = [
                ('trivial', trivial, 'trivial'),
                ('sign', sign, 'sign'),
                ('standard_plus', plus, 'standard'),
                ('standard_minus', minus, 'standard'),
            ]
            standard_pair = ('standard_plus', 'standard_minus')
            # These exact projectors are useful to later rationalize symmetry
            # constraints without trusting floating-point SVD bases.
            arrays['projector6_trivial_' + owner] = sum(actions.values())
            arrays['projector6_sign_' + owner] = sum(
                parity(p) * matrix for p, matrix in actions.items())
        elif owner in ('edge_isolate', 'path3'):
            involution = actions[root_perms[1]].astype(float)
            sectors = [
                ('plus', range_basis((identity + involution) @ u / 2), 'plus'),
                ('minus', range_basis((identity - involution) @ u / 2), 'minus'),
            ]
        else:
            sectors = [('trivial', u, 'trivial')]

        sectors = [(name, v, group) for name, v, group in sectors if v.shape[1]]
        all_u = np.column_stack([v for _, v, _ in sectors])
        if all_u.shape != (full_dimension, kernel_dimension):
            raise AssertionError((owner, 'Dimensions do not sum to equality kernel'))
        orthogonal_error = maximum_abs(all_u.T @ all_u - np.eye(kernel_dimension))
        subspace_error = maximum_abs(all_u @ all_u.T - u @ u.T)
        if max(orthogonal_error, subspace_error) > tolerance:
            raise AssertionError((owner, 'Subspace reconstruction error',
                                  orthogonal_error, subspace_error))

        normalized = counts.astype(float) / denominator
        combined = np.einsum('ai,hab,bj->hij', all_u, normalized, all_u, optimize=True)
        cross_error = 0.0
        starts = np.cumsum([0] + [v.shape[1] for _, v, _ in sectors])
        for i, (sector, v, group) in enumerate(sectors):
            name = owner + '__' + sector
            group_name = owner + '__' + group
            block_names.append(name)
            owners.append(owner)
            group_of_block.append(group_name)
            arrays['U_' + name] = v
            arrays['owner_' + name] = np.array(owner)
            arrays['group_' + name] = np.array(group_name)
            arrays['M_' + name] = combined[:, starts[i]:starts[i+1], starts[i]:starts[i+1]]
            # B * coordinates = U. This is a numerical bridge to the exact
            # original kernel coordinates, not a rational certificate.
            # QR triangular solve is substantially more accurate here than
            # generic least squares: the primitive integer columns can have
            # condition number around 10^7, although their QR span is stable.
            coordinates = np.linalg.solve(r_factor, u.T @ v)
            arrays['kernel_coordinates_' + name] = coordinates
            if maximum_abs(b @ coordinates - v) > tolerance:
                raise AssertionError((name, 'Kernel coordinate reconstruction failed'))
            for j in range(i):
                cross_error = max(cross_error, maximum_abs(
                    combined[:, starts[i]:starts[i+1], starts[j]:starts[j+1]]))
            total_new_variables += v.shape[1] * (v.shape[1] + 1) // 2
        if cross_error > tolerance:
            raise AssertionError((owner, 'Host cross terms do not vanish', cross_error))

        standard_identical_error = 0.0
        if standard_pair:
            plus_name, minus_name = (owner + '__' + x for x in standard_pair)
            standard_identical_error = maximum_abs(arrays['M_' + plus_name] - arrays['M_' + minus_name])
            if standard_identical_error > tolerance:
                raise AssertionError((owner, 'Standard-copy matrices differ', standard_identical_error))

        # Optional compressed groups. A variable X for group g contributes
        # sum_c U[g,c] X U[g,c]^T in full flag coordinates. Its host matrix
        # is the sum of the corresponding diagonal M blocks, and trace cost
        # is number_of_copies * trace(X).
        local_groups = list(dict.fromkeys(group for _, _, group in sectors))
        for group in local_groups:
            group_name = owner + '__' + group
            selected = [(sector, v) for sector, v, g in sectors if g == group]
            dims = {v.shape[1] for _, v in selected}
            if len(dims) != 1:
                raise AssertionError(('Unequal equivalent-block dimensions', group_name))
            copies = np.stack([v for _, v in selected])
            matrices = sum(arrays['M_' + owner + '__' + sector] for sector, _ in selected)
            group_names.append(group_name)
            group_owners.append(owner)
            arrays['group_U_' + group_name] = copies
            arrays['group_M_' + group_name] = matrices
            arrays['group_multiplicity_' + group_name] = np.array(len(selected), dtype=np.int32)
            arrays['group_owner_' + group_name] = np.array(owner)
            arrays['group_members_' + group_name] = np.array([owner + '__' + sector for sector, _ in selected])
            rank = copies.shape[-1]
            total_compressed_variables += rank * (rank + 1) // 2

        total_old_variables += kernel_dimension * (kernel_dimension + 1) // 2
        report['owners'][owner] = {
            'full_flag_dimension': full_dimension,
            'kernel_dimension': kernel_dimension,
            'root_automorphism_order': len(actions),
            'exact_host_invariance': 'PASS',
            'exact_equality_kernel_invariance': 'PASS',
            'sectors': {name: int(v.shape[1]) for name, v, _ in sectors},
            'orthonormal_error': orthogonal_error,
            'equality_subspace_error': subspace_error,
            'max_host_cross_block': cross_error,
            'max_standard_copy_matrix_difference': standard_identical_error,
            'compressed_groups': [owner + '__' + group for group in local_groups],
        }
        # Independent end-to-end audit of the advertised NPZ parameterization.
        # This numerical test supplements (and does not replace) exact
        # invariance plus the representation-theoretic no-loss argument.
        random_factor = rng.standard_normal((kernel_dimension, kernel_dimension))
        random_psd = random_factor @ random_factor.T / kernel_dimension
        gram = u @ random_psd @ u.T
        averaged = sum(p @ gram @ p.T for p in actions.values()) / len(actions)
        expanded = np.zeros_like(gram)
        trace_cost = 0.0
        for group in local_groups:
            group_name = owner + '__' + group
            copies = arrays['group_U_' + group_name]
            compressed = sum(v.T @ averaged @ v for v in copies) / len(copies)
            expanded += sum(v @ compressed @ v.T for v in copies)
            trace_cost += len(copies) * np.trace(compressed)
        roundtrip = {
            'host_coefficient_error': maximum_abs(
                np.einsum('hab,ab->h', normalized, gram)
                - np.einsum('hab,ab->h', normalized, averaged)),
            'compressed_gram_error': maximum_abs(expanded - averaged),
            'trace_error': float(abs(np.trace(gram) - trace_cost)),
        }
        if max(roundtrip.values()) > tolerance:
            raise AssertionError((owner, 'Reynolds roundtrip failed', roundtrip))
        roundtrip_checks[owner] = roundtrip
        print(owner, kernel_dimension, '->', report['owners'][owner]['sectors'],
              'max cross', cross_error, flush=True)

    arrays['block_names'] = np.array(block_names)
    arrays['owners'] = np.array(owners)
    arrays['group_of_block'] = np.array(group_of_block)
    arrays['group_names'] = np.array(group_names)
    arrays['group_owners'] = np.array(group_owners)
    arrays['original_block_names'] = np.array([x[0] for x in ORIGINAL_BLOCKS])
    output_path.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(output_path, **arrays)
    report['symmetric_matrix_variable_counts'] = {
        'original_all_five_blocks': total_old_variables,
        'unmerged_symmetry_blocks': total_new_variables,
        'compressed_symmetry_groups': total_compressed_variables,
    }
    report['independent_numeric_reynolds_roundtrip'] = roundtrip_checks
    report['npz_schema'] = {
        'block_names': 'Names of all unmerged PSD subspaces; owners has the corresponding original block.',
        'U_<block>': 'float64 (full_flag_dimension, small_rank) orthonormal embedding.',
        'M_<block>': 'float64 (1044,small_rank,small_rank), already divided by host sampling denominator.',
        'kernel_coordinates_<block>': 'float64 coordinates such that original B times coordinates equals U.',
        'group_names': 'Compressed group names; group_owners gives original block.',
        'group_U_<group>': 'float64 (multiplicity,full_flag_dimension,small_rank); all copies use same PSD variable.',
        'group_M_<group>': 'float64 (1044,small_rank,small_rank), sum of copy M arrays.',
        'group_multiplicity_<group>': 'int32 scalar; trace contribution is multiplicity*trace(X).',
        'group_members_<group>': 'Names of unmerged blocks within this group.',
        'original_B_<owner>': 'Original exact integer kernel basis.',
        'original_U_<owner>': 'Original reduced QR orthonormal kernel basis.',
        'action_<owner>_<perm>': 'Exact integer permutation image[i] of flag i.',
        'projector6_trivial/sign_<owner>': 'Exact integer six times the S3 projector.',
    }
    report_path = output_path.with_name('symmetry_blocks_validation.json')
    report_path.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print('Saved', output_path, flush=True)
    print('Variable counts', report['symmetric_matrix_variable_counts'], flush=True)
    return report


if __name__ == '__main__':
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=root / 'certificates/flag_basis.npz')
    parser.add_argument('--out', type=Path, default=root / 'certificates/symmetry_blocks.npz')
    parser.add_argument('--tolerance', type=float, default=1e-12)
    args = parser.parse_args()
    build(args.input, args.out, args.tolerance)
