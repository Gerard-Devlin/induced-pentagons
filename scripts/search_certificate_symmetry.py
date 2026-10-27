#!/usr/bin/env python3
"""Numerical discovery with root-symmetry compressed flag-algebra PSD blocks.

Uses exactly the target, column normalization, and slope constraints of
search_certificate.py. A numerical solution is NOT an exact certificate.
The output is atomically replaced only after all saved arrays can be reloaded.
Original-owner QR U/X matrices are supplied for the exact rationalizer.
"""
from __future__ import annotations

import _bootstrap  # local CLI module paths only

import argparse
import io
import json
import os
from pathlib import Path
import tempfile
import time

import cvxpy as cp
import numpy as np
import scipy.sparse as sp
import scipy.linalg as la


ROOT = Path(__file__).resolve().parents[1]


def atomic_npz(path: Path, arrays: dict[str, np.ndarray]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    buffer = io.BytesIO()
    np.savez_compressed(buffer, **arrays)
    payload = buffer.getvalue()
    with tempfile.NamedTemporaryFile(prefix=path.stem + '.', suffix='.tmp.npz',
                                     dir=path.parent, delete=False) as stream:
        temporary = Path(stream.name)
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())
    try:
        with np.load(temporary, allow_pickle=False) as check:
            if set(check.files) != set(arrays):
                raise AssertionError('Atomic NPZ key mismatch')
            for key, value in arrays.items():
                if not np.array_equal(check[key], np.asarray(value)):
                    raise AssertionError(('Atomic NPZ reload mismatch', key))
        os.replace(temporary, path)
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise


def atomic_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(prefix=path.stem + '.', suffix='.tmp',
                                     dir=path.parent, mode='w',
                                     encoding='utf-8', delete=False) as stream:
        temporary = Path(stream.name)
        json.dump(value, stream, indent=2, allow_nan=False)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


def run(solver: str = 'CLARABEL', triangle: bool = False, max_iter: int = 100,
        relax: bool = True, direct_method: str = 'qdldl', time_limit: float = 300.0,
        warm_start: bool = False, output: Path | None = None,
        enforce_support: bool = False, trace_weight: float = 1e-9,
        feasibility_only: bool = False) -> dict:
    output = output or ROOT / 'results/sdp_solution.npz'
    start = time.monotonic()
    f = np.load(ROOT / 'certificates/flag_basis.npz', allow_pickle=False)
    s = np.load(ROOT / 'certificates/symmetry_blocks.npz', allow_pickle=False)
    p = np.load(ROOT / 'certificates/pattern_columns.npz', allow_pickle=False)
    if not (np.array_equal(f['host_masks'], p['host_masks'])
            and np.array_equal(s['host_masks'], p['host_masks'])):
        raise AssertionError('Host ordering mismatch')
    owners = ['one_root', 'independent3', 'edge_isolate', 'path3']
    if triangle:
        owners.append('triangle3')
    groups = [str(g) for g, owner in zip(s['group_names'], s['group_owners'])
              if str(owner) in owners]
    free, pos, target = p['free_columns'], p['positive_columns'], p['target']
    fs = np.maximum(np.max(np.abs(free), axis=0), 1e-15)
    ps = np.maximum(np.max(np.abs(pos), axis=0), 1e-15)
    lf = cp.Variable(37, name='scaled_free')
    ap = cp.Variable(4, nonneg=True, name='scaled_positive')
    terms = [(free / fs) @ lf, (pos / ps) @ ap]
    constraints = [lf[0] >= -115.699 * fs[0], lf[0] <= -1e-5 * fs[0],
                   lf[2] <= -1e-5 * fs[2],
                   lf[1] / fs[1] + lf[2] / fs[2] >= 310.001]
    variables, traces = {}, []
    embeddings = {}
    group_owners = {}
    numerical_blocks = {}
    data = {}
    for group in groups:
        copies = s['group_U_' + group]
        raw = s['group_M_' + group]
        multiplicity = int(s['group_multiplicity_' + group])
        owner = str(s['group_owner_' + group])
        rank = raw.shape[1]
        x = cp.Variable((rank, rank), symmetric=True, name=group)
        constraints.append(x >> 0)
        flat = raw.transpose(0, 2, 1).reshape(len(target), rank * rank).copy()
        flat[np.abs(flat) < 1e-16] = 0
        terms.append(sp.csr_matrix(flat) @ cp.reshape(x, (rank * rank,), order='F'))
        traces.append(multiplicity * cp.trace(x))
        variables[group], embeddings[group], group_owners[group] = x, copies, owner
        numerical_blocks[group] = raw
        print('PSD group', group, 'rank', rank, 'copies', multiplicity,
              'nnz', np.count_nonzero(flat), flush=True)
    delta = cp.Variable(nonneg=True, name='relaxation') if relax else 0
    expr = sum(terms)
    supported = np.array([], dtype=np.int32)
    support_rank_report = None
    if enforce_support:
        support = json.loads((ROOT / 'certificates/equality_host_support.json').read_text())
        supported = np.array(support['supported_host_indices'], dtype=np.int32)
        if len(supported) != support['supported_host_count']:
            raise AssertionError('Equality support count metadata mismatch')
        for i in supported:
            record = support['hosts'][int(i)]
            if (not record['supported'] or record['host_index'] != int(i)
                    or record['host_mask'] != int(f['host_masks'][i])):
                raise AssertionError(('Equality support host mismatch', int(i)))
        outside = np.setdiff1d(np.arange(len(target)), supported)
        # Host equations have an exact weighted-average dependence at the
        # equality graphon. Remove dependent rows for numerical conditioning;
        # every omitted row is independently checked after the solve.
        operator_parts = [free[supported] / fs, pos[supported] / ps]
        for group in groups:
            matrix = numerical_blocks[group][supported]
            i, j = np.triu_indices(matrix.shape[1])
            part = matrix[:, i, j].copy()
            part[:, i != j] *= 2
            operator_parts.append(part)
        operator = np.column_stack(operator_parts)
        column_scale = np.maximum(np.max(np.abs(operator), axis=0), 1e-15)
        normalized_operator = operator / column_scale
        singular_values = la.svdvals(normalized_operator)
        rank_tolerance = 1e-10
        equality_rank = int(np.count_nonzero(singular_values > rank_tolerance))
        _, _, pivots = la.qr(normalized_operator.T, mode='economic', pivoting=True)
        keep = np.sort(pivots[:equality_rank])
        row_coefficients, _, _, _ = np.linalg.lstsq(
            normalized_operator[keep].T, normalized_operator.T, rcond=None)
        row_error = float(np.max(np.abs(
            normalized_operator[keep].T @ row_coefficients - normalized_operator.T)))
        affine_error = float(np.max(np.abs(target[supported[keep]] @ row_coefficients
                                           - target[supported])))
        if row_error > 1e-10 or affine_error > 1e-10:
            raise AssertionError(('Dependent support row check failed', row_error, affine_error))
        support_rank_report = {
            'discovery_only': True, 'total_supported_hosts': len(supported),
            'operator_rank': equality_rank, 'rank_tolerance': rank_tolerance,
            'kept_host_indices': supported[keep].tolist(),
            'omitted_host_indices': np.delete(supported, keep).tolist(),
            'singular_values': singular_values.tolist(),
            'dependent_operator_reconstruction_error': row_error,
            'dependent_target_reconstruction_error': affine_error,
            'note': 'All original supported host rows are checked after solving.',
        }
        atomic_json(ROOT / 'results/sdp_support_rank.json', support_rank_report)
        constraints.append(expr[supported[keep]] == target[supported[keep]])
        constraints.append(expr[outside] <= target[outside] + delta)
        print('Equality support', len(supported), 'hosts; independent rows', equality_rank,
              '; inequalities on', len(outside), 'row reconstruction error', row_error, flush=True)
    else:
        constraints.append(expr <= target + delta)
    objective = (cp.Minimize(delta + trace_weight * sum(traces)) if relax else
                 cp.Minimize(0) if feasibility_only else cp.Minimize(sum(traces)))
    problem = cp.Problem(objective, constraints)

    if warm_start and output.exists():
        with np.load(output, allow_pickle=False) as previous:
            lf.value = previous['lambda_free'] * fs
            ap.value = np.maximum(previous['a_positive'], 0) * ps
            if relax:
                delta.value = max(float(previous['delta']), 0)
            for group, x in variables.items():
                owner = group_owners[group]
                if 'U_' + owner not in previous.files:
                    continue
                full = previous['U_' + owner] @ previous['X_' + owner] @ previous['U_' + owner].T
                copies = embeddings[group]
                candidate = sum(v.T @ full @ v for v in copies) / len(copies)
                values, vectors = np.linalg.eigh((candidate + candidate.T) / 2)
                x.value = (vectors * np.maximum(values, 0)) @ vectors.T
        print('Loaded numerical warm start from', output, flush=True)

    if solver == 'CLARABEL':
        options = dict(max_iter=max_iter, tol_gap_abs=1e-10, tol_feas=1e-10,
                       tol_gap_rel=1e-10, verbose=True, max_threads=1,
                       direct_solve_method=direct_method, time_limit=time_limit)
    else:
        options = dict(max_iters=max_iter, eps=2e-8, verbose=True, normalize=True,
                       acceleration_lookback=10, time_limit_secs=time_limit)
    exception = None
    print('Starting', solver, 'groups', len(groups), 'canonicalization elapsed',
          time.monotonic() - start, flush=True)
    try:
        problem.solve(solver=solver, warm_start=warm_start, **options)
    except Exception as exc:
        exception = repr(exc)
        print('Solver exception:', exception, flush=True)

    result = {
        'solver': solver, 'direct_method': direct_method if solver == 'CLARABEL' else None,
        'status': problem.status,
        'objective': float(problem.value) if problem.value is not None and np.isfinite(problem.value) else None,
        'elapsed_seconds': time.monotonic() - start,
        'numerical_discovery_only': True, 'exact_certificate_verified': False,
        'triangle_block': triangle, 'blocks': owners, 'compressed_groups': groups,
        'max_iter_requested': max_iter, 'time_limit_seconds': time_limit,
        'solver_exception': exception, 'solution_saved': False,
        'exact_support_equalities': enforce_support,
        'supported_host_count': len(supported),
        'trace_weight': trace_weight if relax else (0 if feasibility_only else 1),
        'support_rank_reduction': support_rank_report,
    }
    all_available = (lf.value is not None and ap.value is not None
                     and all(x.value is not None for x in variables.values())
                     and (not relax or delta.value is not None))
    if all_available:
        lambdas = np.asarray(lf.value / fs)
        positives = np.asarray(ap.value / ps)
        relaxation = float(delta.value) if relax else 0.0
        full_grams = {owner: np.zeros((f['B_' + owner].shape[0],) * 2)
                      for owner in owners}
        for group, x in variables.items():
            value = (np.asarray(x.value) + np.asarray(x.value).T) / 2
            data['X_group_' + group] = value
            for v in embeddings[group]:
                full_grams[group_owners[group]] += v @ value @ v.T
        expanded = free @ lambdas + pos @ positives
        min_eigenvalues = {}
        for owner in owners:
            u, r = np.linalg.qr(f['B_' + owner].astype(float), mode='reduced')
            gram = full_grams[owner]
            x = u.T @ gram @ u
            x = (x + x.T) / 2
            data['U_' + owner], data['R_' + owner], data['X_' + owner] = u, r, x
            raw = f['C_' + owner].astype(float) / int(f['denominator_' + owner])
            expanded += np.einsum('hab,ab->h', raw, u @ x @ u.T, optimize=True)
            min_eigenvalues[owner] = float(np.linalg.eigvalsh(x)[0])
        actual_slacks = target - expanded
        discovery_slacks = actual_slacks + relaxation
        group_expr = np.asarray(expr.value)
        roundtrip_error = float(np.max(np.abs(expanded - group_expr)))
        data.update(lambda_free=lambdas, a_positive=positives,
                    delta=np.array(relaxation), slacks=discovery_slacks,
                    slacks_without_relaxation=actual_slacks,
                    block_names=np.array(owners), compressed_group_names=np.array(groups),
                    host_masks=f['host_masks'], target=target)
        for key, value in data.items():
            array = np.asarray(value)
            if array.dtype.kind in 'fc' and not np.all(np.isfinite(array)):
                raise AssertionError(('Nonfinite solver output', key))
        result.update(
            delta=relaxation, slack_min=float(discovery_slacks.min()),
            unrelaxed_slack_min=float(actual_slacks.min()),
            lambda_first3=lambdas[:3].tolist(), a_positive=positives.tolist(),
            block_min_eigenvalues=min_eigenvalues,
            original_owner_reconstruction_error=roundtrip_error,
            positive_slack_hosts_above_1e_8=int(np.count_nonzero(actual_slacks > 1e-8)),
            supported_host_residual_max=(float(np.max(np.abs(actual_slacks[supported])))
                                         if len(supported) else None),
        )
        result['numerically_feasible_within_1e_8'] = bool(
            relaxation <= 1e-8 and min(min_eigenvalues.values()) >= -1e-8
            and actual_slacks.min() >= -1e-8 and positives.min() >= -1e-8
            and roundtrip_error <= 1e-8
            and -115.699 - 1e-8 <= lambdas[0] <= 1e-8
            and lambdas[2] <= 1e-8 and lambdas[1] + lambdas[2] >= 310.001 - 1e-8)
        atomic_npz(output, data)
        result['solution_saved'] = True
        result['solution_path'] = str(output)
    summary = (ROOT / 'results/sdp_symmetry_search_summary.json' if output.name == 'sdp_solution.npz'
               else output.with_name(output.stem + '_summary.json'))
    atomic_json(summary, result)
    print(json.dumps(result, indent=2), flush=True)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--solver', choices=['CLARABEL', 'SCS'], default='CLARABEL')
    parser.add_argument('--triangle', action='store_true')
    parser.add_argument('--max-iter', type=int)
    parser.add_argument('--no-relax', action='store_true')
    parser.add_argument('--direct-method', default='qdldl')
    parser.add_argument('--time-limit', type=float, default=300)
    parser.add_argument('--warm-start', action='store_true')
    parser.add_argument('--out', type=Path)
    parser.add_argument('--enforce-support', action='store_true',
                        help='Use only the explicit realizable host indices in equality_host_support.json')
    parser.add_argument('--trace-weight', type=float, default=1e-9)
    parser.add_argument('--feasibility-only', action='store_true',
                        help='With --no-relax, use a zero objective rather than minimizing trace')
    args = parser.parse_args()
    run(args.solver, args.triangle,
        args.max_iter if args.max_iter is not None else (100 if args.solver == 'CLARABEL' else 20000),
        not args.no_relax, args.direct_method, args.time_limit, args.warm_start, args.out,
        args.enforce_support, args.trace_weight, args.feasibility_only)
