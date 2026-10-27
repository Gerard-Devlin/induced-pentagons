#!/usr/bin/env python3
"""Numerical CSDP discovery with all 37 free multipliers eliminated.

This is a conditioning fallback, not a proof verifier. Pivoted row QR selects
37 equations from E*y + M*z = b. Substitution leaves 1011 equations in PSD
blocks and nonnegative variables only. Results are expanded in the
original 1048 equations before the existing numerical parser is used.
All files are separate from the primary CSDP run and exact certificates.
"""
from __future__ import annotations

import _bootstrap  # local CLI module paths only

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

import numpy as np
import scipy.linalg as sla

from search_certificate_csdp import ROOT, TAU, atomic_npz, parse_solution


def original_system():
    p = np.load(ROOT/'certificates/pattern_columns.npz')
    fs = np.maximum(np.max(np.abs(p['free_columns']), axis=0), 1e-15)
    ps = np.maximum(np.max(np.abs(p['positive_columns']), axis=0), 1e-15)
    E = np.zeros((1048, 37))
    E[:1044] = p['free_columns']/fs
    E[1044, 0] = E[1045, 0] = TAU/fs[0]
    E[1046, 2] = TAU/fs[2]
    E[1047, 1:3] = TAU/fs[1:3]
    b = np.r_[p['target']/TAU, -115.699, -1e-5, -1e-5, 310.001]
    # Diagonal variables: 1044 host slacks, four positive multipliers,
    # one relaxation, four bound slacks. No free-variable splitting.
    D = np.zeros((1048, 1053))
    D[:1044, :1044] = np.eye(1044)
    D[:1044, 1044:1048] = p['positive_columns']/ps
    D[:1044, 1048] = -1
    D[1044:, 1049:] = np.diag([-1, 1, 1, -1])
    return p, fs, ps, E, D, b


def export_eliminated(work, triangle=False, trace_penalty=1e-14):
    p, fs, ps, E, D, b = original_system()
    s = np.load(ROOT/'certificates/symmetry_blocks.npz')
    assert np.array_equal(p['host_masks'], s['host_masks'])
    groups = [str(g) for g in s['group_names']
              if triangle or str(s['group_owner_'+str(g)]) != 'triangle3']
    sizes = [s['group_M_'+g].shape[1] for g in groups]
    _, R, piv = sla.qr(E.T, pivoting=True, mode='economic')
    assert np.min(np.abs(np.diag(R[:, :37]))) > 1e-9
    P = np.asarray(piv[:37], dtype=int)
    remaining = np.asarray(sorted(set(range(1048))-set(P)), dtype=int)
    T = sla.solve(E[P].T, E[remaining].T).T
    elimination_error = float(np.max(np.abs(E[remaining]-T@E[P])))
    assert elimination_error < 1e-12
    reduced_rhs = b[remaining]-T@b[P]
    diagonal = D[remaining]-T@D[P]
    reduced = {}
    for g, n in zip(groups, sizes):
        full = np.zeros((1048, n*n))
        full[:1044] = s['group_M_'+g].reshape(1044, n*n)
        reduced[g] = (full[remaining]-T@full[P]).reshape(1011, n, n)
    # Check substitution numerically on arbitrary symmetric block matrices.
    rng = np.random.default_rng(20261027)
    z = rng.normal(size=1053)
    full_contribution = D@z
    reduced_contribution = diagonal@z
    for g, n in zip(groups, sizes):
        X = rng.normal(size=(n, n)); X = (X+X.T)/2
        full_contribution[:1044] += np.einsum('hij,ij->h', s['group_M_'+g], X)
        reduced_contribution += np.einsum('hij,ij->h', reduced[g], X)
    y = sla.solve(E[P], b[P]-full_contribution[P])
    error = np.max(np.abs((E@y+full_contribution-b)[remaining]
                         -(reduced_contribution-reduced_rhs)))
    assert error < 1e-9
    db = len(groups)+1
    dat = work/'pentagon_eliminated.dat-s'
    with dat.open('w') as out:
        out.write('"Numerical discovery with 37 free multipliers eliminated"\n')
        out.write(f'1011\n{db}\n')
        out.write(' '.join(map(str, sizes+[-1053]))+'\n')
        out.write(' '.join(f'{x:.18e}' for x in reduced_rhs)+'\n')
        def emit(k, block, i, j, value):
            if abs(value) > 1e-17:
                out.write(f'{k} {block} {i+1} {j+1} {value:.18e}\n')
        for block, (g, n) in enumerate(zip(groups, sizes), 1):
            for i in range(n):
                emit(0, block, i, i, -trace_penalty*int(s['group_multiplicity_'+g]))
        emit(0, db, 1048, 1048, -1)
        for h in range(1011):
            for block, (g, n) in enumerate(zip(groups, sizes), 1):
                mat = reduced[g][h]
                for i in range(n):
                    for j in range(i, n):
                        emit(h+1, block, i, j, float(mat[i, j]))
            for j in np.flatnonzero(abs(diagonal[h]) > 1e-17):
                emit(h+1, db, int(j), int(j), float(diagonal[h, j]))
    metadata = {
        'status': 'numerical_discovery_input; not a proof',
        'groups': groups, 'sizes': sizes, 'diagonal_block': db,
        'diagonal_size': 1053, 'free_scaling': fs.tolist(),
        'positive_scaling': ps.tolist(), 'triangle': triangle,
        'host_equation_scale': TAU, 'trace_penalty': trace_penalty,
        'free_penalty': 0, 'pivot_rows': P.tolist(),
        'remaining_rows': remaining.tolist(), 'equations': 1011,
        'pivot_condition_number': float(np.linalg.cond(E[P])),
        'elimination_residual_max': elimination_error,
        'random_substitution_check_max': float(error),
        'offsets': {'slacks': 0, 'positive': 1044, 'delta': 1048, 'bounds': 1049}
    }
    (work/'metadata.json').write_text(json.dumps(metadata, indent=2)+'\n')
    atomic_npz(work/'elimination.npz', pivot=P, remaining=remaining, T=T, E=E, rhs=b)
    print(f'Eliminated export: {dat.stat().st_size/1e6:.1f} MB; '
          f'1011 equations; pivot condition {metadata["pivot_condition_number"]:.3g}', flush=True)
    return dat, metadata


def parse_eliminated(work, solution, metadata, output):
    p, fs, ps, E, D, rhs = original_system()
    s = np.load(ROOT/'certificates/symmetry_blocks.npz')
    saved = np.load(work/'elimination.npz')
    P, remaining, T = saved['pivot'], saved['remaining'], saved['T']
    groups, sizes = metadata['groups'], metadata['sizes']
    blocks = [np.zeros((n, n)) for n in sizes]
    diagonal = np.zeros(1053)
    with solution.open() as inp:
        dual = np.array([float(x) for x in next(inp).split()])
        assert len(dual) == 1011
        for line in inp:
            if not line.strip():
                continue
            which, block, i, j, value = line.split()
            if int(which) != 2:
                continue
            block, i, j, value = int(block)-1, int(i)-1, int(j)-1, float(value)
            if block == len(groups):
                assert i == j
                diagonal[i] = value
            else:
                blocks[block][i, j] = blocks[block][j, i] = value
    cone = D@diagonal
    for g, X in zip(groups, blocks):
        cone[:1044] += np.einsum('hij,ij->h', s['group_M_'+g], X)
    free = sla.solve(E[P], rhs[P]-cone[P])
    residual = E@free+cone-rhs
    # Lift the dual through the same row operations. E.T*dual_lift=0.
    dual_lift = np.zeros(1048)
    dual_lift[remaining] = dual
    dual_lift[P] = -T.T@dual
    expanded = np.zeros(1127)
    expanded[:1048] = diagonal[:1048]
    expanded[1048:1085] = np.maximum(free, 0)
    expanded[1085:1122] = np.maximum(-free, 0)
    expanded[1122] = diagonal[1048]
    expanded[1123:] = diagonal[1049:]
    expanded_path = work/'expanded_primal.sol'
    with expanded_path.open('w') as out:
        out.write(' '.join(f'{v:.18e}' for v in dual_lift)+'\n')
        for block, X in enumerate(blocks, 1):
            for i in range(len(X)):
                for j in range(i, len(X)):
                    if X[i, j]:
                        out.write(f'2 {block} {i+1} {j+1} {X[i,j]:.18e}\n')
        for i, value in enumerate(expanded):
            if value:
                out.write(f'2 {len(groups)+1} {i+1} {i+1} {value:.18e}\n')
    original_metadata = dict(metadata, diagonal_size=1127,
                             offsets={'slacks': 0, 'positive': 1044, 'freeplus': 1048,
                                      'freeminus': 1085, 'delta': 1122, 'bounds': 1123})
    report = parse_solution(work, expanded_path, original_metadata, output)
    report.update({
        'free_variables_eliminated': 37,
        'original_scaled_equation_residual_max': float(abs(residual).max()),
        'original_scaled_bound_residual_max': float(abs(residual[1044:]).max()),
        'lifted_dual_free_residual_max': float(abs(E.T@dual_lift).max()),
        'minimum_diagonal_primal': float(diagonal.min()),
        'numerically_feasible_at_1e_7': bool(abs(residual).max() < 1e-7
                                            and diagonal.min() > -1e-8
                                            and all(np.linalg.eigvalsh(X).min() > -1e-8 for X in blocks))
    })
    output.with_suffix('.summary.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2), flush=True)
    return report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--solver', default='/tmp/pentagon_csdp/solver/csdp')
    ap.add_argument('--triangle', action='store_true')
    ap.add_argument('--trace-penalty', type=float, default=1e-14)
    ap.add_argument('--max-iter', type=int, default=150)
    ap.add_argument('--threads', type=int, default=2)
    ap.add_argument('--export-only', action='store_true')
    ap.add_argument('--parse-only', action='store_true')
    ap.add_argument('--work-dir', type=Path, default=ROOT/'results/csdp_eliminated')
    ap.add_argument('--output', type=Path, default=ROOT/'results/sdp_csdp_eliminated_solution.npz')
    args = ap.parse_args()
    work = args.work_dir.resolve(); work.mkdir(parents=True, exist_ok=True)
    sol = work/'pentagon_eliminated.sol'
    if args.parse_only:
        parse_eliminated(work, sol, json.loads((work/'metadata.json').read_text()), args.output)
        return
    dat, metadata = export_eliminated(work, args.triangle, args.trace_penalty)
    if args.export_only:
        return
    (work/'param.csdp').write_text(
        f'axtol=1e-9\natytol=1e-9\nobjtol=1e-10\nmaxiter={args.max_iter}\n'
        'printlevel=1\nperturbobj=0\n')
    env = os.environ.copy()
    env['OMP_NUM_THREADS'] = env['OPENBLAS_NUM_THREADS'] = str(args.threads)
    command = [args.solver, str(dat), str(sol)]
    if shutil.which('stdbuf'):
        command = ['stdbuf', '-oL']+command
    start = time.time()
    result = subprocess.run(command, cwd=work, env=env)
    print(f'CSDP exit {result.returncode}; elapsed {time.time()-start:.1f}s', flush=True)
    if not sol.exists():
        raise SystemExit('CSDP did not write a numerical solution.')
    parse_eliminated(work, sol, metadata, args.output)


if __name__ == '__main__':
    main()
