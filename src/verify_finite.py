#!/usr/bin/env python3
"""Run exact finite Clebsch checks; the global certificate is verified separately."""
from __future__ import annotations

import _bootstrap  # local CLI module paths only
import argparse, hashlib, json
from fractions import Fraction as F
from itertools import combinations, permutations
from pathlib import Path
from clebsch_core import *


def run() -> dict:
    if not __debug__:raise RuntimeError('Exact finite verification requires assertions enabled.')
    assert len(EDGES) == 40 and len(CYCLES) == 192 and len(PATHS) == 480
    assert all(a.bit_count() == 5 for a in ADJ)
    assert not any(edge(a, b) and edge(a, c) and edge(b, c) for a,b,c in combinations(range(16),3))
    vc = [sum(v in c for c in CYCLES) for v in range(16)]
    assert vc == [60] * 16
    pc = {(u,v):sum(u in c and v in c for c in CYCLES) for u,v in combinations(range(16),2)}
    assert all(n == (24 if edge(u,v) else 12) for (u,v),n in pc.items())
    generated = set()
    for v in range(16):
        for order in permutations(GENERATORS):
            w = v; path = [v]
            for a in order[:-1]:
                w ^= a; path.append(w)
            assert w ^ order[-1] == v
            assert len(set(path)) == 5
            generated.add(tuple(sorted(path)))
    assert generated == set(CYCLES)
    keep = [v for v in range(16) if v not in (0,1)]
    e14 = sum(edge(u,v) for u,v in combinations(keep,2))
    c14 = sum(is_induced_c5(vs,ADJ) for vs in combinations(keep,5))
    assert (e14,c14)==(31,96)
    assert 3125*c14*c14 - e14**5 == 170849
    assert 3125*192**2 * 8 == 9 * 40**5
    hessian=[]
    for u in range(16):
        row=[]
        for v in range(16):
            P2 = 0 if u==v else pc[tuple(sorted((u,v)))]
            E2 = int(edge(u,v))
            value = F(P2,192)-F(3600,192**2)-F(5,2)*(F(E2,40)-F(25,40**2))
            target = F(1-16*int(u==v),256)
            assert value == target
            row.append(str(value))
        hessian.append(row)
    # Independently check A^2=3I-2A+2J and a negative eigenvector.
    for u in range(16):
        for v in range(16):
            assert (ADJ[u]&ADJ[v]).bit_count() == 3*int(u==v)-2*int(edge(u,v))+2
    w=[(-1)**((u&7).bit_count()) for u in range(16)]
    assert sum(w)==0
    assert all(sum(w[v] for v in range(16) if edge(u,v)) == -3*w[u] for u in range(16))
    h=[(((-1)**((u&7).bit_count()))+((-1)**((u&11).bit_count())))//2 for u in range(16)]
    assert sum(h)==0 and sum(v*v for v in h)==8 and edge_quadratic(h)==-12
    return {'status':'PASS','scope':'finite identities only; global theorem NOT certified',
            'vertices':16,'edges':40,'pentagons':192,'induced_P4s':480,
            'independent_generator_enumeration':True,'vertex_counts':vc,
            'hessian_entries_checked':256,'hessian':hessian,
            '14_vertex_example':{'edges':e14,'pentagons':c14,'integer_violation':170849},
            'lambda_minus12_witness':h}


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,default=Path('results/finite_checks.json'))
    args=ap.parse_args(); result=run();args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='hessian'},indent=2))
