#!/usr/bin/env python3
"""Exact independent branch census for Section 14.1 (standard library only).

Derive the counts from the Cayley graph, not from the production candidate
iterator. Independently count four-vertex induced types and all balanced
signed four-point supports, then compare with the complete supplied records.
The stored global proof and polynomial verification have separate gates.
"""

import _bootstrap  # local CLI module paths only
from collections import Counter
from itertools import combinations, combinations_with_replacement
from math import comb
from pathlib import Path
import argparse, hashlib, json

ROOT=Path(__file__).resolve().parents[1]
GEN={1,2,4,8,15}
TYPES=tuple(range(-1,16))

def edge(a,b):
    return a>=0 and b>=0 and (a^b) in GEN

def check(condition,message):
    if not condition: raise ValueError(message)

def verify(data_dir=None):
    if not __debug__: raise RuntimeError('Run this exact census without -O or PYTHONOPTIMIZE.')
    data=Path(data_dir or ROOT/'certificates')
    neighbors={u:{v for v in range(16) if edge(u,v)} for u in range(16)}
    edges=[(u,v) for u,v in combinations(range(16),2) if edge(u,v)]
    check(len(edges)==40 and {len(x) for x in neighbors.values()}=={5},'Clebsch degrees/edges')
    check(all(len(neighbors[u]&neighbors[v])==(0 if edge(u,v) else 2)
              for u,v in combinations(range(16),2)),'Clebsch codegrees')
    for u,v in edges:
        other=set(range(16))-(neighbors[u]|neighbors[v])
        check(len(other)==6 and all(len(neighbors[w]&other)==1 for w in other),
              'Six common nonneighbors do not induce a three-edge matching')
    induced=Counter();signed=Counter();signed_shapes=Counter()
    for four in combinations(range(16),4):
        pairs=[(u,v) for u,v in combinations(four,2) if edge(u,v)]
        deg=sorted(sum(u in e for e in pairs) for u in four)
        shape=('2K2' if deg==[1,1,1,1] else 'P3+K1' if deg==[0,1,1,2] else 'other')
        induced[shape]+=1
        for positive in combinations(four,2):
            h={v:(1 if v in positive else -1) for v in four}
            q=sum(h[u]*h[v] for u,v in pairs)
            signed[q]+=1
            if q in (-2,2): signed_shapes[(q,shape)]+=1
    check(induced['2K2']==40*3//2==60,'Induced 2K2 count')
    p3s=[]
    for center in range(16):
        for leaves in combinations(neighbors[center],2):
            check(not edge(*leaves),'Triangle encountered')
            union=neighbors[center]|neighbors[leaves[0]]|neighbors[leaves[1]]
            check(len(union)==13,'P3 neighborhood union')
            p3s.append((center,leaves))
    check(len(p3s)==160 and induced['P3+K1']==160*3==480,'Induced P3+K1 count')
    check(signed[2]==2*60==120,'Positive signed support count')
    check(signed[-2]==4*60+2*480==1200,'Negative signed support count')
    check(signed_shapes[(2,'2K2')]==120 and signed_shapes[(2,'P3+K1')]==0
          and signed_shapes[(2,'other')]==0,'Positive Q support classification')
    check(signed_shapes[(-2,'2K2')]==240 and signed_shapes[(-2,'P3+K1')]==960
          and signed_shapes[(-2,'other')]==0,'Negative Q support classification')
    allowed_add=[(u,v) for u,v in combinations_with_replacement(TYPES,2)
                 if u==-1 or v==-1 or u==v]
    check(len(allowed_add)==33,'Allowed added-edge types')
    plus_incident=sum(1 for center in TYPES for a,b in combinations_with_replacement(TYPES,2)
                      if (center==-1 or a==-1 or center==a)
                      and (center==-1 or b==-1 or center==b))
    minus_incident=sum(1 for center in TYPES for a,b in combinations_with_replacement(TYPES,2)
                       if edge(center,a) and edge(center,b))
    check(plus_incident==comb(18,2)+16*comb(3,2)==201,'Incident additions')
    check(minus_incident==16*comb(6,2)==240,'Incident deletions')
    expected={
        '-2':{'V=0,T=2':comb(41,2)+minus_incident,'V=2,T=1':80*40,'V=4,T=0':signed[-2]},
        '-1':{'V=0,T=1':40,'V=2,T=0':80},
        '0':{'V=0,T=0':1},
        '1':{'V=0,T=1':33},
        '2':{'V=0,T=2':comb(34,2)+plus_incident,'V=4,T=0':signed[2]},
    }
    supplied=json.loads((data/'eventual_polynomials_small_offsets.json').read_text())
    check(set(supplied['offsets'])==set(expected),'Need all five supplied offsets')
    report={}
    for j,branch in expected.items():
        recorded=supplied['offsets'][j]
        observed=Counter()
        for row in recorded['presentations']:
            d=row['datum'];v=sum(a*a for a in d['h']);t=len(d['toggles'])
            observed[f'V={v},T={t}']+=1
        check(dict(observed)==branch==recorded['branch_counts'],f'Branch mismatch at offset {j}')
        check(sum(branch.values())==recorded['candidate_presentations_checked'],f'Total mismatch at {j}')
        report[j]={'branch_counts':branch,'total':sum(branch.values()),'status':'PASS'}
    check(sum(x['total'] for x in report.values())==6496,'Total census count')
    return {'schema':'induced-pentagons.presentation-census.v1','status':'PASS',
            'convention':'Clebsch types fixed; identify exceptional-vertex relabelings preserving the wrong-pair graph and types; no Clebsch automorphism quotient.',
            'induced_2K2':60,'induced_P3_plus_K1':480,'positive_Q2_supports':120,'negative_Q2_supports':1200,
            'V0_T2_additions':{'incident_isolated_center':153,'incident_active_center':48,'disjoint':561,'total':762},
            'V0_T2_deletions':{'incident':240,'disjoint':820,'total':1060},
            'offsets':report,'total_presentations':6496,
            'scope':'Exact branch cardinalities and record-level agreement; the main gate checks every polynomial and all global certificates separately.',
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=ROOT/'results/presentation_census.json')
    args=ap.parse_args();r=verify();args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()
