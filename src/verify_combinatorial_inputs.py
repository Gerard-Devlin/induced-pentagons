#!/usr/bin/env python3
"""Independent exact recount of ALL seven-host combinatorial inputs.

The production generators enumerate partial injections in C++. This verifier
instead relabels each host by all 7! permutations with NumPy integer arrays,
then counts full relabelings and divides out the unused ordering multiplicity.
It imports no production counting code and never uses floating-point values.
"""

import _bootstrap  # local CLI module paths only
from fractions import Fraction
from itertools import combinations, permutations
from pathlib import Path
import argparse, hashlib, json, math, os, time
import numpy as np

ROOT=Path(__file__).resolve().parents[1]
PAIRS7=list(combinations(range(7),2));BITS7={p:i for i,p in enumerate(PAIRS7)}
BLOCKS=[('one_root',1,4,()),('independent3',3,5,()),
        ('edge_isolate',3,5,((0,1),)),('path3',3,5,((0,1),(1,2))),
        ('triangle3',3,5,((0,1),(0,2),(1,2)))]

def mask_edges(edges):
    return sum(1<<BITS7[tuple(sorted(p))] for p in edges)

def submask(relabelings,vertices):
    out=np.zeros(len(relabelings),dtype=np.uint16)
    for bit,(i,j) in enumerate(combinations(vertices,2)):
        out|=(((relabelings>>BITS7[tuple(sorted((i,j)))])&1)<<bit).astype(np.uint16)
    return out

def canon_table(n,roots):
    pairs=list(combinations(range(n),2));bits={p:i for i,p in enumerate(pairs)}
    values=np.arange(1<<len(pairs),dtype=np.uint16)
    best=values.copy()
    for ext in permutations(range(roots,n)):
        p=tuple(range(roots))+ext;out=np.zeros(len(values),dtype=np.uint16)
        for dst,(i,j) in enumerate(pairs):
            out|=((values>>bits[tuple(sorted((p[i],p[j])))])&1)<<dst
        best=np.minimum(best,out)
    return best

def verify(data):
    if not __debug__:raise RuntimeError('Assertions are disabled; exact verification refuses to run under Python -O.')
    started=time.time()
    with np.load(data/'pattern_columns.npz') as archive:p={k:archive[k] for k in archive.files}
    with np.load(data/'flag_basis.npz') as archive:f={k:archive[k] for k in archive.files}
    meta=json.loads((data/'pattern_columns.json').read_text())
    from proof_specification import verify_specification
    semantic_check=verify_specification(meta,p,f)
    hosts=p['host_masks'];assert np.array_equal(hosts,f['host_masks']) and len(hosts)==1044
    assert hosts.tolist()==sorted(set(hosts.tolist()))
    perm=list(permutations(range(7)))
    maps=np.array([[BITS7[tuple(sorted((v[i],v[j])))] for i,j in PAIRS7] for v in perm],dtype=np.uint32)
    specs=meta['patterns'];assert [s['name'] for s in specs]==p['pattern_names'].tolist()
    prepared=[]
    for name,r,n,re in BLOCKS:
        masks=f['flag_masks_'+name].tolist();ct=canon_table(n,r)
        pairs=list(combinations(range(n),2))
        root_pairs=[(bit,pair) for bit,pair in enumerate(pairs) if pair[1]<r]
        expected_masks=sorted({int(ct[m]) for m in range(1<<len(pairs))
                               if {pair for bit,pair in root_pairs if (m>>bit)&1}==set(re)})
        assert masks==expected_masks,(name,'flag basis differs from declared type')
        index={m:i for i,m in enumerate(masks)}
        lookup=np.array([index.get(int(v),-1) for v in ct],dtype=np.int32)
        prepared.append((name,r,n,mask_edges(re),mask_edges(combinations(range(r),2)),lookup,len(masks)))
    ct5=canon_table(5,0);reps=sorted(set(ct5.tolist()));ix5={m:i for i,m in enumerate(reps)}
    table5=np.array([ix5[int(m)] for m in ct5],dtype=np.int32)
    assert reps==p['fixed_density_graph_masks'].tolist() and len(reps)==34
    atlas_orbits=[]
    for h,H in enumerate(hosts):
        rel=np.zeros(5040,dtype=np.uint32)
        for dst in range(21):rel|=((int(H)>>maps[:,dst])&1)<<dst
        assert int(rel.min())==int(H)
        aut=int(np.count_nonzero(rel==H));assert aut==int(f['host_automorphism_orders'][h])
        atlas_orbits.append(5040//aut)
        for j,s in enumerate(specs):
            e=mask_edges(s['edges']);ne=mask_edges(s['nonedges'])
            total=int(np.count_nonzero(((rel&e)==e)&((rel&ne)==0)))
            mult=math.factorial(7-s['vertices']);assert total%mult==0
            assert total//mult==int(p['pattern_counts'][h,j]),(h,s['name'])
        first5=table5[submask(rel,list(range(5)))];lastedge=(rel>>BITS7[(5,6)])&1
        counts=np.bincount(first5,minlength=34)
        edgecounts=np.bincount(first5[lastedge==1],minlength=34)
        assert np.all(counts%240==0) and np.all(edgecounts%240==0)
        assert np.array_equal(counts//240,p['fixed_density_induced_counts'][h])
        assert np.array_equal(edgecounts//240,p['fixed_density_complement_edge_counts'][h])
        for name,r,n,re,rall,lookup,dim in prepared:
            valid=rel[(rel&rall)==re]
            a=lookup[submask(valid,list(range(n)))]
            b=lookup[submask(valid,list(range(r))+list(range(n,7)))]
            assert np.all(a>=0) and np.all(b>=0)
            counts=np.bincount(a*dim+b,minlength=dim*dim).reshape(dim,dim)
            multiplicity=math.factorial(n-r)**2
            assert np.all(counts%multiplicity==0)
            assert np.array_equal(counts//multiplicity,f['C_'+name][h]),(h,name)
        if (h+1)%200==0:print(f'Independently recounted {h+1}/1044 hosts',flush=True)
    assert sum(atlas_orbits)==2**21
    for e in range(22):
        assert sum(n for H,n in zip(hosts,atlas_orbits) if int(H).bit_count()==e)==math.comb(21,e)
    # Reconstruct the common-denominator columns from the independently checked
    # primitive counts, without using the generator's column arithmetic.
    D=int(p['common_denominator']);names=p['pattern_names'].tolist()
    columns={}
    for column in meta['columns']:
        name,terms=column['name'],column['terms']
        coeff=[Fraction(terms.get(k,'0'))/int(p['pattern_denominators'][i]) for i,k in enumerate(names)]
        L=math.lcm(D,*(c.denominator for c in coeff))
        raw=p['pattern_counts'].astype(object)@np.array([int(c*L) for c in coeff],dtype=object)
        assert all(int(v)%(L//D)==0 for v in raw)
        columns[name]=raw//(L//D)
    assert p['free_names'].tolist()[:3]==['Phi1','Phi2','Phi3']
    for i,name in enumerate(['Phi1','Phi2','Phi3']):assert np.array_equal(columns[name],p['free_numerators'][:,i])
    for i,name in enumerate(p['positive_names'].tolist()):assert np.array_equal(columns[name],p['positive_numerators'][:,i])
    assert D%3024==0
    fixed=(144*p['fixed_density_complement_edge_counts']-5*p['fixed_density_induced_counts'])*(D//3024)
    assert np.array_equal(fixed,p['free_numerators'][:,3:])
    tau=Fraction(5,663552);assert (tau*D).denominator==1
    assert np.array_equal(np.array([int(tau*D)]*1044,dtype=object)-columns['theta'],p['target_numerators'])
    return {'status':'verified_exact','hosts':1044,'labelled_graphs_covered':2**21,
            'full_relabelings':1044*5040,'primitive_patterns_per_host':len(specs),
            'flag_product_blocks':5,'all_fixed_density_columns':34,
            'all_free_columns':37,'all_positive_variational_columns':4,
            'method':'Independent full-permutation integer recount; no production generator imports',
            'mathematical_specification':semantic_check,
            'seconds':time.time()-started,
            'input_sha256':{name:hashlib.sha256((data/name).read_bytes()).hexdigest()
                            for name in ['pattern_columns.npz','flag_basis.npz','pattern_columns.json']}}

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--data-dir',type=Path,default=ROOT/'certificates')
    ap.add_argument('--output',type=Path,default=ROOT/'results/combinatorial_input_verification.json')
    a=ap.parse_args();result=verify(a.data_dir)
    a.output.parent.mkdir(parents=True,exist_ok=True);tmp=a.output.with_suffix('.tmp')
    tmp.write_text(json.dumps(result,indent=2)+'\n');os.replace(tmp,a.output)
    print(json.dumps(result,indent=2))
