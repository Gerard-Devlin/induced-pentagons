#!/usr/bin/env python3
"""Construct and verify exact equality spans from a verified main SOS.

No witness is emitted unless it is an exact combination of square vectors
whose coefficients in the actual main certificate are strictly positive.
"""

import _bootstrap  # local CLI module paths only
from pathlib import Path
from fractions import Fraction
from itertools import combinations
import argparse, hashlib, json, os, sys
import numpy as np
from verification_json import load_proof_json, exact_fraction

ROOT=Path(__file__).resolve().parents[1]
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)

def atomic(path,obj):
    path=Path(path);tmp=path.with_suffix(path.suffix+'.tmp')
    tmp.write_text(json.dumps(obj,indent=2)+'\n');os.replace(tmp,path)

def exact_solve(columns, target):
    """Exact rational solve; optional FLINT acceleration, SymPy fallback."""
    n,m=len(target),len(columns)
    if any(len(col)!=n for col in columns): raise ValueError('Ragged coefficient columns')
    if not m: return [] if all(x==0 for x in target) else None
    if not n: return [Fraction(0)]*m
    rows=[[Fraction(columns[j][i]) for j in range(m)]+[Fraction(target[i])] for i in range(n)]
    try:
        from flint import fmpq_mat
    except ModuleNotFoundError as exc:
        if exc.name != 'flint': raise
        from sympy import Matrix, Rational
        mat,pivots=Matrix([[Rational(v.numerator,v.denominator) for v in row] for row in rows]).rref()
        rank=len(pivots)
    else:
        mat,rank=fmpq_mat([[str(v) for v in row] for row in rows]).rref()
    x=[Fraction(0)]*m
    for i in range(rank):
        piv=next((j for j in range(m+1) if mat[i,j]),None)
        if piv==m:return None
        if piv is not None:x[piv]=Fraction(str(mat[i,m]))
    if not all(sum(Fraction(columns[j][i])*x[j] for j in range(m))==Fraction(target[i]) for i in range(n)):
        raise ArithmeticError('Exact linear-system residual is nonzero')
    return x

def mask_functions():
    bits={p:i for i,p in enumerate(combinations(range(5),2))}
    def edge(mask,a,b):return (int(mask)>>bits[tuple(sorted((a,b)))])&1
    def triangle(mask):return any(edge(mask,a,b)*edge(mask,a,c)*edge(mask,b,c) for a,b,c in combinations(range(5),3))
    return edge,triangle

def positive_sources(cert,block):
    return [s for s in cert['squares'] if s['block']==block and Fraction(s['coefficient'])>0]

def combination(sources,weights):
    return [{'source_id':s['id'],'coefficient':str(w)} for s,w in zip(sources,weights) if w]

def triangle_combination(sources,masks):
    _,tri=mask_functions();target=[int(tri(m)) for m in masks]
    cols=[s['vector'] for s in sources]
    weights=exact_solve(cols,target)
    if weights is not None:return weights,[Fraction(x) for x in target]
    # A different strictly positive triangle vector is equally sufficient.
    from scipy.optimize import linprog
    V=np.array(cols,dtype=float).T
    tf=np.array([i for i,x in enumerate(target) if x==0]);bad=np.array([i for i,x in enumerate(target) if x])
    norms=np.maximum(np.max(np.abs(V),axis=0),1);A=V/norms
    r=linprog(np.zeros(len(cols)),A_ub=-A[bad],b_ub=-np.ones(len(bad)),
              A_eq=A[tf],b_eq=np.zeros(len(tf)),bounds=[(None,None)]*len(cols),method='highs')
    if not r.success:raise RuntimeError('Triangle domination is not certified by the positive square span.')
    support=np.where(np.abs(r.x)>1e-9)[0].tolist()
    active=[int(i) for i in bad if abs((A@r.x)[i]-1)<1e-6]
    rows=tf.tolist()+active;rhs=[0]*len(tf)+[1]*len(active)
    reduced=exact_solve([[cols[j][i] for i in rows] for j in support],rhs)
    if reduced is None:raise RuntimeError('Triangle LP did not yield an exact rational witness.')
    weights=[Fraction(0)]*len(cols)
    for j,v in zip(support,reduced):weights[j]=v
    G=[sum(w*c[i] for w,c in zip(weights,cols)) for i in range(len(masks))]
    if not all((G[i]>=1 if target[i] else G[i]==0) for i in range(len(masks))):
        raise RuntimeError('Exact triangle sign check failed; no witness emitted.')
    return weights,G

def verify_spans(certificate,triangle_file,degree_file,data_dir=None):
    if not __debug__:
        raise RuntimeError('Exact equality-span verification refuses Python -O, -OO, or PYTHONOPTIMIZE.')
    data=Path(data_dir or ROOT/'certificates');certificate=Path(certificate)
    # A positive coefficient in an arbitrary JSON object is not evidence that
    # its square vanishes at equality.  Verify the complete main identity and
    # signs here as well, including when this entry point is used standalone.
    from rationalize_certificate import verify_certificate
    maincheck=verify_certificate(certificate,data)
    cert=load_proof_json(certificate);digest=hashlib.sha256(certificate.read_bytes()).hexdigest()
    for category in ('free_columns','positive_columns','squares','slacks'):
        for index,item in enumerate(cert[category]):
            exact_fraction(item['coefficient'],f'{certificate.name}.{category}[{index}].coefficient')
    flags=np.load(data/'flag_basis.npz');edge,tri=mask_functions()
    allsrc={s['id']:s for s in cert['squares']}
    def combine(terms,block,indices,extras=None):
        extras=extras or {};v=[Fraction(0)]*len(indices)
        for item in terms:
            name=item['source_id'];w=exact_fraction(item['coefficient'],f'{block} span source {name!r}')
            if name in extras:row=extras[name]
            else:
                s=allsrc[name]
                assert s['block']==block and exact_fraction(s['coefficient'],f'main square {name!r}')>0
                row=s['vector']
            for j,i in enumerate(indices):v[j]+=w*int(row[i])
        return v
    t=load_proof_json(triangle_file)
    assert t.get('schema')=='induced-pentagons.triangle-span.v1', 'Unrecognized triangle-span schema'
    assert t['certificate_sha256']==digest
    masks=flags['flag_masks_path3'].tolist();assert t['flag_masks']==masks
    v=combine(t['combination'],'path3',list(range(len(masks))))
    assert [str(x) for x in v]==t['result_vector']
    assert all((v[i]>=1 if tri(m) else v[i]==0) for i,m in enumerate(masks))
    d=load_proof_json(degree_file)
    assert d.get('schema')=='induced-pentagons.degree-codegree-spans.v1', 'Unrecognized degree/codegree-span schema'
    assert d['certificate_sha256']==digest
    ix=[i for i,m in enumerate(masks) if not tri(m)]
    assert len(ix)==24 and d['degree']['flag_indices']==ix
    target=[24*(edge(masks[i],1,3)+edge(masks[i],1,4))-5 for i in ix]
    assert combine(d['degree']['combination'],'path3',ix)==target
    masks=flags['flag_masks_edge_isolate'].tolist();ix=[i for i,m in enumerate(masks) if not tri(m)]
    assert len(ix)==32
    extras={f'degree_identity_{r}':[24*(edge(m,r,3)+edge(m,r,4))-5 for m in masks] for r in (0,1)}
    for item in d['codegree']:
        r=item['root'];assert r in (0,1) and item['flag_indices']==ix
        target=[5*sum(edge(masks[i],r,j)*edge(masks[i],2,j) for j in (3,4))
                -2*sum(edge(masks[i],2,j) for j in (3,4)) for i in ix]
        assert combine(item['combination'],'edge_isolate',ix,extras)==target
    assert sorted(x['root'] for x in d['codegree'])==[0,1]
    return {'status':'verified_exact','triangle_coordinates':72,
            'triangle_free_path_coordinates':24,'codegree_coordinates_each':32,
            'certificate_sha256':digest,'main_certificate_verification':maincheck}

def generate(certificate,data_dir=None):
    from rationalize_certificate import verify_certificate
    data=Path(data_dir or ROOT/'certificates');certificate=Path(certificate)
    maincheck=verify_certificate(certificate,data)
    cert=json.loads(certificate.read_text());digest=hashlib.sha256(certificate.read_bytes()).hexdigest()
    f=np.load(data/'flag_basis.npz');edge,tri=mask_functions()
    masks=f['flag_masks_path3'].tolist();src=positive_sources(cert,'path3')
    w,G=triangle_combination(src,masks)
    tr={'schema':'induced-pentagons.triangle-span.v1','certificate_sha256':digest,
        'provenance':'Exact triangle-domination witness for the main certificate',
        'flag_masks':masks,'combination':combination(src,w),'result_vector':[str(v) for v in G]}
    ix=[i for i,m in enumerate(masks) if not tri(m)]
    target=[24*(edge(masks[i],1,3)+edge(masks[i],1,4))-5 for i in ix]
    w=exact_solve([[s['vector'][i] for i in ix] for s in src],target)
    if w is None:raise RuntimeError('Degree span is not proved by the current positive squares.')
    dg={'schema':'induced-pentagons.degree-codegree-spans.v1','certificate_sha256':digest,
        'provenance':'Exact degree and codegree witnesses for the main certificate',
        'degree':{'flag_indices':ix,'combination':combination(src,w)},'codegree':[]}
    masks=f['flag_masks_edge_isolate'].tolist();ix=[i for i,m in enumerate(masks) if not tri(m)]
    src=positive_sources(cert,'edge_isolate')
    extra=[{'id':f'degree_identity_{r}','vector':[24*(edge(m,r,3)+edge(m,r,4))-5 for m in masks]} for r in (0,1)]
    available=src+extra
    for r in (0,1):
        target=[5*sum(edge(masks[i],r,j)*edge(masks[i],2,j) for j in (3,4))
                -2*sum(edge(masks[i],2,j) for j in (3,4)) for i in ix]
        w=exact_solve([[s['vector'][i] for i in ix] for s in available],target)
        if w is None:raise RuntimeError(f'Codegree span {r} is not certified.')
        dg['codegree'].append({'root':r,'flag_indices':ix,'combination':combination(available,w)})
    trfile=data/'all_graph_path3_triangle_domination_span.json'
    dgfile=data/'all_graph_tf_degree_codegree_spans.json'
    # Commit only after both objects have passed an independent readback check.
    trtmp=trfile.with_suffix('.pending.json');dgtmp=dgfile.with_suffix('.pending.json')
    atomic(trtmp,tr);atomic(dgtmp,dg)
    report=verify_spans(certificate,trtmp,dgtmp,data)
    os.replace(trtmp,trfile);os.replace(dgtmp,dgfile)
    atomic(ROOT/'results/equality_spans_verification.json',report)
    return report

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--certificate',type=Path,default=ROOT/'certificates/all_graph_exact_certificate.json')
    ap.add_argument('--verify-only',action='store_true');a=ap.parse_args()
    if a.verify_only:
        result=verify_spans(a.certificate,ROOT/'certificates/all_graph_path3_triangle_domination_span.json',
                           ROOT/'certificates/all_graph_tf_degree_codegree_spans.json')
    else:result=generate(a.certificate)
    print(json.dumps(result,indent=2))
