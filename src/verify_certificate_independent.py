#!/usr/bin/env python3
"""A second exact SOS checker using raw pattern counts and integer Gram matrices.

This does not import the certificate generator, its verifier, or its prebuilt
free/positive columns. It clears rational denominators, builds each entire
integer Gram matrix, and contracts it against each raw host tensor with Python
arbitrary-precision integers. Primitive count correctness is separately checked
by verify_combinatorial_inputs.py on every host.
"""

import _bootstrap  # local CLI module paths only
from pathlib import Path
from fractions import Fraction as F
import argparse, hashlib, json, math, os, sys, time
import numpy as np
from verification_json import load_proof_json, exact_fraction

ROOT=Path(__file__).resolve().parents[1]
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)

def verify(certificate,data_dir=None):
    if not __debug__:raise RuntimeError('Assertions are disabled; exact verification refuses to run under Python -O.')
    start=time.time();data=Path(data_dir or ROOT/'certificates');certificate=Path(certificate)
    c=load_proof_json(certificate)
    assert c.get('schema')=='induced-pentagons.exact-certificate.v1', 'Unrecognized main certificate schema'
    with np.load(data/'pattern_columns.npz') as a:p={k:a[k] for k in a.files}
    with np.load(data/'flag_basis.npz') as a:f={k:a[k] for k in a.files}
    assert c['constants']=={'pstar':'5/144','tau':'5/663552'}
    assert c['host_masks']==p['host_masks'].tolist()==f['host_masks'].tolist()
    assert len(c['host_masks'])==len(set(c['host_masks']))==1044
    free=[exact_fraction(r['coefficient'],f'{certificate.name}.free_columns[{i}].coefficient') for i,r in enumerate(c['free_columns'])]
    positive=[exact_fraction(r['coefficient'],f'{certificate.name}.positive_columns[{i}].coefficient') for i,r in enumerate(c['positive_columns'])]
    assert len(free)==37 and len(positive)==4 and min(positive)>=0
    assert [x['name'] for x in c['free_columns']]==p['free_names'].tolist()
    assert [x['name'] for x in c['positive_columns']]==['PhiTri','Ji0','Ji1','Jdel']
    assert -F(1157,10)<free[0]<0 and free[2]<0 and free[1]+free[2]>310
    slope=1-F(5,144)*free[0]**2/(4*(free[1]+free[2]));assert slope>F(5,8)
    squares=c['squares'];weights=[exact_fraction(r['coefficient'],f'{certificate.name}.squares[{i}].coefficient') for i,r in enumerate(squares)]
    assert all(w>0 for w in weights) and len({s['id'] for s in squares})==len(squares)
    slacks=[exact_fraction(r['coefficient'],f'{certificate.name}.slacks[{i}].coefficient') for i,r in enumerate(c['slacks'])]
    assert len(slacks)==1044 and all(s>=0 for s in slacks)
    for h,r in enumerate(c['slacks']):assert r['host_index']==h and r['host_mask']==c['host_masks'][h]
    S=math.lcm(*(x.denominator for x in free+positive+weights+slacks))
    raw={str(n):(p['pattern_counts'][:,i],int(p['pattern_denominators'][i]))
         for i,n in enumerate(p['pattern_names'])}
    tau=F(5,663552);pstar=F(5,144);kap=F(1,9216)
    terms={f'Phi{j}':{f'L{j}':pstar,f'B{j}':-tau} for j in (1,2,3)}
    terms['PhiTri']={'L_triangle':pstar,'B_triangle':-tau}
    for i in (0,1):terms[f'Ji{i}']={f'J{i}_A':F(1),f'J{i}_B':F(-1),f'R{i}':-kap}
    terms['Jdel']={'Jdel_Lg':F(1,2),'Ddel':-kap,
                  **{f'Jdel_Lf{i}{j}':F(-1,2) for i in (0,1) for j in (0,1)}}
    D=math.lcm(663552,raw['theta'][1],3024,140,1260,
               *((value/raw[name][1]).denominator for col in terms.values() for name,value in col.items()))
    residual=[int(tau*D*S)-int(x)*(D//raw['theta'][1])*S for x in raw['theta'][0]]
    for name,coef in zip(['Phi1','Phi2','Phi3','PhiTri','Ji0','Ji1','Jdel'],free[:3]+positive):
        w=int(coef*S)
        for pattern,value in terms[name].items():
            k=int(value*D/raw[pattern][1])*w
            for h,count in enumerate(raw[pattern][0]):residual[h]-=int(count)*k
    for j,coef in enumerate(free[3:]):
        k=int(coef*S)*(D//3024)
        for h in range(1044):
            num=144*int(p['fixed_density_complement_edge_counts'][h,j])-5*int(p['fixed_density_induced_counts'][h,j])
            residual[h]-=num*k
    byblock={}
    for square,w in zip(squares,weights):
        name=square['block'];v=square['vector'];d=len(f['flag_masks_'+name])
        assert len(v)==d and any(v) and all(type(x) is int for x in v)
        assert all(sum(int(q)*x for q,x in zip(row,v))==0 for row in f['Q_basis_'+name])
        if name not in byblock:byblock[name]=np.zeros((d,d),dtype=object)
        vv=np.array(v,dtype=object)
        byblock[name]+=int(w*S)*np.outer(vv,vv)
    for name,G in byblock.items():
        k=D//int(f['denominator_'+name]);C=f['C_'+name]
        for h in range(1044):
            i,j=np.nonzero(C[h])
            value=sum(int(C[h,a,b])*G[a,b] for a,b in zip(i,j))
            residual[h]-=k*value
    for h,(r,s) in enumerate(zip(residual,slacks)):
        assert r==int(s*S)*D,(h,'exact host identity failed')
    return {'status':'verified_exact','host_identities':1044,
            'positive_squares':len(squares),'positive_host_slacks':sum(s>0 for s in slacks),
            'positive_variational_terms':sum(a>0 for a in positive),
            'slope_lower_bound':str(slope),
            'method':'Raw primitive pattern densities; complete integer Gram matrices; Python arbitrary-precision contractions',
            'imports_production_verifier':False,
            'certificate_sha256':hashlib.sha256(certificate.read_bytes()).hexdigest(),
            'seconds':time.time()-start}

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--certificate',type=Path,default=ROOT/'certificates/all_graph_exact_certificate.json')
    ap.add_argument('--output',type=Path,default=ROOT/'results/independent_certificate_verification.json')
    a=ap.parse_args();r=verify(a.certificate)
    a.output.parent.mkdir(parents=True,exist_ok=True);tmp=a.output.with_suffix('.tmp')
    tmp.write_text(json.dumps(r,indent=2)+'\n');os.replace(tmp,a.output)
    print(json.dumps(r,indent=2))
