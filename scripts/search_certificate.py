#!/usr/bin/env python3
"""Numerical discovery of the exact flag-algebra certificate.

A numerical optimum is never a proof. Only the separately verified exact
rational identity and sign checks can discharge Proposition 4.1.
"""

import _bootstrap  # local CLI module paths only
import argparse, json, time
from pathlib import Path
import numpy as np
import scipy.sparse as sp
import cvxpy as cp

ROOT=Path(__file__).resolve().parents[1]
def run(solver='CLARABEL',triangle=False,max_iter=200,relax=True):
    f=np.load(ROOT/'certificates/flag_basis.npz')
    p=np.load(ROOT/'certificates/pattern_columns.npz')
    assert np.array_equal(f['host_masks'],p['host_masks'])
    names=['one_root','independent3','edge_isolate','path3']
    if triangle:names.append('triangle3')
    constraints=[];data={};terms=[];traces=[];variables={}
    free=p['free_columns'];pos=p['positive_columns'];target=p['target']
    fs=np.maximum(np.max(np.abs(free),axis=0),1e-15)
    ps=np.maximum(np.max(np.abs(pos),axis=0),1e-15)
    lf=cp.Variable(37,name='scaled_free');ap=cp.Variable(4,nonneg=True,name='scaled_positive')
    # Column normalization changes variables, never the underlying identity.
    terms.extend([(free/fs)@lf,(pos/ps)@ap])
    constraints.extend([lf[0]>=-115.699*fs[0],lf[0]<=-1e-5*fs[0],
                        lf[2]<=-1e-5*fs[2],lf[1]/fs[1]+lf[2]/fs[2]>=310.001])
    for name in names:
        B=f['B_'+name].astype(float)
        U,R=np.linalg.qr(B,mode='reduced')
        raw=f['C_'+name].astype(float)/int(f['denominator_'+name])
        reduced=np.einsum('ai,hab,bj->hij',U,raw,U,optimize=True)
        r=U.shape[1]
        X=cp.Variable((r,r),symmetric=True,name=name)
        constraints.append(X>>0)
        flat=reduced.transpose(0,2,1).reshape(len(target),r*r)
        # Columns with tiny QR noise are explicitly zeroed for sparse storage;
        # the discovery matrix alone is approximate, exact verification is later.
        flat[np.abs(flat)<1e-16]=0
        terms.append(sp.csr_matrix(flat)@cp.reshape(X,(r*r,),order='F'))
        traces.append(cp.trace(X));variables[name]=X
        data['U_'+name]=U;data['R_'+name]=R
        print(name,'rank',r,'nonzero coefficients',np.count_nonzero(flat),flush=True)
    expr=sum(terms)
    delta=cp.Variable(nonneg=True,name='relaxation') if relax else 0
    constraints.append(expr<=target+delta)
    objective=cp.Minimize(delta+1e-9*sum(traces)) if relax else cp.Minimize(sum(traces))
    problem=cp.Problem(objective,constraints)
    start=time.time()
    if solver=='CLARABEL':
        options=dict(max_iter=max_iter,tol_gap_abs=1e-10,tol_feas=1e-10,
                     tol_gap_rel=1e-10,verbose=True)
    else:
        options=dict(max_iters=max_iter,eps=2e-8,verbose=True,normalize=True,
                     acceleration_lookback=10)
    try:problem.solve(solver=solver,**options)
    except Exception as e:print('Solver exception',repr(e),flush=True)
    result={'solver':solver,'status':problem.status,'objective':problem.value,
            'elapsed_seconds':time.time()-start,'numerical_discovery_only':True,
            'triangle_block':triangle,'blocks':names}
    if lf.value is not None:
        data['lambda_free']=lf.value/fs;data['a_positive']=ap.value/ps
        data['delta']=np.array(float(delta.value) if relax else 0.0)
        data['slacks']=target+float(data['delta'])-expr.value
        result.update(delta=float(data['delta']),slack_min=float(data['slacks'].min()),
                      lambda_first3=data['lambda_free'][:3].tolist(),a_positive=data['a_positive'].tolist(),
                      block_min_eigenvalues={})
        for name,X in variables.items():
            data['X_'+name]=X.value
            result['block_min_eigenvalues'][name]=float(np.linalg.eigvalsh(X.value)[0])
        data['block_names']=np.array(names)
        (ROOT/'results').mkdir(exist_ok=True)
        np.savez_compressed(ROOT/'results/sdp_solution.npz',**data)
    (ROOT/'results/sdp_search_summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--solver',default='CLARABEL',choices=['CLARABEL','SCS'])
    a.add_argument('--triangle',action='store_true');a.add_argument('--max-iter',type=int,default=200)
    a.add_argument('--no-relax',action='store_true');args=a.parse_args()
    run(args.solver,args.triangle,args.max_iter,not args.no_relax)
