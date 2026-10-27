#!/usr/bin/env python3
"""Search for, rationalize, and verify a NEW exact pentagon certificate.

A numerical SDP is a discovery aid, never the proof. This program rounds
rank-one directions into the exact equality kernel, solves a finite LP,
reconstructs a basic solution over Q, and checks every host row and sign
exactly before emitting a certificate. Failure emits diagnostics only.

Inputs:
  certificates/flag_basis.npz, certificates/pattern_columns.npz,
  certificates/equality_host_support.json, results/sdp_csdp_regularized_solution.npz
The SDP archive supplies U_<block> and X_<block>.

Dependencies: numpy, scipy, sympy; python-flint strongly recommended.
"""
from __future__ import annotations

import _bootstrap  # local CLI module paths only

import argparse
from fractions import Fraction
import hashlib
import io
import json
import math
import os
from pathlib import Path
import sys
import time

import numpy as np
import scipy.linalg as sla
from scipy.optimize import linprog
from scipy.sparse import csr_matrix
import sympy as sp

ROOT=Path(__file__).resolve().parents[1]
BLOCKS=("one_root","independent3","edge_isolate","path3","triangle3")
LOWER_L1=Fraction("-115.699")
UPPER_NEGATIVE=Fraction("-0.00000001")
LOWER_SUM=Fraction("310.001")


def atomic_json(path, obj):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
    tmp=path.with_suffix(path.suffix+".tmp")
    tmp.write_text(json.dumps(obj,indent=2)+"\n",encoding="utf-8")
    os.replace(tmp,path)


def egcd(a,b):
    oldr,r=a,b;olds,s=1,0;oldt,t=0,1
    while r:
        q=oldr//r
        oldr,r=r,oldr-q*r;olds,s=s,olds-q*s;oldt,t=t,oldt-q*t
    return (oldr,olds,oldt) if oldr>=0 else (-oldr,-olds,-oldt)


def saturated_kernel(rows, dimension):
    """An integer basis of ker_Z(rows), with an LLL step after each row.

    Each extended-gcd column operation is unimodular. Deleting the single
    nonzero coordinate of a row therefore preserves the full saturated
    integer kernel, unlike independently clearing RREF column denominators.
    """
    Q=sp.Matrix(rows.tolist()) if len(rows) else sp.zeros(0,dimension)
    K=sp.eye(dimension)
    for k in range(Q.rows):
        a=list(Q[k,:]*K)
        if not any(a): continue
        j=min((j for j,x in enumerate(a) if x),key=lambda j:abs(a[j]))
        K.col_swap(0,j);a[0],a[j]=a[j],a[0]
        for j in range(1,K.cols):
            if not a[j]: continue
            x,y=int(a[0]),int(a[j]);g,s,t=egcd(x,y)
            old0,oldj=K[:,0],K[:,j]
            K[:,0]=s*old0+t*oldj
            K[:,j]=(-y//g)*old0+(x//g)*oldj
            a[0],a[j]=g,0
        K=K[:,1:]
        K=K.T.lll().T
    assert Q*K==sp.zeros(Q.rows,K.cols)
    assert K.cols==dimension-Q.rank()
    return np.array(K.tolist(),dtype=np.int64)


def primitive(v):
    values=[int(x) for x in v]
    g=math.gcd(*values)
    if not g: return None
    values=[x//g for x in values]
    if next(x for x in values if x)<0: values=[-x for x in values]
    return np.array(values,dtype=np.int64)


def seed_vectors(name,masks):
    if name not in ("path3","edge_isolate"): return []
    pairs=[(i,j) for i in range(5) for j in range(i+1,5)]
    bits={p:k for k,p in enumerate(pairs)}
    def edge(m,i,j):
        return (int(m)>>bits[tuple(sorted((i,j)))])&1
    if name=="path3":
        triangle=[]
        for m in masks:
            triangle.append(int(any(edge(m,a,b) and edge(m,a,c) and edge(m,b,c)
                                    for a in range(5) for b in range(a+1,5)
                                    for c in range(b+1,5))))
        degree=[24*(edge(m,1,3)+edge(m,1,4))-5 for m in masks]
        return [("triangle_indicator",triangle),("degree_target",degree)]
    return [(f"codegree_target_{i}",
             [5*sum(edge(m,i,j)*edge(m,2,j) for j in (3,4))
              -2*sum(edge(m,2,j) for j in (3,4)) for m in masks])
            for i in (0,1)]


def qnumerators(C,vectors):
    """Return v^T C_H v for every host and integer vector."""
    vectors=np.asarray(vectors,dtype=np.int64)
    if vectors.ndim==1: vectors=vectors[np.newaxis,:]
    maxv=max((abs(int(x)) for x in vectors.flat),default=0)
    # Each C_H has nonnegative entries with sum <= its sampling denominator.
    limit=int(np.max(C.sum(axis=(1,2))))*maxv*maxv
    if limit < np.iinfo(np.int64).max:
        outers=(vectors[:,:,None]*vectors[:,None,:]).reshape(len(vectors),-1)
        return csr_matrix(C.reshape(C.shape[0],-1),dtype=np.int64) @ outers.T
    # Conservative arbitrary-integer fallback for independently supplied data.
    result=np.zeros((len(C),len(vectors)),dtype=object)
    for h,mat in enumerate(C):
        ii,jj=np.nonzero(mat)
        for j,v in enumerate(vectors):
            result[h,j]=sum(int(mat[a,b])*int(v[a])*int(v[b]) for a,b in zip(ii,jj))
    return result


def candidate_directions(flags,solution,kernels,grid,rotations=1,eigen_tol=1e-9):
    candidates=[]
    rng=np.random.default_rng(20261027)
    for name in BLOCKS:
        if f"X_{name}" not in solution: continue
        U=np.asarray(solution[f"U_{name}"],float)
        X=np.asarray(solution[f"X_{name}"],float)
        X=(X+X.T)/2
        ev,vec=np.linalg.eigh(X)
        keep=ev>max(1e-14,eigen_tol*max(0,float(ev.max())))
        vectors=U@vec[:,keep]
        K=kernels[name]
        raw=[(f"eigen_{i}",vectors[:,i]) for i in range(vectors.shape[1])]
        # Random rotations of a PSD factor add directions in the same numeric
        # range, enlarging the finite rank-one cone without assuming positivity.
        factor=vectors*np.sqrt(ev[keep])[np.newaxis,:]
        for j in range(rotations):
            rot,_=np.linalg.qr(rng.normal(size=(factor.shape[1],factor.shape[1])))
            other=factor@rot
            raw.extend((f"rot{j}_{i}",other[:,i]/np.linalg.norm(other[:,i]))
                       for i in range(other.shape[1]) if np.linalg.norm(other[:,i])>1e-16)
        selected=[];seen=set()
        for label,v in raw:
            coeff=np.linalg.lstsq(K.astype(float),v,rcond=None)[0]
            integer=primitive(K@np.rint(grid*coeff).astype(np.int64))
            if integer is None: continue
            key=tuple(map(int,integer))
            if key in seen: continue
            seen.add(key);selected.append((label,integer,False))
        for label,v in seed_vectors(name,flags[f"flag_masks_{name}"]):
            integer=primitive(v)
            if integer is None: continue
            key=tuple(map(int,integer))
            if key not in seen:
                seen.add(key);selected.append((label,integer,True))
        Q=flags[f"Q_basis_{name}"]
        for _,v,_ in selected:
            assert all(sum(int(q)*int(x) for q,x in zip(row,v))==0 for row in Q)
        counts=qnumerators(flags[f"C_{name}"],[v for _,v,_ in selected])
        for j,(label,v,is_seed) in enumerate(selected):
            norm2=sum(int(x)**2 for x in v)
            candidates.append({
                "id":f"{name}_{hashlib.sha256(v.tobytes()).hexdigest()[:16]}",
                "block":name,"origin":label,"vector":v,"norm2":norm2,
                "denominator":int(flags[f"denominator_{name}"]),
                "qnum":counts[:,j],"seed":is_seed})
        print(f"  {name}: rank {int(keep.sum())}, {len(selected)} candidates",flush=True)
    return candidates


def exact_basic_solve(matrix,rhs):
    try:
        from flint import fmpq_mat
        x=fmpq_mat(matrix).solve(fmpq_mat([[v] for v in rhs]))
        return [Fraction(str(x[i,0])) for i in range(len(rhs))]
    except ImportError:
        x=sp.Matrix(matrix).inv()*sp.Matrix(rhs)
        return [Fraction(int(v.p),int(v.q)) for v in x]


def cleared_residual(patterns,candidates,coefficients):
    """Compute D*S*(target - free - positive - squares) with integers."""
    D=int(patterns["common_denominator"])
    S=math.lcm(*(v.denominator for v in coefficients))
    residual=[int(t)*S for t in patterns["target_numerators"]]
    base=np.column_stack((patterns["free_numerators"],patterns["positive_numerators"]))
    for j,c in enumerate(coefficients[:41]):
        if not c: continue
        mult=int(c*S)
        for h in range(1044): residual[h]-=int(base[h,j])*mult
    for candidate,c in zip(candidates,coefficients[41:]):
        if not c: continue
        mult=(D//candidate["denominator"])*int(c*S)
        for h,q in enumerate(candidate["qnum"]): residual[h]-=int(q)*mult
    return residual,D*S


def rational_from_lp(patterns,candidates,Abar,bbar,scales,result,support,
                     tight_tolerance=1e-8,seed_min_weight=Fraction(0)):
    tau=Fraction(5,663552)
    z=result.x
    active=list(range(37))+[j for j in range(37,len(z)) if z[j]>1e-12]
    slack=bbar-Abar@z
    tight=set(support)
    tight.update(np.flatnonzero(slack <= tight_tolerance).tolist())
    records=[("host",h) for h in sorted(tight)]
    float_rows=[Abar[h,active] for _,h in records]
    float_rhs=[bbar[h] for _,h in records]
    original=z*float(tau)/scales
    bounds=[]
    if result.lower.residual[0]<tight_tolerance: bounds.append(("l1_lower",0,LOWER_L1,1))
    if result.upper.residual[0]<tight_tolerance: bounds.append(("l1_upper",0,UPPER_NEGATIVE,1))
    if result.upper.residual[2]<tight_tolerance: bounds.append(("l3_upper",2,UPPER_NEGATIVE,1))
    if seed_min_weight>0:
        for j,candidate in enumerate(candidates,41):
            if candidate["seed"] and result.lower.residual[j]<tight_tolerance:
                bounds.append(("seed",j,seed_min_weight/candidate["norm2"],candidate["norm2"]))
    for label,j,value,norm_divisor in bounds:
        row=np.zeros(len(z));row[j]=float(tau)/scales[j]/norm_divisor
        records.append(("bound",(j,value)))
        float_rows.append(row[active]);float_rhs.append(float(value))
    if abs(original[1]+original[2]-float(LOWER_SUM))<tight_tolerance:
        row=np.zeros(len(z));row[1]=float(tau)/scales[1];row[2]=float(tau)/scales[2]
        records.append(("sum",LOWER_SUM))
        float_rows.append(row[active]);float_rhs.append(float(LOWER_SUM))
    M=np.array(float_rows)
    norms=np.linalg.norm(M,axis=1);norms[norms==0]=1
    _,R,piv=sla.qr((M/norms[:,None]).T,pivoting=True,mode="economic")
    diag=np.abs(np.diag(R))
    rank=int(np.sum(diag>max(1e-11,diag.max()*1e-10))) if len(diag) else 0
    if rank<len(active):
        return None,{"reason":"insufficient independent tight constraints",
                     "rank":rank,"active_variables":len(active),"tight_rows":len(records)}
    chosen=piv[:len(active)]
    D=int(patterns["common_denominator"])
    base=np.column_stack((patterns["free_numerators"],patterns["positive_numerators"]))
    exactrows=[];exactrhs=[]
    for rid in chosen:
        kind,info=records[int(rid)]
        if kind=="host":
            h=int(info)
            row=[int(base[h,j]) for j in range(41)]
            row += [int(c["qnum"][h])*(D//c["denominator"]) for c in candidates]
            rhs=int(patterns["target_numerators"][h])
        else:
            row=[0]*len(z)
            if kind=="bound":
                j,value=info;row[j]=value.denominator;rhs=value.numerator
            else:
                value=info;row[1]=row[2]=value.denominator;rhs=value.numerator
        exactrows.append([row[j] for j in active]);exactrhs.append(rhs)
    try:
        solution=exact_basic_solve(exactrows,exactrhs)
    except Exception as e:
        return None,{"reason":"exact basic-system solve failed","exception":str(e)}
    coefficients=[Fraction(0)]*len(z)
    for j,c in zip(active,solution): coefficients[j]=c
    residual,den=cleared_residual(patterns,candidates,coefficients)
    badhosts=[h for h,r in enumerate(residual) if r<0]
    badweights=[j for j,c in enumerate(coefficients[37:],37) if c<0]
    badseeds=([j for j,candidate in enumerate(candidates,41)
               if candidate["seed"] and coefficients[j]<=0]
              if seed_min_weight>0 else [])
    l1,l2,l3=coefficients[:3]
    good_slope=(-Fraction(1157,10)<l1<0 and l3<0 and l2+l3>310)
    diagnostics={
        "active_variables":len(active),"tight_rows":len(records),
        "negative_host_slacks":len(badhosts),"negative_weights":len(badweights),
        "nonpositive_required_seeds":len(badseeds),
        "stated_slope_bounds":good_slope,
        "selected_host_rows":[int(records[int(r)][1]) for r in chosen
                              if records[int(r)][0]=="host"],
        "coefficient_denominator_bits":max(c.denominator.bit_length() for c in coefficients),
    }
    if badhosts:
        diagnostics["negative_host_indices"]=badhosts[:30]
        diagnostics["minimum_slack"]=float(Fraction(min(residual),den))
    if badhosts or badweights or badseeds or not good_slope:
        return None,diagnostics
    return (coefficients,[Fraction(r,den) for r in residual]),diagnostics


def make_certificate(patterns,candidates,exact,diagnostics):
    coefficients,slacks=exact
    squares=[{"id":c["id"],"block":c["block"],
              "vector":[int(x) for x in c["vector"]],"coefficient":str(coef)}
             for c,coef in zip(candidates,coefficients[41:]) if coef>0]
    return {
        "schema":"induced-pentagons.exact-certificate.v1",
        "provenance":"Exact rational witness for Proposition 4.1.",
        "status":"exact_identity_verified; equality span witnesses are separate",
        "identity":"tau-theta = free + positive_variational + flag_squares + host_slacks",
        "constants":{"pstar":"5/144","tau":"5/663552"},
        "host_masks":[int(x) for x in patterns["host_masks"]],
        "free_columns":[{"name":str(n),"coefficient":str(c)}
                        for n,c in zip(patterns["free_names"],coefficients[:37])],
        "positive_columns":[{"name":str(n),"coefficient":str(c)}
                            for n,c in zip(patterns["positive_names"],coefficients[37:41])],
        "squares":squares,
        "slacks":[{"host_index":i,"host_mask":int(patterns["host_masks"][i]),
                   "coefficient":str(s)} for i,s in enumerate(slacks)],
        "discovery_diagnostics":diagnostics,
    }


def verify_certificate(certificate_path,data_dir=None):
    """Independently verify every rational row, kernel condition, and sign.

    This checks the sharp-bound certificate. Triangle/degree/codegree span
    witnesses are additionally checked for the equality classification.
    """
    if not __debug__:
        raise RuntimeError("Exact verification requires assertions; do not run Python with -O, -OO, or PYTHONOPTIMIZE.")
    if hasattr(sys,"set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    from verification_json import load_proof_json, exact_fraction
    data=Path(data_dir or ROOT/"certificates")
    cert=load_proof_json(certificate_path)
    assert cert.get("schema")=="induced-pentagons.exact-certificate.v1", 'Unrecognized main certificate schema'
    patterns=np.load(data/"pattern_columns.npz",allow_pickle=False)
    flags=np.load(data/"flag_basis.npz",allow_pickle=False)
    assert cert["constants"]=={"pstar":"5/144","tau":"5/663552"}
    assert cert["host_masks"]==patterns["host_masks"].tolist()==flags["host_masks"].tolist()
    assert [r["name"] for r in cert["free_columns"]]==patterns["free_names"].tolist()
    assert [r["name"] for r in cert["positive_columns"]]==patterns["positive_names"].tolist()
    coefficients=[exact_fraction(r["coefficient"],f'{Path(certificate_path).name}.{category}[{i}].coefficient')
                  for category in ("free_columns","positive_columns")
                  for i,r in enumerate(cert[category])]
    assert len(coefficients)==41 and all(c>=0 for c in coefficients[37:])
    l1,l2,l3=coefficients[:3]
    assert -Fraction(1157,10)<l1<0 and l3<0 and l2+l3>310
    slope=1-Fraction(5,144)*l1*l1/(4*(l2+l3))
    assert slope>Fraction(5,8)
    candidates=[];seen=set();by_block={}
    for s in cert["squares"]:
        name=s["block"];assert name in BLOCKS
        assert s["id"] not in seen;seen.add(s["id"])
        vector=s["vector"]
        assert all(type(x) is int for x in vector)
        assert len(vector)==len(flags[f"flag_masks_{name}"]) and any(vector)
        Q=flags[f"Q_basis_{name}"]
        assert all(sum(int(q)*v for q,v in zip(row,vector))==0 for row in Q)
        coefficient=exact_fraction(s["coefficient"],f'{Path(certificate_path).name}.square {s["id"]!r}');assert coefficient>0
        coefficients.append(coefficient)
        by_block.setdefault(name,[]).append((len(candidates),vector))
        candidates.append({"denominator":int(flags[f"denominator_{name}"])})
    for name,entries in by_block.items():
        allcounts=qnumerators(flags[f"C_{name}"],[v for _,v in entries])
        for j,(index,_) in enumerate(entries):
            candidates[index]["qnum"]=allcounts[:,j]
    residual,den=cleared_residual(patterns,candidates,coefficients)
    assert len(cert["slacks"])==1044
    positive_slacks=0
    for h,(r,stored) in enumerate(zip(residual,cert["slacks"])):
        assert stored["host_index"]==h and stored["host_mask"]==int(patterns["host_masks"][h])
        actual=Fraction(r,den)
        assert actual==exact_fraction(stored["coefficient"],f'{Path(certificate_path).name}.slacks[{h}].coefficient'), (h, 'exact host identity failed')
        assert actual>=0
        positive_slacks += actual>0
    return {"status":"verified_exact","host_identities":1044,
            "positive_squares":len(candidates),"positive_host_slacks":positive_slacks,
            "positive_variational_terms":sum(c>0 for c in coefficients[37:41]),
            "slope_lower_bound":str(slope),"slope_exceeds_5_over_8":True}


def main():
    if not __debug__:
        raise RuntimeError("Certificate reconstruction requires assertions; do not use Python -O, -OO, or PYTHONOPTIMIZE.")
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--data-dir",type=Path,default=ROOT/"certificates")
    ap.add_argument("--solution",type=Path,default=ROOT/"results"/"sdp_csdp_regularized_solution.npz")
    ap.add_argument("--output",type=Path,default=ROOT/"certificates"/"all_graph_exact_certificate.json")
    ap.add_argument("--grids",default="1000,10000,100000,1000000,10000000")
    ap.add_argument("--rotations",type=int,default=1)
    ap.add_argument("--eigen-tolerance",type=float,default=1e-12)
    ap.add_argument("--seed-min-weight",type=float,default=1e-10,
                    help="positive normalized weight for four equality targets; 0 permits a bound-only certificate")
    ap.add_argument("--verify-only",action="store_true")
    args=ap.parse_args()
    if args.verify_only:
        print(json.dumps(verify_certificate(args.output,args.data_dir),indent=2));return
    if not args.solution.exists():
        raise SystemExit("Numerical SDP input is absent; no certificate emitted.")
    patterns=np.load(args.data_dir/"pattern_columns.npz")
    flags=np.load(args.data_dir/"flag_basis.npz")
    solution=np.load(args.solution)
    assert np.array_equal(patterns["host_masks"],flags["host_masks"])
    support=json.loads((args.data_dir/"equality_host_support.json").read_text())["supported_host_indices"]
    kernels={}
    for name in BLOCKS:
        if f"X_{name}" not in solution: continue
        kernels[name]=saturated_kernel(flags[f"Q_basis_{name}"],len(flags[f"flag_masks_{name}"]))
        print(f"Kernel {name}: {kernels[name].shape}, max entry {abs(kernels[name]).max()}",flush=True)
    attempts=[]
    for grid in map(int,args.grids.split(",")):
        start=time.time()
        print(f"Rational direction grid {grid}",flush=True)
        candidates=candidate_directions(flags,solution,kernels,grid,
                                         args.rotations,args.eigen_tolerance)
        squares=np.column_stack([np.asarray(c["qnum"],float)/c["denominator"]/c["norm2"]
                                  for c in candidates])
        A=np.column_stack((patterns["free_columns"],patterns["positive_columns"],squares))
        scales=np.max(np.abs(A),axis=0);scales[scales==0]=1
        tau=float(Fraction(5,663552))
        Abar=A/scales[np.newaxis,:];bbar=patterns["target"]/tau
        bounds=[(None,None)]*37+[(0,None)]*(4+len(candidates))
        bounds[0]=(float(LOWER_L1)*scales[0]/tau,float(UPPER_NEGATIVE)*scales[0]/tau)
        bounds[2]=(None,float(UPPER_NEGATIVE)*scales[2]/tau)
        for i,c in enumerate(candidates,41):
            if c["seed"] and args.seed_min_weight>0:
                bounds[i]=(args.seed_min_weight*scales[i]/tau,None)
        extra=np.zeros(len(bounds));extra[1]=-tau/scales[1];extra[2]=-tau/scales[2]
        outside=np.array(sorted(set(range(1044))-set(support)),dtype=int)
        Aub=np.vstack((Abar[outside],extra[None,:]))
        bub=np.r_[bbar[outside],-float(LOWER_SUM)]
        result=linprog(np.zeros(len(bounds)),A_ub=Aub,b_ub=bub,
                       A_eq=Abar[support],b_eq=bbar[support],bounds=bounds,
                       method="highs",
                       options={"primal_feasibility_tolerance":1e-9,
                                "dual_feasibility_tolerance":1e-9})
        report={"grid":grid,"candidates":len(candidates),"lp_status":int(result.status),
                "lp_message":result.message}
        if result.success:
            exact=None;reconstruction_attempts=[]
            for tolerance in (1e-8,1e-7,1e-6,1e-5):
                exact,detail=rational_from_lp(
                    patterns,candidates,Abar,bbar,scales,result,support,tolerance,
                    Fraction(str(args.seed_min_weight)))
                detail["tight_tolerance"]=tolerance
                reconstruction_attempts.append(detail)
                if exact is not None: break
            report.update(detail)
            report["exact_rationalization_attempts"]=reconstruction_attempts
            if exact is not None:
                cert=make_certificate(patterns,candidates,exact,report)
                pending=args.output.with_suffix(".pending.json")
                atomic_json(pending,cert)
                verification=verify_certificate(pending,args.data_dir)
                cert["verification"]=verification
                atomic_json(args.output,cert);pending.unlink()
                report["seconds"]=time.time()-start;attempts.append(report)
                atomic_json(ROOT/"results"/"rationalization_report.json",
                            {"status":"verified_exact","attempts":attempts,"verification":verification})
                print(json.dumps(verification,indent=2));return
        report["seconds"]=time.time()-start;attempts.append(report)
        print(json.dumps(report,indent=2),flush=True)
        atomic_json(ROOT/"results"/"rationalization_report.json",
                    {"status":"not_verified","attempts":attempts})
    raise SystemExit("No exact certificate passed. Discovery diagnostics saved; no proof certificate emitted.")


if __name__=="__main__":
    if hasattr(sys,"set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    main()
