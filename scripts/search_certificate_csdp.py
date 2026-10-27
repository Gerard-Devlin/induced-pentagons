#!/usr/bin/env python3
"""CSDP/SDPA discovery route for the missing rational pentagon certificate.

This is numerical discovery only. It never emits a verified certificate.
The official CSDP source and build details are recorded in audit/csdp_build.txt.
"""
from __future__ import annotations

import _bootstrap  # local CLI module paths only
import argparse
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import time
import numpy as np

ROOT=Path(__file__).resolve().parents[1]
TAU=5/663552


def atomic_npz(path,**arrays):
    buf=io.BytesIO();np.savez_compressed(buf,**arrays)
    tmp=path.with_suffix(".npz.tmp");tmp.write_bytes(buf.getvalue())
    os.replace(tmp,path)
    with np.load(path) as check:
        for key in check.files: _=check[key]


def export_problem(work,triangle=False,trace_penalty=1e-14,free_penalty=1e-12):
    p=np.load(ROOT/"certificates/pattern_columns.npz")
    s=np.load(ROOT/"certificates/symmetry_blocks.npz")
    assert np.array_equal(p["host_masks"],s["host_masks"])
    groups=[str(g) for g in s["group_names"]
            if triangle or str(s["group_owner_"+str(g)])!="triangle3"]
    matrices={g:s["group_M_"+g] for g in groups}
    sizes=[matrices[g].shape[1] for g in groups]
    free=p["free_columns"];positive=p["positive_columns"]
    fs=np.maximum(np.max(np.abs(free),axis=0),1e-15)
    ps=np.maximum(np.max(np.abs(positive),axis=0),1e-15)
    fn=free/fs;pn=positive/ps
    # All entries below are zero-based internally; SDPA indices are one-based.
    offset_slacks=0
    offset_positive=1044
    offset_freeplus=1048
    offset_freeminus=1085
    offset_delta=1122
    offset_bounds=1123
    diag_size=1127
    db=len(groups)+1
    rhs=np.r_[p["target"]/TAU,-115.699,-1e-5,-1e-5,310.001]
    datafile=work/"pentagon.dat-s"
    with datafile.open("w") as out:
        out.write('"New pentagon certificate discovery; numerical input only"\n')
        out.write("1048\n")
        out.write(f"{len(groups)+1}\n")
        out.write(" ".join(map(str,sizes+[-diag_size]))+"\n")
        out.write(" ".join(f"{x:.18e}" for x in rhs)+"\n")
        def emit(k,b,i,j,value):
            if abs(value)>1e-17:
                out.write(f"{k} {b} {i+1} {j+1} {value:.18e}\n")
        # CSDP maximizes tr(CX). We minimize relaxation with a tiny trace and
        # free-split regularization; both are discovery-only choices.
        for b,(g,n) in enumerate(zip(groups,sizes),1):
            mult=int(s["group_multiplicity_"+g])
            for i in range(n): emit(0,b,i,i,-trace_penalty*mult)
        emit(0,db,offset_delta,offset_delta,-1)
        for j in range(74):
            emit(0,db,offset_freeplus+j,offset_freeplus+j,-free_penalty)
        for h in range(1044):
            k=h+1
            for b,(g,n) in enumerate(zip(groups,sizes),1):
                M=matrices[g][h]
                for i in range(n):
                    for j in range(i,n): emit(k,b,i,j,float(M[i,j]))
            emit(k,db,offset_slacks+h,offset_slacks+h,1)
            emit(k,db,offset_delta,offset_delta,-1)
            for j in range(4):
                emit(k,db,offset_positive+j,offset_positive+j,float(pn[h,j]))
            for j in range(37):
                v=float(fn[h,j])
                emit(k,db,offset_freeplus+j,offset_freeplus+j,v)
                emit(k,db,offset_freeminus+j,offset_freeminus+j,-v)
        # lambda1 - lower_slack = -115.699
        # lambda1 + upper_slack = -1e-5
        # lambda3 + upper_slack = -1e-5
        # lambda2 + lambda3 - lower_slack = 310.001
        for r,j,slacksign in ((0,0,-1),(1,0,1),(2,2,1)):
            k=1045+r;v=TAU/fs[j]
            emit(k,db,offset_freeplus+j,offset_freeplus+j,v)
            emit(k,db,offset_freeminus+j,offset_freeminus+j,-v)
            emit(k,db,offset_bounds+r,offset_bounds+r,slacksign)
        for j in (1,2):
            v=TAU/fs[j]
            emit(1048,db,offset_freeplus+j,offset_freeplus+j,v)
            emit(1048,db,offset_freeminus+j,offset_freeminus+j,-v)
        emit(1048,db,offset_bounds+3,offset_bounds+3,-1)
    metadata={
        "status":"numerical_discovery_input","groups":groups,"sizes":sizes,
        "diagonal_block":db,"diagonal_size":diag_size,
        "offsets":{"slacks":offset_slacks,"positive":offset_positive,
                   "freeplus":offset_freeplus,"freeminus":offset_freeminus,
                   "delta":offset_delta,"bounds":offset_bounds},
        "free_scaling":fs.tolist(),"positive_scaling":ps.tolist(),
        "host_equation_scale":TAU,"triangle":triangle,
        "trace_penalty":trace_penalty,
        "free_penalty":free_penalty,
    }
    (work/"metadata.json").write_text(json.dumps(metadata,indent=2)+"\n")
    print(f"Exported {datafile.stat().st_size/1e6:.1f} MB, "
          f"1048 equalities, PSD blocks {sizes}, diagonal {diag_size}",flush=True)
    return datafile,metadata


def parse_solution(work,path,metadata,output=None):
    p=np.load(ROOT/"certificates/pattern_columns.npz")
    s=np.load(ROOT/"certificates/symmetry_blocks.npz")
    groups=metadata["groups"];sizes=metadata["sizes"]
    blocks=[np.zeros((n,n)) for n in sizes]
    diagonal=np.zeros(metadata["diagonal_size"])
    with path.open() as inp:
        dual=np.array([float(x) for x in next(inp).split()])
        assert len(dual)==1048
        for line in inp:
            if not line.strip(): continue
            which,b,i,j,value=line.split()
            if int(which)!=2: continue
            b,i,j=int(b)-1,int(i)-1,int(j)-1;value=float(value)
            if b==len(groups):
                assert i==j;diagonal[i]=value
            else: blocks[b][i,j]=blocks[b][j,i]=value
    off=metadata["offsets"]
    sf=diagonal[off["freeplus"]:off["freeplus"]+37]-diagonal[off["freeminus"]:off["freeminus"]+37]
    lam=TAU*sf/np.array(metadata["free_scaling"])
    apos=TAU*diagonal[off["positive"]:off["positive"]+4]/np.array(metadata["positive_scaling"])
    delta=TAU*diagonal[off["delta"]]
    data={"lambda_free":lam,"a_positive":apos,"delta":np.array(delta),
          "scaled_delta":np.array(diagonal[off["delta"]]),"csdp_dual":dual}
    owners=sorted(set(str(s["group_owner_"+g]) for g in groups))
    combined={}
    for owner in owners:
        U=s["original_U_"+owner];data["U_"+owner]=U
        combined[owner]=np.zeros((U.shape[0],U.shape[0]))
    expression=p["free_columns"]@lam+p["positive_columns"]@apos
    eig={}
    for g,Y in zip(groups,blocks):
        actual=TAU*Y
        expression+=np.einsum("hij,ij->h",s["group_M_"+g],actual)
        owner=str(s["group_owner_"+g])
        for Ucopy in s["group_U_"+g]:
            combined[owner]+=Ucopy@actual@Ucopy.T
        eig[g]=float(np.linalg.eigvalsh(actual).min())
        data["group_X_"+g]=actual
    for owner,G in combined.items():
        U=data["U_"+owner]
        data["X_"+owner]=U.T@G@U
    data["slacks"]=p["target"]+delta-expression
    data["block_names"]=np.array(owners)
    data["solver"]=np.array("CSDP 6.2.0")
    expected=TAU*diagonal[:1044]
    output=Path(output or ROOT/"results/sdp_csdp_solution.npz")
    atomic_npz(output,**data)
    report={
        "solver":"CSDP 6.2.0","numerical_discovery_only":True,
        "delta":float(delta),"scaled_delta":float(diagonal[off["delta"]]),
        "lambda_first3":lam[:3].tolist(),"a_positive":apos.tolist(),
        "slack_min":float(data["slacks"].min()),
        "host_equation_residual_max":float(abs(data["slacks"]-expected).max()),
        "block_min_eigenvalues":eig,"output":str(output),
    }
    output.with_suffix(".summary.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2),flush=True)
    return report


def main():
    if not __debug__:
        raise RuntimeError("Discovery input checks require assertions; do not use Python -O, -OO, or PYTHONOPTIMIZE.")
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--solver",default=shutil.which("csdp") or "/tmp/pentagon_csdp/solver/csdp")
    ap.add_argument("--triangle",action="store_true")
    ap.add_argument("--max-iter",type=int,default=150)
    ap.add_argument("--threads",type=int,default=2)
    ap.add_argument("--export-only",action="store_true")
    ap.add_argument("--parse-only",action="store_true")
    ap.add_argument("--trace-penalty",type=float,default=1e-14)
    ap.add_argument("--free-penalty",type=float,default=1e-12)
    ap.add_argument("--warm-start",type=Path)
    ap.add_argument("--output",type=Path,default=ROOT/"results/sdp_csdp_solution.npz")
    ap.add_argument("--work-dir",type=Path,default=ROOT/"results/csdp")
    args=ap.parse_args()
    work=args.work_dir.resolve();work.mkdir(parents=True,exist_ok=True)
    sol=work/"pentagon.sol"
    if args.parse_only:
        metadata=json.loads((work/"metadata.json").read_text())
        parse_solution(work,sol,metadata,args.output);return
    dat,metadata=export_problem(work,args.triangle,args.trace_penalty,args.free_penalty)
    if args.export_only:return
    (work/"param.csdp").write_text(
        f"axtol=1e-9\natytol=1e-9\nobjtol=1e-10\nmaxiter={args.max_iter}\n"
        "printlevel=1\nperturbobj=0\n")
    env=os.environ.copy()
    env["OMP_NUM_THREADS"]=str(args.threads)
    env["OPENBLAS_NUM_THREADS"]=str(args.threads)
    command=[args.solver,str(dat),str(sol)]
    if args.warm_start: command.append(str(args.warm_start.resolve()))
    if shutil.which("stdbuf"): command=["stdbuf","-oL"]+command
    start=time.time()
    result=subprocess.run(command,cwd=work,env=env)
    print(f"CSDP exit {result.returncode}; elapsed {time.time()-start:.1f}s",flush=True)
    if sol.exists(): parse_solution(work,sol,metadata,args.output)
    else: raise SystemExit("CSDP did not produce a numerical solution.")


if __name__=="__main__":
    main()
