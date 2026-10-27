#!/usr/bin/env python3
"""Rebuild exact finite-pattern data used in the replacement flag certificate.

This file does not itself supply positive square coefficients. It builds
the required numerical SDP input from exact integer injection counts and
exports enough information for independent rational verification.

Run from any directory:
    python3 scripts/build_pattern_columns.py
Requires Python 3, NumPy, and a C++17 compiler (g++ by default).
"""
from __future__ import annotations

import _bootstrap  # local CLI module paths only

import argparse
from fractions import Fraction
import hashlib
import io
import itertools
import json
import math
import os
from pathlib import Path
import subprocess

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
PSTAR = Fraction(5, 144)
TAU = Fraction(5, 663552)
KAPPA = TAU / (2 * PSTAR)
EDGES7 = list(itertools.combinations(range(7), 2))
BIT7 = {pair: i for i, pair in enumerate(EDGES7)}


def edge_list(edges):
    return sorted({tuple(sorted(e)) for e in edges})


def mask7(edges):
    return sum(1 << BIT7[e] for e in edge_list(edges))


def falling(n, r):
    return math.factorial(n) // math.factorial(n-r)


def build_specs():
    cycle = [(0,1),(1,2),(2,3),(3,4),(0,4)]
    chords = [(0,2),(0,3),(1,3),(1,4),(2,4)]
    patterns = []
    def add(name, n, edges, nonedges=()):
        e, ne = edge_list(edges), edge_list(nonedges)
        assert not set(e) & set(ne), name
        assert all(0 <= u < v < n for u,v in e+ne), name
        patterns.append(dict(name=name, vertices=n, edges=e, nonedges=ne,
                             denominator=falling(7,n)))
    add("p", 2, [(0,1)])
    add("theta", 5, cycle, chords)
    add("L1", 6, cycle+[(0,5)], chords)
    add("L2", 7, cycle+[(0,5),(0,6)], chords)
    add("L3", 7, cycle+[(0,5),(5,6)], chords)
    add("B1", 3, [(0,1),(0,2)])
    add("B2", 4, [(0,1),(0,2),(0,3)])
    add("B3", 4, [(0,1),(1,2),(2,3)])
    add("L_triangle", 7, cycle+[(0,5),(0,6),(5,6)], chords)
    add("B_triangle", 4, [(0,1),(0,2),(1,2),(0,3)])
    psi = [(0,1),(0,2),(1,2),(0,3),(1,3)]
    ae = [(0,4),(4,5),(5,6),(1,6)]
    an = [(0,5),(0,6),(1,4),(1,5),(4,6)]
    be = [(0,4),(1,4),(1,5),(5,6),(0,6)]
    bn = [(0,5),(4,5),(4,6),(1,6)]
    for i in (0,1):
        pe = psi+([(2,3)] if i else [])
        pn = [] if i else [(2,3)]
        add(f"R{i}", 4, pe, pn)
        add(f"J{i}_A", 7, pe+ae, pn+an)
        add(f"J{i}_B", 7, pe+be, pn+bn)
    tri = [(0,1),(0,2),(1,2)]
    path_edges = [(3,4),(4,5),(5,6)]
    path_nonedges = [(3,5),(3,6),(4,6)]
    add("Jdel_Lg", 7, tri+path_edges+[(0,3),(0,6)],
        path_nonedges+[(0,4),(0,5)])
    # 1-g(j)(1-h(j)) = (1-g(j)) + g(j)h(j). These four
    # terms have disjoint Boolean support; no repeated edge variable occurs.
    for u,v in itertools.product((0,1), repeat=2):
        e = tri+path_edges+[(0,3),(0,6)]
        ne = path_nonedges+[(1,3),(1,6)]
        for j,choice in ((4,u),(5,v)):
            if choice: e += [(0,j),(1,j)]
            else: ne += [(0,j)]
        add(f"Jdel_Lf{u}{v}", 7, e, ne)
    add("Ddel", 4, psi)
    return patterns


def canonical5():
    """Independent exhaustive canonicalization of all 2^10 labelled graphs."""
    pairs = list(itertools.combinations(range(5),2))
    bits = {p:i for i,p in enumerate(pairs)}
    maps = [[bits[tuple(sorted((p[i],p[j])))] for i,j in pairs]
            for p in itertools.permutations(range(5))]
    canonical = []
    for mask in range(1 << 10):
        canonical.append(min(sum(((mask>>src)&1)<<dst
                                 for dst,src in enumerate(mp))
                             for mp in maps))
    representatives = sorted(set(canonical))
    assert len(representatives) == 34
    index = {m:i for i,m in enumerate(representatives)}
    return [index[m] for m in canonical], representatives, pairs


def column_specs():
    cols = {
        "p": {"p":Fraction(1)},
        "theta": {"theta":Fraction(1)},
    }
    for j in (1,2,3):
        cols[f"Phi{j}"] = {f"L{j}":PSTAR, f"B{j}":-TAU}
    cols["PhiTri"] = {"L_triangle":PSTAR, "B_triangle":-TAU}
    for i in (0,1):
        cols[f"Ji{i}"] = {f"J{i}_A":Fraction(1), f"J{i}_B":Fraction(-1),
                          f"R{i}":-KAPPA}
    cols["Jdel"] = {"Jdel_Lg":Fraction(1,2), "Ddel":-KAPPA,
                    **{f"Jdel_Lf{a}{b}":Fraction(-1,2)
                       for a,b in itertools.product((0,1), repeat=2)}}
    return cols


def exact_columns(counts, specs, column_definitions):
    index = {p["name"]:i for i,p in enumerate(specs)}
    numerators, denominators = [], []
    for terms in column_definitions.values():
        coefs = {name:c/specs[index[name]]["denominator"]
                 for name,c in terms.items()}
        den = math.lcm(*(c.denominator for c in coefs.values()))
        num = np.zeros(counts.shape[0], dtype=np.int64)
        for name,c in coefs.items():
            num += counts[:,index[name]]*int(c*den)
        common = math.gcd(den, *(int(x) for x in num))
        numerators.append(num//common)
        denominators.append(den//common)
    return np.column_stack(numerators), np.array(denominators,dtype=np.int64)


def verify_python_rows(hosts, specs, counts):
    """Independently re-enumerate three hosts with Python integer bit tests."""
    samples = sorted({0, len(hosts)//2, len(hosts)-1})
    checks = []
    for row in samples:
        host = int(hosts[row])
        for j,p in enumerate(specs):
            n = p["vertices"]
            actual=0
            for inj in itertools.permutations(range(7),n):
                def edge(u,v):
                    pair = tuple(sorted((inj[u],inj[v])))
                    return (host>>BIT7[pair])&1
                if all(edge(u,v) for u,v in p["edges"]) and all(
                       not edge(u,v) for u,v in p["nonedges"]):
                    actual += 1
            assert actual == int(counts[row,j]), (row,p["name"],actual)
        checks.append(dict(row=row,mask=host,patterns_checked=len(specs)))
    return checks


def main():
    if not __debug__:
        raise RuntimeError("Exact pattern generation requires assertions; do not use Python -O, -OO, or PYTHONOPTIMIZE.")
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--data-dir", type=Path, default=ROOT/"certificates")
    ap.add_argument("--host-masks", type=Path)
    ap.add_argument("--compiler", default="g++")
    ap.add_argument("--skip-python-crosscheck", action="store_true",
                    help="skip the independent three-host Python cross-check")
    args=ap.parse_args()
    data=args.data_dir.resolve();data.mkdir(parents=True,exist_ok=True)
    host_file=(args.host_masks or data/"host_masks.txt").resolve()
    hosts=np.array([int(s) for s in host_file.read_text().split()],dtype=np.int64)
    assert len(hosts)==1044 and len(set(hosts.tolist()))==1044
    assert hosts.tolist()==sorted(hosts.tolist())
    assert hosts[0]==0 and hosts[-1]==(1<<21)-1
    specs=build_specs()
    work=ROOT/".build";work.mkdir(exist_ok=True)
    spec_file=work/"pattern_specs.tsv"
    spec_file.write_text("".join(
        f'{p["name"]} {p["vertices"]} {mask7(p["edges"])} '
        f'{mask7(p["nonedges"])}\n' for p in specs))
    canonical, representatives, pairs5=canonical5()
    canon_file=work/"canonical5_indices.txt"
    canon_file.write_text("\n".join(map(str,canonical))+"\n")
    source=Path(__file__).with_name("pattern_columns.cpp")
    exe=work/"pattern_columns"
    subprocess.run([args.compiler,"-O3","-std=c++17",str(source),"-o",str(exe)],
                   check=True)
    raw=data/"pattern_counts.tsv"
    subprocess.run([str(exe),str(host_file),str(spec_file),str(canon_file),str(raw)],
                   check=True)
    lines=raw.read_text().splitlines()
    nr,npats=map(int,lines[0].split())
    assert nr==len(hosts) and npats==len(specs)
    raw_rows=np.array([list(map(int,s.split())) for s in lines[1:1+nr]],
                      dtype=np.int64)
    assert np.array_equal(raw_rows[:,0],hosts)
    counts=raw_rows[:,1:1+npats]
    induced=raw_rows[:,1+npats:1+npats+34]
    paired=raw_rows[:,1+npats+34:]
    assert induced.shape==paired.shape==(1044,34)
    assert np.all(induced.sum(axis=1)==21)
    assert np.all(paired>=0) and np.all(paired<=induced)
    assert np.array_equal(paired.sum(axis=1),
                          np.array([int(x).bit_count() for x in hosts]))
    homline=lines[-1].split()
    assert homline[0]=="CLEBSCH" and len(homline)==npats+1
    hom=list(map(int,homline[1:]))
    index={p["name"]:i for i,p in enumerate(specs)}
    assert np.array_equal(counts[:,index["R0"]]+counts[:,index["R1"]],
                          counts[:,index["Ddel"]])
    # Four Lf events partition a subset of the profile possibilities.
    lf = sum(counts[:,index[f"Jdel_Lf{a}{b}"]]
             for a,b in itertools.product((0,1),repeat=2))
    assert np.all(lf <= 5040)
    definitions=column_specs()
    nums,dens=exact_columns(counts,specs,definitions)
    values=nums/dens[np.newaxis,:]
    fixed_nums=144*paired-5*induced
    fixed_den=3024
    fixed=fixed_nums/fixed_den
    assert np.max(np.abs(fixed.sum(axis=1)-(values[:,0]-float(PSTAR))))<1e-14
    equality_pattern={p["name"]:Fraction(hom[j],48**p["vertices"])
                      for j,p in enumerate(specs)}
    equality_columns={name:sum(c*equality_pattern[p] for p,c in terms.items())
                      for name,terms in definitions.items()}
    assert equality_columns["p"]==PSTAR
    assert equality_columns["theta"]==TAU
    assert all(equality_columns[name]==0 for name in list(definitions)[2:])
    pychecks=[] if args.skip_python_crosscheck else verify_python_rows(
        hosts,specs,counts)
    positive_names=["PhiTri","Ji0","Ji1","Jdel"]
    free_names=["Phi1","Phi2","Phi3"]
    colnames=list(definitions)
    free=np.column_stack([values[:,colnames.index(n)] for n in free_names]
                          +[fixed])
    positive=np.column_stack([values[:,colnames.index(n)] for n in positive_names])
    theta=values[:,colnames.index("theta")]
    common_den=math.lcm(TAU.denominator,fixed_den,*map(int,dens),140,1260)
    common_nums=nums*(common_den//dens)[np.newaxis,:]
    free_nums=np.column_stack(
        [common_nums[:,colnames.index(n)] for n in free_names]
        +[fixed_nums*(common_den//fixed_den)])
    positive_nums=np.column_stack(
        [common_nums[:,colnames.index(n)] for n in positive_names])
    target_nums=int(TAU*common_den)-common_nums[:,colnames.index("theta")]
    assert np.max(np.abs(free_nums/common_den-free))<1e-14
    assert np.max(np.abs(positive_nums/common_den-positive))<1e-14
    npz_buffer=io.BytesIO()
    np.savez_compressed(
        npz_buffer,
        host_masks=hosts,
        pattern_names=np.array([p["name"] for p in specs]),
        pattern_counts=counts,
        pattern_denominators=np.array([p["denominator"] for p in specs]),
        column_names=np.array(colnames), columns=values,
        column_numerators=nums, column_denominators=dens,
        fixed_density_numerators=fixed_nums,
        fixed_density_denominator=np.array(fixed_den),
        fixed_density=fixed, fixed_density_graph_masks=np.array(representatives),
        fixed_density_induced_counts=induced,
        fixed_density_complement_edge_counts=paired,
        free_columns=free,
        free_names=np.array(free_names+[f"density_{m}" for m in representatives]),
        positive_columns=positive,positive_names=np.array(positive_names),
        target=float(TAU)-theta,theta=theta,p=values[:,0],
        pstar=np.array(float(PSTAR)),tau=np.array(float(TAU)),
        common_denominator=np.array(common_den),
        free_numerators=free_nums,positive_numerators=positive_nums,
        target_numerators=target_nums,
    )
    npz_path=data/"pattern_columns.npz"
    npz_temporary=data/"pattern_columns.npz.tmp"
    npz_temporary.write_bytes(npz_buffer.getvalue())
    os.replace(npz_temporary,npz_path)
    with np.load(npz_path) as check:
        for key in check.files:
            _=check[key]
    obj={
        "schema":"pentagon-pattern-columns-v1",
        "status":"exact_pattern_data; not a proof certificate",
        "source":"Manuscript Sections 2.2, 2.3 and 4.1--4.2",
        "normalization":{"pstar":str(PSTAR),"tau":str(TAU),"kappa":str(KAPPA),
                         "pattern_density":"injection_count/(7)_r",
                         "all_columns_common_denominator":common_den,
                         "common_denominator_also_clears_flag_140_and_1260":True},
        "host_order":{"count":len(hosts),"mask_pairs":EDGES7,
                      "masks":hosts.tolist(),
                      "host_masks_sha256":hashlib.sha256(host_file.read_bytes()).hexdigest()},
        "patterns":[{**p,"injection_counts":counts[:,j].tolist(),
                     "clebsch_homomorphism_count":hom[j],
                     "clebsch_reference_density":str(equality_pattern[p["name"]])}
                    for j,p in enumerate(specs)],
        "columns":[{"name":name,"terms":{k:str(v) for k,v in terms.items()},
                    "numerators":nums[:,j].tolist(),"denominator":int(dens[j]),
                    "clebsch_reference_value":str(equality_columns[name])}
                   for j,(name,terms) in enumerate(definitions.items())],
        "fixed_density":{
            "description":"p_F*t(K2)-pstar*p_F; five-set and complementary pair disjoint",
            "graphs":[{"mask":m,"edges":[e for b,e in enumerate(pairs5) if (m>>b)&1]}
                      for m in representatives],
            "induced_counts":induced.tolist(),"complement_edge_counts":paired.tolist(),
            "subset_denominator":21,"column_denominator":fixed_den,
            "column_numerators":fixed_nums.tolist(),
            "basis_note":"34 five-graph density identities; their sum is p-pstar."
        },
        "checks":{"host_count":True,"complete_and_empty_hosts":True,
                  "subset_count_21":True,"paired_counts_sum_to_host_edges":True,
                  "R0_plus_R1_equals_Ddel":True,
                  "all_reference_variational_columns_zero":True,
                  "independent_python_crosscheck":pychecks},
    }
    (data/"pattern_columns.json").write_text(json.dumps(obj,separators=(",",":"))+"\n")
    report={
        "status":"passed","host_rows":1044,"patterns":npats,
        "free_columns":37,"nonnegative_variational_columns":4,
        "reference_p":str(equality_columns["p"]),
        "reference_theta":str(equality_columns["theta"]),
        "independent_python_checks":pychecks,
        "missing":"Positive flag-square certificate coefficients and span witnesses remain separate inputs."
    }
    (data/"pattern_columns_validation.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2))


if __name__=="__main__":
    main()
