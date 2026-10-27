#!/usr/bin/env python3
"""Exhaust all 2^16 neighborhoods, using two independent loop organizations."""
from __future__ import annotations

import _bootstrap  # local CLI module paths only
import argparse, json, hashlib
from pathlib import Path
from clebsch_core import *


def run() -> dict:
    if not __debug__:raise RuntimeError('Exact profile verification requires assertions enabled.')
    counts=all_profile_counts()
    degree_max=[0]*17
    eq12=[];eq60=[]
    for mask,c in enumerate(counts):
        # Independent direct scan of the 480 induced paths.
        d=profile_count_direct(mask)
        assert c==d, (mask,c,d)
        degree=mask.bit_count()
        degree_max[degree]=max(degree_max[degree],c)
        assert c<=12*degree and 5*c<=12*degree**2 and c<=60
        if c==12*degree: eq12.append(mask)
        if c==60: eq60.append(mask)
    assert degree_max==[0,0,6,18,36,60,60,54,48,44,42,35,25,18,12,0,0]
    assert set(eq12)=={0,*ADJ}
    assert set(eq60)==set(ADJ)|{ADJ[u]|(1<<u) for u in range(16)}
    return {'status':'PASS','scope':'Boolean profile identities; multilinear extension follows analytically',
            'profiles_checked':65536,'paths':480,'degreewise_maxima':degree_max,
            'equality_c_equals_12d':eq12,'equality_c_equals_60':eq60,
            'counts_sha256':hashlib.sha256(bytes(counts)).hexdigest()}


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,default=Path('results/profile_checks.json'))
    args=ap.parse_args();r=run();args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
