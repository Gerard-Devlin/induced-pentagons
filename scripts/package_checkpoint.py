#!/usr/bin/env python3
"""Make a self-contained, checksummed proof package without search caches."""

import _bootstrap  # local CLI module paths only
import argparse, hashlib, json, os, zipfile
from pathlib import Path
from release_integrity import VERIFIED_STATUS, VerificationStateError, verify_current
ROOT=Path(__file__).resolve().parents[1]

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--label',required=True)
    ap.add_argument('--require-verified',action='store_true',
                    help='Refuse to package unless a complete PASS binds all current release inputs.')
    a=ap.parse_args()
    if not a.label or not all(c.isalnum() or c in '_-' for c in a.label):
        raise ValueError('Label must use letters, digits, underscores, or hyphens.')
    if not __debug__:
        raise RuntimeError('Archive verification refuses disabled assertions.')
    verification_path=ROOT/'results/verification_manifest.json'
    verification=json.loads(verification_path.read_text()) if verification_path.exists() else {}
    required=a.require_verified or a.label.startswith(('verified','reviewed','release','final'))
    current={'status':'incomplete'}
    if verification.get('status')==VERIFIED_STATUS or required:
        try:
            current=verify_current(ROOT,verification)
        except VerificationStateError as exc:
            if required:raise
            current={'status':'stale','reason':str(exc)}
    out=ROOT.parent/f'Induced_Pentagons_{a.label}.zip'
    excluded_suffixes={'.aux','.blg','.fdb_latexmk','.fls','.out','.pyc','.so','.dat-s','.sol','.tmp','.log','.pending'}
    records={}
    for p in sorted(ROOT.rglob('*')):
        rel=p.relative_to(ROOT)
        if not p.is_file():continue
        repository_metadata = (rel.as_posix() in {'.gitignore', '.gitattributes'} or
                               rel.parts[0] == '.github')
        if not repository_metadata and any(part.startswith('.') or part=='__pycache__' for part in rel.parts):continue
        if p.suffix in excluded_suffixes or p.name.endswith('.pending.json'):continue
        if rel.parts[0] in {'logs','tmp','manuscript'}:continue
        if rel.as_posix()==f'audit/{a.label}_manifest.json':continue
        if p.name in {'symmetry_blocks.npz','CHECKPOINT_MANIFEST.json'}:continue
        if p.name in {'upper_bound_certificate_v1.json','sdp_csdp_solution.npz','sdp_solution.npz'}:continue
        records[rel.as_posix()]=p.read_bytes()
    manifest={'schema':'induced-pentagons.proof-package.v1','label':a.label,
              'status':VERIFIED_STATUS if current['status']=='current' else current['status'],
              'verification_freshness':current,
              'proof_scope':'Exact computational dependencies; analytic arguments are given in the manuscript.',
              'omitted_reproducible_caches':['certificates/symmetry_blocks.npz','SDPA exports and raw solver solutions','build products and live logs','superseded numeric and first upper-bound checkpoints'],
              'files':[{'path':name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
                       for name,b in records.items()]}
    mb=(json.dumps(manifest,indent=2)+'\n').encode()
    records['CHECKPOINT_MANIFEST.json']=mb
    tmp=out.with_suffix('.pending.zip')
    with zipfile.ZipFile(tmp,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
        for name,b in records.items():z.writestr('pentagons/'+name,b)
    with zipfile.ZipFile(tmp) as z:
        assert z.testzip() is None
        for r in manifest['files']:
            assert hashlib.sha256(z.read('pentagons/'+r['path'])).hexdigest()==r['sha256']
    os.replace(tmp,out)
    (ROOT/'audit'/f'{a.label}_manifest.json').write_bytes(mb)
    print(json.dumps({'path':str(out),'bytes':out.stat().st_size,'files':len(records),
                      'sha256':hashlib.sha256(out.read_bytes()).hexdigest()},indent=2))

if __name__=='__main__':main()
