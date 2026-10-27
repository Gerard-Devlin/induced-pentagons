#!/usr/bin/env python3
"""Build each paper edition in an isolated directory and atomically commit it.

This prevents a partial compiler write or a concurrent build from replacing
a previously usable PDF. A PDF must pass pdfinfo and the final LaTeX log
must have no undefined references or overfull boxes before it is delivered.
"""

import _bootstrap  # local CLI module paths only
import argparse, json, os, shutil, subprocess, tempfile
from pathlib import Path
from latex_toolchain import latexmk_command
ROOT=Path(__file__).resolve().parents[1]

def atomic(path,contents):
    path.parent.mkdir(parents=True,exist_ok=True);tmp=path.with_suffix(path.suffix+'.pending')
    tmp.write_bytes(contents);os.replace(tmp,path)

def build(edition):
    source=ROOT/'paper';logs=ROOT/'logs';logs.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='pentagon-paper-') as name:
        work=Path(name)
        for p in source.iterdir():
            if p.is_file() and p.suffix in ('.tex','.bib','.bst','.sty','.cls'):shutil.copyfile(p,work/p.name)
        shutil.copytree(source/'figures',work/'figures')
        result=subprocess.run(latexmk_command(edition+'.tex'),
                              cwd=work,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        atomic(logs/f'build_{edition}.txt',result.stdout)
        if result.returncode:raise RuntimeError(f'{edition}: compiler failed; see logs/build_{edition}.txt')
        final_log=(work/f'{edition}.log').read_text(errors='replace')
        atomic(logs/f'{edition}_final.log',final_log.encode())
        for bad in ('Overfull','undefined references','Citation `','LaTeX Error:'):
            if bad in final_log:raise RuntimeError(f'{edition}: final log contains {bad!r}')
        pdf=work/f'{edition}.pdf'
        info=subprocess.run(['pdfinfo',str(pdf)],capture_output=True,text=True,check=True)
        if 'Syntax Error' in info.stderr:raise RuntimeError(f'{edition}: PDF structure is invalid')
        pages=next(int(x.split(':',1)[1]) for x in info.stdout.splitlines() if x.startswith('Pages:'))
        atomic(source/pdf.name,pdf.read_bytes())
        for suffix in ('.bbl',):
            p=work/(edition+suffix)
            if p.exists():atomic(source/p.name,p.read_bytes())
        check=subprocess.run(['pdfinfo',str(source/pdf.name)],capture_output=True,text=True,check=True)
        if 'Syntax Error' in check.stderr:raise RuntimeError('Committed PDF did not pass readback')
        return {'edition':edition,'pages':pages,'bytes':pdf.stat().st_size,'status':'built_and_readback_verified'}

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--edition',choices=['main','submission','both'],default='both')
    a=ap.parse_args();editions=['main','submission'] if a.edition=='both' else [a.edition]
    for e in editions:print(json.dumps(build(e)),flush=True)
