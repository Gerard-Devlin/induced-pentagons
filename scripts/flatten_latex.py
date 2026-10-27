#!/usr/bin/env python3
"""Produce one editable .tex file while keeping the modular source canonical."""

import _bootstrap  # local CLI module paths only
from pathlib import Path
import re

def main():
    root=Path(__file__).resolve().parents[1]/'paper'
    text=(root/'main.tex').read_text()
    def replace(m):
        name=m.group(1)
        p=root/(name+'.tex')
        if not p.exists():return m.group(0) # optional author_metadata.tex
        return '\n% BEGIN source: '+name+'\n'+p.read_text()+'\n% END source: '+name+'\n'
    text=re.sub(r'\\input\{([^}]+)\}',replace,text)
    bbl=root/'main.bbl'
    if bbl.exists():
        text=re.sub(r'(\\bibliographystyle\{[^}]+\})\s*\\bibliography\{[^}]+\}',lambda m:m.group(1)+'\n'+bbl.read_text(),text)
    (root/'Induced_pentagons_full_source.tex').write_text(text)
    (root/'Induced_pentagons_submission.tex').write_text('\\def\\SubmissionBuild{1}\n'+text)
    print('Wrote both flattened LaTeX editions (figure remains in the accompanying figures folder).')

if __name__=='__main__':main()
