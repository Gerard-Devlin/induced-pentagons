"""Portable local TeX executable discovery; no document content is executed."""

import _bootstrap  # local CLI module paths only
from pathlib import Path
import shutil

def latexmk_command(source, bibliography=True):
    if Path(source).name != source or not source.endswith('.tex'):
        raise ValueError('Expected a LaTeX basename')
    for name in ('latexmk','pdflatex'):
        if shutil.which(name) is None: raise RuntimeError('Missing TeX executable: '+name)
    command=['latexmk','-pdf','-interaction=nonstopmode','-halt-on-error']
    if bibliography:
        program=next((shutil.which(n) for n in ('bibtex','bibtex.original','bibtex8') if shutil.which(n)),None)
        if program is None: raise RuntimeError('Missing BibTeX; install bibtex or use the flattened source.')
        config='"'+program+'" %O %B'
        config=config.replace('\\','\\\\').replace("'","\\'")
        command += ['-e',"$bibtex = '"+config+"';"]
    return command+[source]
