#!/usr/bin/env python3
"""Compile both flattened sources and compare every page with the modular PDFs.

This checks distributable LaTeX completeness and rendered text agreement. It
does not replace visual inspection or certify the mathematics in the prose.
Requires latexmk/pdflatex and Poppler's pdfinfo and pdftotext, no Python packages.
"""

import _bootstrap  # local CLI module paths only
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
from latex_toolchain import latexmk_command

ROOT = Path(__file__).resolve().parents[1]


def page_text(path):
    result = subprocess.run(['pdftotext', '-layout', '-enc', 'UTF-8', str(path), '-'],
                            capture_output=True, text=True, encoding='utf-8', check=True)
    if result.stderr.strip():
        raise RuntimeError(f'{path.name}: PDF text extraction reported {result.stderr}')
    pages = result.stdout.split('\f')
    if pages and not pages[-1].strip():
        pages.pop()
    return [' '.join(page.split()) for page in pages]


def verify():
    records = []
    source = ROOT / 'paper'
    for modular, flat in (('main', 'Induced_pentagons_full_source'),
                          ('submission', 'Induced_pentagons_submission')):
        expected = page_text(source / (modular + '.pdf'))
        with tempfile.TemporaryDirectory(prefix='pentagon-flat-') as name:
            work = Path(name)
            shutil.copy2(source / (flat + '.tex'), work / (flat + '.tex'))
            shutil.copytree(source / 'figures', work / 'figures')
            # The flattened source contains its bibliography. These supporting
            # files are copied only for optional user-specified style packages.
            for suffix in ('.bst', '.sty', '.cls'):
                for path in source.glob('*' + suffix):
                    shutil.copy2(path, work / path.name)
            result = subprocess.run(latexmk_command(flat + '.tex', bibliography=False), cwd=work,
                                    capture_output=True, text=True, encoding='utf-8', errors='replace')
            if result.returncode:
                raise RuntimeError(f'{flat}: independent flattened compile failed\n{result.stdout[-6000:]}')
            log = (work / (flat + '.log')).read_text(errors='replace')
            for bad in ('Overfull', 'undefined references', 'Citation `', 'LaTeX Error:'):
                if bad in log:
                    raise RuntimeError(f'{flat}: final compiler log contains {bad!r}')
            pdf = work / (flat + '.pdf')
            info = subprocess.run(['pdfinfo', str(pdf)], capture_output=True, text=True, check=True)
            if info.stderr.strip():
                raise RuntimeError(f'{flat}: invalid PDF structure: {info.stderr}')
            actual = page_text(pdf)
            if actual != expected:
                mismatches = [i + 1 for i in range(max(len(actual), len(expected)))
                              if i >= len(actual) or i >= len(expected) or actual[i] != expected[i]]
                raise RuntimeError(f'{flat}: flattened/modular text differs on pages {mismatches}')
            records.append({'edition': flat, 'pages': len(actual), 'compile_status': 'PASS',
                            'normalized_page_text_equals_modular_build': True,
                            'flattened_tex_sha256': hashlib.sha256((source / (flat + '.tex')).read_bytes()).hexdigest(),
                            'modular_pdf_sha256': hashlib.sha256((source / (modular + '.pdf')).read_bytes()).hexdigest()})
    return {'status': 'PASS', 'scope': 'Independent compilability and exact pagewise normalized text agreement; mathematical arguments and visual layout require their separate reviews.',
            'editions': records}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'audit' / 'flattened_source_verification.json')
    args = parser.parse_args()
    result = verify()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
