#!/usr/bin/env python3
"""Fetch official cached artifacts for the Mathlib modules this project imports."""
from __future__ import annotations

import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / 'formal/paper'


def imported_modules() -> list[str]:
    modules = set()
    for directory, folders, files in os.walk(PAPER):
        folders[:] = [n for n in folders if not n.startswith('.')]
        for name in files:
            if name.endswith('.lean'):
                text = (Path(directory) / name).read_text(encoding='utf-8')
                modules.update(re.findall(r'(?m)^(?:public )?import (Mathlib\.[A-Za-z0-9_.]+)\s*$', text))
    if not modules:
        raise RuntimeError('No direct Mathlib imports found')
    return sorted(modules)


def main():
    lake = shutil.which('lake')
    if lake is None:
        raise SystemExit('Lake is not on PATH. Install formal/paper/lean-toolchain first.')
    os.environ.setdefault('MATHLIB_NO_CACHE_ON_UPDATE', '1')
    modules = imported_modules()
    print(f'Fetching pinned Mathlib cache for {len(modules)} direct imports and their dependencies.', flush=True)
    subprocess.run([lake, 'exe', 'cache', 'get', *modules], cwd=PAPER, check=True)


if __name__ == '__main__':
    main()
