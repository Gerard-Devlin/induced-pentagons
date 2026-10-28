#!/usr/bin/env python3
"""Bind a verification verdict to the source, data, and paper actually shipped.

Hashes detect changes after verification; they are not a digital signature or
a substitute for rerunning the mathematical checks. Numerical discovery and
runtime reports are covered by the archive manifest, not by the proof verdict.
"""
from __future__ import annotations

import _bootstrap  # local CLI module paths only

import hashlib
from pathlib import Path

VERIFIED_STATUS = 'verified_exact_computational_dependencies'
DISCOVERY_DATA = {'symmetry_blocks.npz', 'symmetry_blocks_validation.json'}
STABLE_AUDIT_RECORDS = {'manuscript_inventory.json'}



class VerificationStateError(RuntimeError):
    pass


def tracked_paths(root: Path) -> list[Path]:
    """The immutable inputs and reader-facing artifacts bound by a full run."""
    root = Path(root)
    paths = []
    for name in ('src', 'scripts', 'certificates', 'paper', 'blueprint', 'docs', 'audit', 'formal'):
        base = root / name
        if not base.is_dir():
            continue
        for path in base.rglob('*'):
            if not path.is_file():
                continue
            rel = path.relative_to(base)
            if any(part.startswith('.') or part == '__pycache__' for part in rel.parts):
                continue
            if name in ('src', 'scripts') and path.suffix not in ('.py', '.cpp'):
                continue
            if name == 'audit' and path.suffix != '.py' and path.name not in STABLE_AUDIT_RECORDS:
                continue
            if name == 'certificates' and (path.name in DISCOVERY_DATA or
                                   path.suffix not in ('.json', '.npz', '.tsv', '.txt')):
                continue
            if name == 'paper' and path.suffix not in ('.tex', '.bib', '.bbl', '.bst', '.sty', '.cls', '.pdf', '.png'):
                continue
            if name in ('docs', 'originals') and path.suffix not in ('.txt', '.md', '.json', '.pdf'):
                continue
            if name == 'formal' and path.suffix not in ('.lean', '.toml', '.md', '.json') and path.name != 'lean-toolchain':
                continue
            paths.append(path)
    for pattern in ('README.md', 'verify.py', 'Makefile', 'requirements-*.txt',
                    'LICENSE*', '.gitignore', '.gitattributes', '.github/workflows/*.yml'):
        paths.extend(p for p in root.glob(pattern) if p.is_file())
    return sorted(set(paths), key=lambda p: p.relative_to(root).as_posix())


def fingerprints(root: Path) -> dict[str, str]:
    return {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in tracked_paths(root)}


def verify_current(root: Path, report: dict) -> dict:
    """Fail closed when a PASS is absent or any bound file has changed."""
    if report.get('status') != VERIFIED_STATUS:
        raise VerificationStateError('A complete successful project-verification report is required.')
    recorded = report.get('sha256')
    if not isinstance(recorded, dict) or not recorded:
        raise VerificationStateError('The verification report has no complete file fingerprint map.')
    current = fingerprints(root)
    if current.keys() != recorded.keys():
        added = sorted(current.keys() - recorded.keys())
        removed = sorted(recorded.keys() - current.keys())
        raise VerificationStateError(f'Verification file set is stale: new={added}, missing={removed}. Rerun verify_project.py.')
    changed = [name for name, digest in current.items() if digest != recorded[name]]
    if changed:
        raise VerificationStateError(f'Verification is stale for {changed}. Rerun verify_project.py.')
    return {'status': 'current', 'files_bound': len(current),
            'meaning': 'All bound source, data, manuscript, and documentation bytes match the successful run.'}
