"""Make the adjacent verifier and script modules available to direct CLI runs."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
for directory in ('src', 'scripts'):
    location = str(ROOT / directory)
    if location not in sys.path:
        sys.path.append(location)
