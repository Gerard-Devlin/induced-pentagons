"""Strict JSON loading and exact rational fields for proof verifiers.

The parser rejects duplicate object keys and non-JSON numeric constants.
Rational proof fields may be strings or exact JSON integers; binary floats
and booleans are rejected. Ordinary finite discovery metadata may use floats.
This module contains no combinatorial counting or certificate arithmetic.
"""

import _bootstrap  # local CLI module paths only
from fractions import Fraction
from pathlib import Path
import json


def load_proof_json(path):
    path = Path(path)

    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f'{path.name}: duplicate JSON key {key!r}')
            result[key] = value
        return result

    def reject_constant(value):
        raise ValueError(f'{path.name}: invalid JSON numeric constant {value}')

    return json.loads(path.read_text(encoding='utf-8'), object_pairs_hook=unique_object,
                      parse_constant=reject_constant)


def exact_fraction(value, location):
    if type(value) not in (str, int):
        raise ValueError(f'{location}: rational proof fields must be strings or exact integers, not {type(value).__name__}')
    try:
        return Fraction(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError(f'{location}: invalid rational coefficient') from exc
