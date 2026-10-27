#!/usr/bin/env python3
"""Remove a supplied name from PDF text and metadata, checking other text.

Requires pypdf only for this document utility, not for mathematical checking.
"""
from pathlib import Path
import argparse
import json
from pypdf import PdfReader, PdfWriter
from pypdf.generic import ContentStream, TextStringObject, NameObject


def normalized(text):
    return ''.join(text.split()).upper()


def anonymize(source, destination, name):
    target = normalized(name)
    if not target:
        raise ValueError('A nonempty name is required')
    reader = PdfReader(source)
    expected = [normalized(p.extract_text() or '').replace(target, '') for p in reader.pages]
    writer = PdfWriter()
    writer.clone_document_from_reader(reader)
    removed = 0
    for page in writer.pages:
        stream = ContentStream(page.get_contents(), writer)
        for operands, operator in stream.operations:
            if operator not in (b'Tj', b'TJ'):
                continue
            pieces = operands[0] if operator == b'TJ' else operands
            index, characters = [], []
            for i, piece in enumerate(pieces):
                if isinstance(piece, str):
                    for j, char in enumerate(piece):
                        if not char.isspace():
                            characters.append(char.upper())
                            index.append((i, j))
            combined = ''.join(characters)
            start = combined.find(target)
            if start < 0:
                continue
            if combined.replace(target, '').strip('0123456789'):
                raise ValueError('Name shares an operator with other text; review manually')
            omit = set(index[start:start + len(target)])
            for i, piece in enumerate(pieces):
                if isinstance(piece, str):
                    pieces[i] = TextStringObject(''.join(c for j, c in enumerate(piece) if (i, j) not in omit))
            removed += 1
        page[NameObject('/Contents')] = writer._add_object(stream)
    metadata = {str(k): str(v) for k, v in (reader.metadata or {}).items()
                if str(k) != '/Author' and target not in normalized(str(v))}
    metadata['/Author'] = ''
    writer.add_metadata(metadata)
    writer._root_object.pop('/Metadata', None)
    writer.compress_identical_objects(remove_identicals=True, remove_orphans=True)
    with Path(destination).open('wb') as output:
        writer.write(output)
    check = PdfReader(destination)
    actual = [normalized(p.extract_text() or '') for p in check.pages]
    assert actual == expected and not any(target in text for text in actual)
    assert not any(target in normalized(str(v)) for v in (check.metadata or {}).values())
    return {'status': 'PASS', 'pages': len(actual), 'text_operators_cleaned': removed,
            'all_other_page_text_preserved': True, 'author_metadata_empty': True}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--name', required=True)
    args = parser.parse_args()
    print(json.dumps(anonymize(args.input, args.output, args.name)))
