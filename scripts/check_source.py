#!/usr/bin/env python3
"""Reject unfinished proofs and extra assumptions in this project's Lean sources."""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]


def code_only(text):
    """Remove nested Lean block comments, line comments and string contents."""
    out = []
    i = 0
    depth = 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == '\n':
                out.append('\n')
            i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            out.append(' ')
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


def main():
    paths = [ROOT / 'PrimeSquares.lean']
    paths += sorted((ROOT / 'PrimeSquares').rglob('*.lean'))
    paths += sorted((ROOT / 'scripts').glob('*.lean'))
    bad = []
    for path in paths:
        code = code_only(path.read_text())
        hits = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', code)
        if hits:
            bad.append((str(path.relative_to(ROOT)), hits))
    if bad:
        print('FAIL: disallowed source tokens:', bad)
        sys.exit(1)
    print(f'PASS: {len(paths)} Lean files scanned; no proof placeholders, extra axioms, '
          'native_decide or unsafe declarations.')


if __name__ == "__main__":
    main()
