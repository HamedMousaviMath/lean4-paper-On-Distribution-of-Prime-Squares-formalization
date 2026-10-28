#!/usr/bin/env python3
"""Ask Lean for every project theorem's transitive axioms and enforce a whitelist."""
from pathlib import Path
import re
import subprocess
import sys

from check_source import code_only

ROOT = Path(__file__).resolve().parents[1]
spec = (ROOT / 'scripts/CheckAxioms.lean').read_text()
names = re.findall(r'^#print axioms (\S+)', spec, flags=re.M)
expected = set()
for path in (ROOT / 'PrimeSquares').rglob('*.lean'):
    # All current modules declare their results directly in namespace PrimeSquares.
    # Refuse a missing audit request when adding a theorem, rather than relying
    # on a fixed count inherited from the initial starter.
    for name in re.findall(r'^(?:theorem|lemma)\s+(\w+)', code_only(path.read_text()), flags=re.M):
        expected.add('PrimeSquares.' + name)
if set(names) != expected or len(set(names)) != len(names):
    raise SystemExit(f'Audit requests must cover every theorem exactly once. '
                     f'Missing: {sorted(expected - set(names))}; '
                     f'extra: {sorted(set(names) - expected)}')
result = subprocess.run(['lake', 'env', 'lean', 'scripts/CheckAxioms.lean'],
                        cwd=ROOT, text=True, stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT)
print(result.stdout, end='')
if result.returncode:
    raise SystemExit(result.returncode)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name in names:
    pattern = (r"'" + re.escape(name) +
               r"' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])")
    match = re.search(pattern, result.stdout, flags=re.S)
    if not match:
        raise SystemExit(f'FAIL: missing or unrecognized Lean audit output for {name}')
    axioms = {x.strip() for x in (match.group(1) or '').split(',') if x.strip()}
    if axioms - allowed:
        raise SystemExit(f'FAIL: unapproved axioms for {name}: {sorted(axioms - allowed)}')
print(f'PASS: all {len(names)} project theorem declarations audited; '
      'only standard Lean axioms occur.')
