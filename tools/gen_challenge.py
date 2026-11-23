#!/usr/bin/env python3
"""Write the comparator challenge from the three statement files.

    python3 tools/gen_challenge.py OUT            write OUT
    python3 tools/gen_challenge.py --check OUT    exit 1 unless OUT is up to date

Palomar compiles the challenge against Mathlib alone, so the challenge cannot import the
statement files. It repeats them instead: the Mathlib imports of the three files, then the body
of each file (everything after its imports) in the order WordRAM/Model.lean,
MinCostFlow/Statement/Problem.lean, MinCostFlow/Statement/Main.lean, then the theorem with
`sorry`. Comparator then checks that every definition the statement uses is identical in the
challenge and in the library. WordRAM/Model.lean is read from the pinned WordRAM package under
.lake/packages, so run this after Lake has fetched the dependencies.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
IMPORT = re.compile(r'^public import ([\w.]+)$')

HEADER = '''module

{imports}
/-!
# Deterministic almost-linear-time minimum-cost flow: the statement to be proved

The theorem `MinCostFlow.theorem_1_1` is Theorem 1.1 (page 2) of J. van den Brand, L. Chen,
R. Kyng, Y. P. Liu, R. Peng, M. Probst Gutenberg, S. Sachdeva and A. Sidford, *A Deterministic
Almost-Linear Time Algorithm for Minimum-Cost Flow* (arXiv:2309.16629v1). Its conclusion,
`MinCostFlowStatement`, is defined below, over the problem and the machine model.

This file imports only Mathlib, so that it can be checked without the library. It repeats the
files `WordRAM/Model.lean` (of the pinned WordRAM package), `MinCostFlow/Statement/Problem.lean`
and `MinCostFlow/Statement/Main.lean` word for word, without their imports, and
`tools/gen_challenge.py` writes it from them. Comparator checks that every definition used by the
statement is identical here and in the library.

The file `Comparator/Solution.lean` proves the theorem.
-/
'''

PART = '''
-- The file {name}, without its imports.
{body}
end
'''

THEOREM = '''
public section

namespace MinCostFlow

/-- **Theorem 1.1** (Min-cost flow, page 2). There is a deterministic algorithm that, given a
graph with `m` edges, integral demands and capacities bounded by `U` in absolute value and
integral costs bounded by `C` in absolute value, computes an exact minimum-cost flow, or reports
that no flow is feasible, in time `O(n) + m^{1+o(1)} log U log C`. -/
theorem theorem_1_1 : MinCostFlowStatement :=
  sorry

end MinCostFlow
'''


def sources():
    models = sorted(ROOT.glob('.lake/packages/*/WordRAM/Model.lean'))
    if len(models) != 1:
        sys.exit('gen_challenge: WordRAM/Model.lean not found under .lake/packages; '
                 'fetch the dependencies first (for example with `lake exe cache get`)')
    return [('WordRAM/Model.lean', models[0]),
            ('MinCostFlow/Statement/Problem.lean', ROOT / 'MinCostFlow/Statement/Problem.lean'),
            ('MinCostFlow/Statement/Main.lean', ROOT / 'MinCostFlow/Statement/Main.lean')]


def split(name, text):
    """The Mathlib imports and the body (everything after the imports) of one file."""
    lines = text.split('\n')
    if lines[0] != 'module':
        sys.exit(f'gen_challenge: {name} does not start with `module`')
    imports, i = [], 1
    while i < len(lines) and (lines[i] == '' or IMPORT.match(lines[i])):
        m = IMPORT.match(lines[i])
        if m:
            imports.append(m.group(1))
        i += 1
    if any(re.match(r'\s*(public |private |meta )*import ', l) for l in lines[i:]):
        sys.exit(f'gen_challenge: {name} has an import that is not `public import` at the top')
    for m in imports:
        if not (m.startswith('Mathlib.') or m.startswith('WordRAM.')
                or m.startswith('MinCostFlow.Statement.')):
            sys.exit(f'gen_challenge: {name} imports {m}, which is neither Mathlib nor a statement file')
    body = '\n'.join(lines[i:]).rstrip('\n')
    # Each file leaves exactly one section open at its end, which `PART` closes.
    if body.count('\n@[expose] public section\n') != 1:
        sys.exit(f'gen_challenge: {name} must open exactly one `@[expose] public section`')
    return [m for m in imports if m.startswith('Mathlib.')], body


def challenge():
    imports, parts = [], []
    for name, path in sources():
        imps, body = split(name, path.read_text())
        imports += [m for m in imps if m not in imports]
        parts.append(PART.format(name=name, body=body))
    head = HEADER.format(imports=''.join(f'public import {m}\n' for m in imports))
    return head + ''.join(parts) + THEOREM


def main():
    args = [a for a in sys.argv[1:] if a != '--check']
    if len(args) != 1:
        sys.exit(__doc__)
    out = Path(args[0])
    text = challenge()
    if '--check' in sys.argv:
        if not out.exists() or out.read_text() != text:
            sys.exit(f'{out} is not the challenge of the statement files; run tools/gen_challenge.py {out}')
    else:
        out.write_text(text)
        print(f'wrote {out}')


if __name__ == '__main__':
    main()
