#!/usr/bin/env python3
"""Write MinCostFlow.lean so that it imports every file under MinCostFlow/. With --check, only report."""
import pathlib, sys
root = pathlib.Path(__file__).resolve().parent.parent
mods = sorted('.'.join(p.relative_to(root).with_suffix('').parts)
              for p in (root / 'MinCostFlow').rglob('*.lean'))
text = 'module\n\n' + ''.join(f'public import {m}\n' for m in mods)
out = root / 'MinCostFlow.lean'
if '--check' in sys.argv:
    if not out.exists() or out.read_text() != text:
        sys.exit('MinCostFlow.lean does not import exactly the files under MinCostFlow/; run tools/gen_root.py')
else:
    out.write_text(text)
    print(f'{len(mods)} modules')
