#!/usr/bin/env python3
"""Reject proof escapes outside the standalone comparator Challenges."""
import pathlib,re,runpy,sys
root=pathlib.Path(__file__).resolve().parents[1]
mask=runpy.run_path(str(root/'scripts/check_lean_modules.py'))['code_mask']
failed=[]
for path in sorted(root.rglob('*.lean')):
    rel=path.relative_to(root)
    if '.lake' in rel.parts or '.git' in rel.parts: continue
    allowed=rel.parts[:1]==('comparators',) and path.name=='Challenge.lean'
    pattern=r'\b(?:admit|native_decide|axiom)\b' if allowed else r'\b(?:sorry|admit|native_decide|axiom)\b'
    for m in re.finditer(pattern,mask(path.read_text())):
        failed.append(f"{rel}:{path.read_text()[:m.start()].count(chr(10))+1}: {m.group()}")
print('\n'.join(failed) if failed else 'PASS: no proof escapes outside comparator Challenges')
sys.exit(bool(failed))
