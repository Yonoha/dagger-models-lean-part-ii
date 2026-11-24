"""Regenerate the source/evidence inventory without changing any proof source."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
sources = {p.relative_to(root).as_posix(): sha(p)
    for p in sorted((root / 'lean').rglob('*.lean'))}
evidence = {p.relative_to(root).as_posix(): sha(p)
    for p in sorted((root / 'verification').rglob('*')) if p.is_file()}
manifest = dict(format_version=1, sources=sources, evidence_files=evidence,
    note='Inventory of this exported snapshot; saved proof receipts retain original verified source hashes.')
(root / 'SOURCE_MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(lean_sources=len(sources), evidence_files=len(evidence))))
