#!/usr/bin/env python3
"""Check every distributed file against the archive manifest; no integrations."""
import hashlib,json
from pathlib import Path

root=Path(__file__).resolve().parent
manifest=json.loads((root/'package-manifest.json').read_text())
for name,item in manifest['files'].items():
    p=root/name
    if not p.resolve().is_relative_to(root):raise ValueError('Manifest path escapes package')
    if getattr(p.stat(),'st_flags',0)&0x40000000:raise RuntimeError('Online-only input refused: '+name)
    if p.stat().st_size!=item['bytes'] or hashlib.sha256(p.read_bytes()).hexdigest()!=item['sha256']:raise ArithmeticError('File differs: '+name)
print(json.dumps({'status':'PASS_PACKAGE_FILE_INTEGRITY','files':len(manifest['files']),'integrations_repeated':False}))
