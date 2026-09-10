#!/usr/bin/env python3
"""Create a single, checksum-verifiable local archive after full acceptance."""
import argparse,json,zipfile
from pathlib import Path
from verify import HERE,digest,save

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    receipt=json.loads((HERE/'evidence/verification.json').read_text())
    if receipt['status']!='PASS_COMPLETE_EXTERNAL_NUMERICAL_RECOMPUTATION':raise ArithmeticError('Full acceptance required')
    if a.output.resolve().is_relative_to(HERE):raise ValueError('Archive must be outside the package directory')
    files=[p for p in sorted(HERE.rglob('*')) if p.is_file() and '__pycache__' not in p.parts and not p.relative_to(HERE).parts[0].startswith('.') and p.name!='package-manifest.json']
    manifest={str(p.relative_to(HERE)):{'sha256':digest(p),'bytes':p.stat().st_size} for p in files}
    for item in json.loads((HERE/'assembly.json').read_text())['files']:
        if manifest.get('snapshot/prime_gaps_20260903/'+item['path'],{}).get('sha256')!=item['sha256']:raise ArithmeticError('Archive source inventory differs')
    save(HERE/'package-manifest.json',{'status':receipt['status'],'files':manifest})
    with zipfile.ZipFile(a.output,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as archive:
        for p in [*files,HERE/'package-manifest.json']:archive.write(p,'prime-gaps-external-182/'+str(p.relative_to(HERE)))
    with zipfile.ZipFile(a.output) as archive:
        if archive.testzip() is not None:raise ArithmeticError('Archive CRC verification failed')
        import hashlib
        for rel,item in manifest.items():
            if hashlib.sha256(archive.read('prime-gaps-external-182/'+rel)).hexdigest()!=item['sha256']:raise ArithmeticError('Archived file differs '+rel)
    checksum=a.output.with_suffix(a.output.suffix+'.sha256');checksum.write_text(digest(a.output)+'  '+a.output.name+'\n')
    print(json.dumps({'archive':str(a.output.resolve()),'bytes':a.output.stat().st_size,'sha256':digest(a.output),'files':len(files)+1}))
if __name__=='__main__':main()
