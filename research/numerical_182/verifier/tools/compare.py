"""Compare all mathematical payloads, separately checking current dependency hashes."""
import hashlib, json
from pathlib import Path

# These are provenance or timing fields, not mathematical inputs or endpoints.
OMIT={'seconds','timings','runtime','input_sha256','implementation_sha256','origin_sha256','coefficient_archive_sha256','reused_from'}
def canonical(value):
    if isinstance(value,dict):return {k:canonical(v) for k,v in value.items() if k not in OMIT}
    if isinstance(value,list):return [canonical(v) for v in value]
    if isinstance(value,str) and value.startswith('/') and 'prime_gaps_20260903/' in value:
        return value.split('prime_gaps_20260903/',1)[1].removeprefix('rebuilt/')
    return value
def differences(a,b,path=''):
    if type(a)!=type(b):return [path+': type differs']
    if isinstance(a,dict):
        out=[path+': key set differs'] if a.keys()!=b.keys() else []
        for key in a.keys()&b.keys():out+=differences(a[key],b[key],path+'/'+key)
        return out
    if isinstance(a,list):
        if len(a)!=len(b):return [path+': length differs']
        return [d for i,(x,y) in enumerate(zip(a,b)) for d in differences(x,y,path+'/'+str(i))]
    return [] if a==b else [path+': value differs']
def check(stage,root):
    actual=json.loads((root/stage['output']).read_text());reference=json.loads((root/stage['reference']).read_text())
    diff=differences(canonical(reference),canonical(actual))
    hashes=0
    for key in ['input_sha256','implementation_sha256','origin_sha256']:
        for name,expected in actual.get(key,{}).items():
            p=Path(name)
            if p.is_absolute() and 'prime_gaps_20260903/' in str(p):p=root/str(p).split('prime_gaps_20260903/',1)[1]
            elif not p.is_absolute():p=root/p
            if not p.resolve().is_relative_to(root.resolve()):raise ArithmeticError('Foreign dependency '+name)
            if hashlib.sha256(p.read_bytes()).hexdigest()!=expected:raise ArithmeticError('Fresh dependency hash mismatch '+name)
            hashes+=1
    array_count=0
    if stage.get('archive'):
        import numpy as np
        fresh=root/Path(stage['output']).with_suffix('.npz');old=root/Path(stage['reference']).with_suffix('.npz')
        if hashlib.sha256(fresh.read_bytes()).hexdigest()!=actual['coefficient_archive_sha256']:raise ArithmeticError('Fresh archive checksum mismatch')
        with np.load(fresh,allow_pickle=False) as a,np.load(old,allow_pickle=False) as b:
            if set(a.files)!=set(b.files):raise ArithmeticError('Different affine array inventory')
            for key in a.files:
                if a[key].dtype!=b[key].dtype or a[key].shape!=b[key].shape or not np.array_equal(a[key],b[key]):raise ArithmeticError('Affine array differs '+key)
                array_count+=1
    return dict(status='PASS' if not diff else 'FAIL',differences=diff,checked_dependency_hashes=hashes,identical_affine_arrays=array_count,excluded_metadata_keys=sorted(OMIT))
