#!/usr/bin/env python3
"""Rerun finite algorithm audits and frozen-record bookkeeping in an isolated copy."""
import argparse,json,os,shutil,subprocess,sys,time
from pathlib import Path
from verify import HERE,digest,save,check_inputs

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--work',type=Path,required=True);args=p.parse_args()
    check_inputs()
    work=args.work.resolve();work.mkdir(parents=True,exist_ok=False);root=work/'prime_gaps_20260903';source=HERE/'snapshot/prime_gaps_20260903'
    subprocess.run(['/bin/cp','-cR',str(source),str(root)],check=True)
    (root/'rebuilt').mkdir();(work/'evidence').mkdir()
    os.environ['TMPDIR']=str(root/'rebuilt')
    for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','VECLIB_MAXIMUM_THREADS'):os.environ[key]='1'
    result={'status':'RUNNING','audits':[]}
    for item in json.loads((HERE/'audits.json').read_text()):
        name=item['name'];output=root/item['output'];original=output.read_bytes() if output.exists() else None
        if original is not None:output.unlink()
        job={**item,'root':str(root),'access_log':'rebuilt/'+name+'-reads.json'};save(work/(name+'-job.json'),job)
        start=time.monotonic()
        with (work/'evidence'/(name+'.log')).open('w') as log:
            r=subprocess.run([sys.executable,'-B',str(HERE/'tools/worker.py'),str(work/(name+'-job.json'))],stdout=log,stderr=subprocess.STDOUT)
        record={'name':name,'exit_code':r.returncode,'seconds':time.monotonic()-start,'entry_sha256':digest(root/item['entry']),'status':'PASS' if r.returncode==0 and output.is_file() else 'FAIL'}
        if output.is_file():
            shutil.copyfile(output,work/'evidence'/(name+'.json'));record['output_sha256']=digest(output)
        # Audits run independently. Restore the hash-bound historical audit input
        # for the next audit rather than rewriting any stored provenance digest.
        if original is not None:output.write_bytes(original)
        result['audits'].append(record);save(work/'audits-result.json',result)
        print(json.dumps(record),flush=True)
        if record['status']=='FAIL':return 1
    result['status']='PASS';save(work/'audits-result.json',result)
    return 0
if __name__=='__main__':raise SystemExit(main())
