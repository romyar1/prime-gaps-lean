#!/usr/bin/env python3
"""Rebuild the fixed 182 numerical certificate using frozen upstream programs."""
import argparse, hashlib, json, os, shutil, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from datetime import datetime, timezone
from pathlib import Path
from tools.compare import check as compare

HERE = Path(__file__).resolve().parent
def digest(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,v):
    tmp=p.with_suffix(p.suffix+'.tmp');tmp.write_text(json.dumps(v,indent=2)+'\n');tmp.replace(p)

def check_inputs(root=None):
    root=root or HERE/'snapshot/prime_gaps_20260903'
    for item in json.loads((HERE/'assembly.json').read_text())['files']:
        p=root/item['path']
        if getattr(p.stat(),'st_flags',0) & 0x40000000:raise RuntimeError('Online-only input refused: '+str(p))
        if digest(p)!=item['sha256']:raise ArithmeticError('Frozen input changed: '+item['path'])

def main():
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument('--work',type=Path,required=True,help='New outside-Dropbox directory, or a resumable run')
    a.add_argument('--resume',action='store_true')
    a.add_argument('--through',help='Stop after this stage (diagnostic; cannot issue full PASS)')
    a.add_argument('--jobs',type=int,choices=(1,2,3),default=1,help='Concurrent single-threaded producers; default 1')
    args=a.parse_args()
    if sys.flags.optimize: raise RuntimeError('Assertions must be enabled')
    import numpy
    if numpy.__version__!='2.3.5': raise RuntimeError('This replay requires NumPy 2.3.5')
    plan=json.loads((HERE/'stages.json').read_text())
    manifest=json.loads((HERE/'assembly.json').read_text())
    src=HERE/'snapshot/prime_gaps_20260903'
    check_inputs(src)
    work=args.work.resolve();root=work/'prime_gaps_20260903'
    if args.resume:
        state=json.loads((work/'run.json').read_text())
        if state['assembly_sha256']!=digest(HERE/'assembly.json'): raise ArithmeticError('Different source assembly')
    else:
        work.mkdir(parents=True,exist_ok=False)
        if sys.platform=='darwin': subprocess.run(['/bin/cp','-cR',str(src),str(root)],check=True)
        else: shutil.copytree(src,root)
        state={'started_utc':datetime.now(timezone.utc).isoformat(),'assembly_sha256':digest(HERE/'assembly.json'),'stages':{},'status':'RUNNING','all_262_recomputed':False}
    (root/'rebuilt').mkdir(exist_ok=True)
    for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','VECLIB_MAXIMUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[v]='1'
    os.environ['TMPDIR']=str(root/'rebuilt');os.environ.pop('PYTHONOPTIMIZE',None)
    forbidden=[s['reference'] for s in plan if s.get('production')]
    forbidden += [str(Path(p).with_suffix('.npz')) for p in forbidden]
    if args.through:
        plan=plan[:next(i+1 for i,s in enumerate(plan) if s['name']==args.through)]
    pending=[]
    for stage in plan:
        name=stage['name'];old=state['stages'].get(name)
        if old and old['status']=='PASS':
            for p,h in old['outputs'].items():
                if digest(root/p)!=h: raise ArithmeticError('Completed output changed: '+p)
            checked=compare(stage,root);save(work/(name+'-comparison.json'),checked)
            if checked['status']!='PASS':raise ArithmeticError('Completed mathematical payload differs: '+name)
            continue
        pending.append(stage)
    def execute(stage):
        name=stage['name']
        out=root/stage['output'];out.parent.mkdir(parents=True,exist_ok=True)
        if out.exists(): raise FileExistsError('Unaccepted output requires review before resume: '+str(out))
        job={**stage,'root':str(root),'access_log':'rebuilt/'+name+'-reads.json','forbid_reads':forbidden if stage.get('production') else []}
        save(work/(name+'-job.json'),job)
        start=time.monotonic()
        print(json.dumps({'event':'START','stage':name}),flush=True)
        with (work/(name+'.log')).open('w') as log:
            result=subprocess.run([sys.executable,'-B',str(HERE/'tools/worker.py'),str(work/(name+'-job.json'))],stdout=log,stderr=subprocess.STDOUT)
        record={'status':'PASS' if result.returncode==0 and out.is_file() else 'FAIL','exit_code':result.returncode,'seconds':time.monotonic()-start,'entry_sha256':digest(root/stage['entry']),'worker_sha256':digest(HERE/'tools/worker.py'),'outputs':{},'job':name+'-job.json'}
        if out.is_file():record['outputs'][stage['output']]=digest(out)
        if stage.get('archive') and out.with_suffix('.npz').exists():record['outputs'][str(Path(stage['output']).with_suffix('.npz'))]=digest(out.with_suffix('.npz'))
        if record['status']=='PASS':
            checked=compare(stage,root);save(work/(name+'-comparison.json'),checked)
            if checked['status']!='PASS':record['status']='FAIL';record['error']='Mathematical payload differs; inspect '+name+'-comparison.json'
        print(json.dumps({'event':'FINISH','stage':name,**record}),flush=True)
        return record
    failed=False
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        running={}
        while pending or running:
            if not failed:
                for stage in list(pending):
                    needed=[] if stage['name'] in ('cap','affines') else ['cap','affines']
                    if len(running)<args.jobs and all(state['stages'].get(n,{}).get('status')=='PASS' for n in needed):
                        pending.remove(stage);running[pool.submit(execute,stage)]=stage
            state['status']='RUNNING';state['active_stages']=[s['name'] for s in running.values()];state.pop('active_stage',None);save(work/'run.json',state)
            if not running:
                if pending and not failed:raise ArithmeticError('Unresolved stage dependencies')
                break
            done,_=wait(running,return_when=FIRST_COMPLETED)
            for future in done:
                stage=running.pop(future)
                try:record=future.result()
                except Exception as e:record={'status':'FAIL','error':str(e)}
                state['stages'][stage['name']]=record;failed|=record['status']!='PASS'
                save(work/'run.json',state)
    state['status']='FAIL' if failed else 'PRODUCTION_FINISHED_AWAITING_COVERAGE';state['active_stages']=[];save(work/'run.json',state)
    return int(failed)
if __name__=='__main__':raise SystemExit(main())
