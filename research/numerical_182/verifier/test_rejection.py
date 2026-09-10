#!/usr/bin/env python3
"""Negative controls: corrupted trial, missing bin, unsafe bound, obsolete FFT runtime."""
import argparse,json,os,subprocess,sys
from pathlib import Path
from verify import HERE,save,check_inputs
from tools.coverage import check

def main():
    p=argparse.ArgumentParser();p.add_argument('--work',type=Path,required=True);a=p.parse_args()
    check_inputs()
    work=a.work.resolve();work.mkdir(parents=True,exist_ok=False);root=work/'prime_gaps_20260903'
    subprocess.run(['/bin/cp','-cR',str(HERE/'snapshot/prime_gaps_20260903'),str(root)],check=True);(root/'rebuilt').mkdir()
    os.environ['TMPDIR']=str(root/'rebuilt');plan=json.loads((HERE/'stages.json').read_text());results=[]
    for name,stage,mutate in [('negative_denominator','cap',lambda d:d['forms']['denominator'].update(lower='-1')),('missing_inner_bin','inner-C-low',lambda d:d['results'].pop())]:
        path=root/next(s['reference'] for s in plan if s['name']==stage);original=path.read_bytes();data=json.loads(original);mutate(data);path.write_text(json.dumps(data))
        try:
            check(root,plan,False)
        except (ArithmeticError,ValueError) as e:results.append({'case':name,'rejected':True,'reason':str(e)})
        else:raise ArithmeticError('Negative control was accepted: '+name)
        finally:path.write_bytes(original)
    for name,entry,target in [('changed_trial','fragment_ritz/certify_fine_restored_182.py','results/multicap_a6_full_cap_n393216_trial.json'),('obsolete_fft_runtime','runtime_fix/check_certificate_runtime.py','runtime/flint/.dylibs/libflint.24.0.dylib')]:
        path=root/target;original=path.read_bytes()
        path.write_bytes(original+b'\n' if name=='changed_trial' else (root/'experiments/runtime_fix/original_libflint.24.0.dylib').read_bytes())
        job={'root':str(root),'entry':'experiments/'+entry,'arguments':[],'access_log':'rebuilt/'+name+'-reads.json'};save(work/(name+'-job.json'),job)
        with (work/(name+'.log')).open('w') as log:r=subprocess.run([sys.executable,'-B',str(HERE/'tools/worker.py'),str(work/(name+'-job.json'))],stdout=log,stderr=subprocess.STDOUT)
        path.write_bytes(original)
        if r.returncode==0:raise ArithmeticError('Negative control was accepted: '+name)
        text=(work/(name+'.log')).read_text()
        if ('AssertionError' if name=='changed_trial' else 'signed') not in text:raise ArithmeticError('Failure was unrelated to negative control: '+name)
        results.append({'case':name,'rejected':True,'exit_code':r.returncode,'log':name+'.log'})
    result={'status':'PASS','cases':results};save(work/'negative-controls.json',result);print(json.dumps(result,indent=2))
if __name__=='__main__':main()
