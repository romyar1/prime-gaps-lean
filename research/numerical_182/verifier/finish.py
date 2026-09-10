#!/usr/bin/env python3
"""Accept a completed recomputation only after coverage, payload and integrity checks."""
import argparse,json,shutil,sys
from pathlib import Path
from datetime import datetime,timezone
from verify import HERE,digest,save
from tools.compare import check as compare
from tools.coverage import check as coverage
from tools.trial import check as trial_check

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--work',type=Path,required=True);p.add_argument('--audits',type=Path,required=True);p.add_argument('--negative',type=Path,required=True);p.add_argument('--export',type=Path);a=p.parse_args()
    root=a.work.resolve()/'prime_gaps_20260903';plan=json.loads((HERE/'stages.json').read_text());state=json.loads((a.work/'run.json').read_text())
    audit=json.loads((a.audits/'audits-result.json').read_text())
    expected_audits=json.loads((HERE/'audits.json').read_text())
    for path,expected in json.loads((HERE/'target/source.json').read_text())['files'].items():
        if digest(HERE/path)!=expected:raise ArithmeticError('Posted Lean target changed: '+path)
    if audit['status']!='PASS' or [x['name'] for x in audit['audits']]!=[x['name'] for x in expected_audits]:raise ArithmeticError('Incomplete audit suite')
    for item,recipe in zip(audit['audits'],expected_audits):
        if item['status']!='PASS' or digest(a.audits/'evidence'/(item['name']+'.json'))!=item['output_sha256']:raise ArithmeticError('Audit result missing or changed')
        if item['entry_sha256']!=digest(root/recipe['entry']):raise ArithmeticError('Audited implementation differs')
    negative=json.loads((a.negative/'negative-controls.json').read_text())
    if negative['status']!='PASS' or {x['case'] for x in negative['cases'] if x['rejected']}!={'negative_denominator','missing_inner_bin','changed_trial','obsolete_fft_runtime'}:raise ArithmeticError('Negative controls missing')
    for item in json.loads((HERE/'assembly.json').read_text())['files']:
        if digest(root/item['path'])!=item['sha256']:raise ArithmeticError('Frozen workspace input changed: '+item['path'])
    comparisons={};forbidden={s['reference'] for s in plan};forbidden|={str(Path(p).with_suffix('.npz')) for p in forbidden}
    for stage in plan:
        name=stage['name'];record=state['stages'].get(name)
        if not record or record['status']!='PASS':raise ArithmeticError('Stage incomplete: '+name)
        if record['entry_sha256']!=digest(root/stage['entry']):raise ArithmeticError('Producer changed: '+name)
        for path,h in record['outputs'].items():
            if digest(root/path)!=h:raise ArithmeticError('Production result changed: '+path)
        job=json.loads((a.work/(name+'-job.json')).read_text())
        for key in ['entry','arguments','output','function','trial']:
            if job.get(key)!=stage.get(key):raise ArithmeticError('Executed recipe differs: '+name+' '+key)
        reads=json.loads((root/job['access_log']).read_text())
        if forbidden.intersection(reads):raise ArithmeticError('Historical numerical output was read: '+name)
        comparisons[name]=compare(stage,root)
    save(a.work/'payload-comparisons.json',comparisons)
    if any(x['status']!='PASS' for x in comparisons.values()):raise ArithmeticError('Mathematical payload differs; see payload-comparisons.json')
    result=coverage(root,plan,True);save(a.work/'coverage.json',result)
    save(a.work/'trial-comparison.json',trial_check())
    receipt={'status':'PASS_COMPLETE_EXTERNAL_NUMERICAL_RECOMPUTATION','completed_utc':datetime.now(timezone.utc).isoformat(),'production_stages':len(plan),'audit_stages':len(expected_audits),'target_inequalities':262,'source_geometry_equalities':result['geometry_checks'],'all_262_recomputed':True,'lean_numerical_premises_discharged':0,'type_iii_proved':False,'historical_production_outputs_read':False,'fresh_affine_arrays_equal':comparisons['affines']['identical_affine_arrays'],'mathematical_payloads_match_reference':True,'recorded_production_seconds':sum(x['seconds'] for x in state['stages'].values()),'scope':'External interval/finite verification of the frozen numerical certificate. The 262 analytic bounds remain explicit hypotheses in the posted Lean development; Type III is separate. Finite implementation audits do not constitute an independent review of every analytic reduction.','target_files':{p.name:digest(p) for p in (HERE/'target').glob('*.lean')},'package_tools':{str(p.relative_to(HERE)):digest(p) for p in [HERE/'verify.py',HERE/'audit.py',HERE/'finish.py',HERE/'stages.json',HERE/'audits.json',*sorted((HERE/'tools').glob('*.py'))]}}
    save(a.work/'verification.json',receipt)
    if a.export:
        a.export.mkdir(parents=True,exist_ok=False)
        for name in ['run.json','coverage.json','payload-comparisons.json','verification.json','trial-comparison.json']:shutil.copyfile(a.work/name,a.export/name)
        shutil.copytree(a.audits/'evidence',a.export/'audits');shutil.copyfile(a.audits/'audits-result.json',a.export/'audits-result.json')
        shutil.copyfile(a.negative/'negative-controls.json',a.export/'negative-controls.json')
        for name in ['changed_trial.log','obsolete_fft_runtime.log']:shutil.copyfile(a.negative/name,a.export/name)
        for stage in plan:
            name=stage['name'];shutil.copyfile(a.work/(name+'.log'),a.export/(name+'.log'));shutil.copyfile(a.work/(name+'-job.json'),a.export/(name+'-job.json'))
            for path in state['stages'][name]['outputs']:
                out=a.export/path;out.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(root/path,out)
            shutil.copyfile(root/'rebuilt'/(name+'-reads.json'),a.export/(name+'-reads.json'))
        files={str(p.relative_to(a.export)):digest(p) for p in a.export.rglob('*') if p.is_file()};save(a.export/'SHA256.json',files)
    print(json.dumps(receipt,indent=2));return 0
if __name__=='__main__':raise SystemExit(main())
