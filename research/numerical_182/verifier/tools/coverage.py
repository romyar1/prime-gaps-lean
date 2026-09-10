"""Exact rational, bijective mapping from production outputs to 262 Lean targets."""
import argparse, json, re
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path

HERE=Path(__file__).resolve().parents[1]
def number(line,key):
    m=re.search(r'\b'+key+r'\s*:=\s*(\(-?\d+ / \d+\)|-?\d+)',line)
    if not m: raise ValueError('Missing rational '+key)
    return Q(m[1].strip('()').replace(' ',''))
def targets():
    text=(HERE/'target/SourceData182.lean').read_text()
    sections=text.split('def trialOuterCertificates',1)[1].split('def trialInnerCertificates',1)
    answer={}
    for side,part in zip(('outer','inner'),sections):
        rows=[x for x in part.splitlines() if '{ cover :=' in x]
        if len(rows)!=(60 if side=='outer' else 137):raise ArithmeticError('Wrong target count')
        for j,row in enumerate(rows):
            family=int(number(row,'family'));kind=re.search(r'kind := \.(\w+)',row)[1]
            kind={'rankTwo':'rank_two'}.get(kind,kind)
            group='C' if family==6 else 'G'+str(family+1)
            key=(side,group,kind,int(number(row,'binIndex')))
            if key in answer:raise ArithmeticError('Duplicate target')
            answer[key]=(j,row)
    return answer

def check(root,plan,rebuilt=True):
    target=targets();seen=set();bounds=[];geometry_checks=0
    def read(name):
        s=next(s for s in plan if s['name']==name)
        return json.loads((root/s['output' if rebuilt else 'reference']).read_text())
    def emit(side,group,kind,index,values,parameters=None,geometry=None,counts=None,witness=None):
        nonlocal geometry_checks
        group='C' if group=='C1' else group
        key=(side,group,kind,index)
        if key in seen or key not in target:raise ArithmeticError('Wrong source inventory '+str(key))
        seen.add(key);j,line=target[key]
        if witness is not None:
            if Q(witness)!=number(line,'witnessUpper'):raise ArithmeticError('Rounded witness endpoint differs '+str(key))
            geometry_checks+=1
        for field,value in values.items():
            actual=Q(value);limit=number(line,field)
            if not 0<=actual<=limit:raise ArithmeticError('Target inequality failed '+str(key)+' '+field)
            bounds.append(dict(side=side,index=j,group=group,kind=kind,bin=index,field=field,value=str(actual),target=str(limit),pass_=True))
        if parameters:
            names={'q_low':'low','q_high':'high','low':'low','high':'high','slope':'slope'}
            for name,field in names.items():
                if name in parameters:
                    if Q(parameters[name])!=number(line,field):raise ArithmeticError('Source-bin geometry differs '+str(key)+' '+name)
                    geometry_checks+=1
        if geometry:
            names={'dimension':'dimension','order':'order','activation':'activation','ceiling':'threshold','radial_lower':'lowerRadius','radial_upper':'upperRadius','hard_cap':'hardCap','split':'split'}
            for name,field in names.items():
                if name in geometry:
                    if Q(geometry[name])!=number(line,field):raise ArithmeticError('Source-group geometry differs '+str(key)+' '+name)
                    geometry_checks+=1
            if 'aligned_cap_pieces' in geometry:
                literal=re.search(r'pieces := \[(.*?)\], sourceRows',line)[1]
                pieces=[]
                for first,last,cap in re.findall(r'⟨(\d+), (\d+), (\([^)]*\)|\d+)⟩',literal):
                    pieces.append((int(first),int(last),Q(cap.strip('()').replace(' ',''))))
                expected=[(int(p['first_index']),int(p['last_index']),Q(p['ceiling'])) for p in geometry['aligned_cap_pieces']]
                if pieces!=expected:raise ArithmeticError('Support pieces differ '+str(key))
                geometry_checks+=3*len(pieces)
        if side=='outer':
            if counts is None:raise ArithmeticError('Missing outer count table')
            literal=re.search(r'counts := \[(.*?)\]',line)[1]
            actual={}
            for first,last,count,multiplier in re.findall(r'⟨(\d+), (\d+), (\d+), (\([^)]*\)|\d+)⟩',literal):
                for q in range(int(first),int(last)+1):
                    if q in actual:raise ArithmeticError('Overlapping Lean count ranges')
                    actual[q]=(int(count),Q(multiplier.strip('()').replace(' ','')))
            expected={}
            for band in counts:
                if kind=='low':start,end,count,multiplier=band['first'],band['last'],band['count'],band['factor']
                else:start=end=band['coarse_sum'];count=band['eligible_count'];multiplier=band['multiplier']
                for q in range(start,end+1):
                    if q in expected:raise ArithmeticError('Overlapping production count ranges')
                    expected[q]=(count,Q(multiplier))
            if actual!=expected:raise ArithmeticError('Count multiplier table differs '+str(key))
            coarse=re.search(r'countCoarse := (true|false)',line)[1]=='true'
            if coarse!=(kind!='low'):raise ArithmeticError('Count table grid differs')
            geometry_checks+=len(actual)
    cap=read('cap');trial=(HERE/'target/TrialData182.lean').read_text()
    for form,side,name in [('denominator','lower','trialDenominatorLower'),('denominator','upper','trialDenominatorUpper'),('J0','lower','trialJ0Lower'),('Jplus','lower','trialJPlusLower'),('EK_outside_C','upper','trialTailUpper')]:
        line=next(x for x in trial.splitlines() if x.startswith('def '+name+' '))
        limit=Q(re.search(r':= \((\d+ / \d+)\)',line)[1].replace(' ',''));actual=Q(cap['forms'][form][side])
        if not (0<=actual and (limit<=actual if side=='lower' else actual<=limit)):raise ArithmeticError('Cap target failed '+name)
        bounds.append(dict(side='cap',field=name,value=str(actual),target=str(limit),direction=side,pass_=True))
    roots=read('outer-rank-roots');faces=read('outer-rank-faces');indices=defaultdict(int)
    face_map={(x['group'],x['band']):x for x in faces['results']}
    for row in roots['results']:
        group=row['group_id'];index=indices[group];indices[group]+=1
        face=face_map.pop((group,index))
        emit('outer',group,'rank_two',index,{'rootUpper':row['root_square_upper'],'faceUpper':face['weighted_face_upper']},row['parameters'],roots['groups'][group],face['full_root_local_count_bands'])
    if face_map:raise ArithmeticError('Unmatched rank-two faces')
    for row in read('outer-high')['results']:
        emit('outer',row['group_id'],'high',0,{'rootUpper':row['roots']['root_triangle_upper'],'faceUpper':row['face']['weighted_face_upper']},geometry=row['source_group'],counts=row['face']['full_root_local_count_bands'])
    for name in ['outer-G1-low','outer-G2-low-0','outer-G2-low-1-5','outer-G2-low-6-10','outer-G2-low-11-21']:
        for row in read(name)['results']:
            emit('outer',row['group_id'],'low',row['index'],{'rootUpper':row['root_triangle_upper'],'faceUpper':row['weighted_face_upper']},row['parameters'],row['group'],row.get('full_fine_count_ranges',[]),row.get('rounded_witness_upper'))
    for name in ['inner-G3-G5-G6-low','inner-G4-low','inner-C-low']:
        for row in read(name)['results']:
            emit('inner',row['label'],'low',row['bin_index'],{'faceUpper':row['inner_face_upper']},row.get('parameters'),row.get('clipped_group'),witness=row.get('rounded_witness_upper'))
    for group in read('inner-rank-high')['groups']:
        for row in group['components']:
            emit('inner',group['group']['id'],row['kind'],0 if row['kind']=='high' else row['component_index'],{'faceUpper':row['raw_inner_face']['upper']},row.get('parameters'),group['group'])
    if seen!=set(target) or len(bounds)!=262:raise ArithmeticError('Incomplete target coverage')
    return dict(status='PASS_ALL_262_RATIONAL_TARGET_COMPARISONS',fresh_outputs=rebuilt,inequalities=len(bounds),geometry_checks=geometry_checks,bounds=bounds,lean_numerical_premises_discharged=0,type_iii_proved=False)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--recorded',action='store_true');p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    result=check(a.root,json.loads((HERE/'stages.json').read_text()),not a.recorded)
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='bounds'}))
