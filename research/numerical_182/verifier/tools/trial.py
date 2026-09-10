"""Check the posted Lean literal trial against the exact numerical input."""
import json,re
from fractions import Fraction as Q
from pathlib import Path
from tools.coverage import HERE,number

def check():
    text=(HERE/'target/TrialData182.lean').read_text()
    trial=json.loads((HERE/'snapshot/prime_gaps_20260903/results/multicap_a6_full_cap_n393216_trial.json').read_text())
    def body(name):return re.split(r'\n(?:def |structure )',text.split('def '+name+' ',1)[1],maxsplit=1)[0].split(':=',1)[1].strip()
    def vector(name):
        value=re.sub(r'\((-?\d+) / (\d+)\)',lambda m:'"'+m[1]+'/'+m[2]+'"',body(name)).replace('!','')
        return json.loads(value)
    def same(a,b):
        if list(map(Q,a))!=list(map(Q,b)):raise ArithmeticError('Exact trial literal differs')
    names={'trialDimension':'dimension','trialIntervals':'intervals','trialRadius':'S','trialRho':'rho','trialRhoStar':'rho_star','trialLambda':'hybrid_lambda','trialKappa':'kappa_upper','trialMinorantA':'minorant_a','trialRoughness':'roughness','trialAuxiliaryRetreat':'auxiliary_retreat','trialHingeThreshold':'hinge_threshold','trialPairBins':'kernel_pair_bins','trialRadialBlocks':'kernel_radial_blocks'}
    for name,key in names.items():
        if Q(body(name).strip('()').replace(' ',''))!=Q(trial[key]):raise ArithmeticError(name+' differs')
    same(vector('trialKnots'),trial['knots'])
    same(vector('trialComponentCap'),[c['cap'] for c in trial['independent_components']])
    signatures=vector('trialAngularSignature')
    if trial['descriptors']!=[[s,i] for s in signatures for i in range(22)]:raise ArithmeticError('Angular/radial descriptor order differs')
    coefficients=vector('trialDataCoefficient')
    if len(coefficients)!=3:raise ArithmeticError('Wrong component count')
    for actual,component in zip(coefficients,trial['independent_components']):
        if len(actual)!=11 or any(len(row)!=22 for row in actual):raise ArithmeticError('Coefficient table shape differs')
        same([q for row in actual for q in row],component['coefficients'])
        if Q(component['lower'])!=0 or Q(component['upper'])!=Q(trial['S']):raise ArithmeticError('Component support differs')
    shells=re.findall(r'\{ lower := .*?\}',body('trialShells'))
    # The roles are the same outer/base/enlarged/subtraction/full ordering used
    # in PhysicalTrial182 and the frozen cap engine.
    roles=['outer','base','enlarged','subtraction_row_14_optimized','full']
    expected=[x for role in roles for x in trial['shells'][role]]
    if len(shells)!=len(expected):raise ArithmeticError('Shell count differs')
    for line,row in zip(shells,expected):same([number(line,k) for k in ['lower','upper','cap']],row)
    if trial['profile']!={'weight':'21/200','slow':'1/100','fast':'907/5'}:raise ArithmeticError('PhysicalTrial profile differs')
    return dict(status='PASS_EXACT_LEAN_TRIAL_LITERALS',coefficients=726,knots=26,angular_signatures=11,component_caps=3,shells=len(shells),scalar_parameters=len(names))
if __name__=='__main__':print(json.dumps(check()))
