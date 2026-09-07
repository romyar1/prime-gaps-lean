#!/usr/bin/env python3
"""Exact cyclotomic group-ring checks of the Type III origin identities.

Uses Python integers exclusively for the certificate. For each listed p and
ratio pair, the numerator p^8*W_hat(0,0) is evaluated as a polynomial in zeta_p,
modulo zeta_p^p=1. Rationality is checked by equal nonconstant coefficients.
This finite check does not prove any uniform bound.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import time


def cyclic_product(a,b):
    p=len(a)
    out=[0]*p
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[(i+j)%p] += x*y
    return out


def star(a):
    p=len(a)
    return [a[-i % p] for i in range(p)]


def scaled_correlations(p):
    """The exact polynomial p^2*C(A,B,1)=p*S(A,B,1)-1."""
    inv=[0]+[pow(a,-1,p) for a in range(1,p)]
    table={}
    for A in range(1,p):
        for B in range(1,p):
            coeff=[0]*p
            coeff[0]=-1
            for u in range(1,p):
                for v in range(1,p):
                    t=(1+A*inv[u*v%p])%p
                    if not t:
                        continue
                    for x in range(1,p):
                        y=B*inv[x*t%p]%p
                        assert (A*inv[u*v%p]-B*inv[x*y%p]+1)%p == 0
                        coeff[(u+v-x-y)%p] += p
            table[A,B]=coeff
    return inv,table


def origin(p,inv,table,R,S):
    coeff=[0]*p
    for r1 in range(1,p):
        for r2 in range(1,p):
            A=r2*inv[r1*r1%p]%p
            B=r1*inv[r2*r2%p]%p
            AA=A*inv[R]%p
            BB=B*inv[S]%p
            product=cyclic_product(table[A,B],star(table[AA,B]))
            product=cyclic_product(product,table[AA,BB])
            product=cyclic_product(product,star(table[A,BB]))
            coeff=[a+b for a,b in zip(coeff,product)]
    assert len(set(coeff[1:])) == 1
    numerator=coeff[0]-coeff[1]
    value=Fraction(numerator,p**8)
    assert numerator % p == 1
    assert value.denominator == p**8
    return {"m_ratio":R,"n_ratio":S,"p8_origin_numerator":numerator,
            "origin_exact":str(value),"reduced_denominator":value.denominator,
            "numerator_mod_p":numerator%p,
            "coefficient_at_zero":coeff[0],
            "common_coefficient_at_every_nonzero_exponent":coeff[1],
            "origin_over_p3":float(value/p**3)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--primes",type=int,nargs="+",default=[5,7,11,17])
    parser.add_argument("--output",type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    receipt={"status":"EXACT_FINITE_ORIGIN_IDENTITIES_ONLY",
             "arithmetic":"Python integers and Fraction; no floating-point arithmetic in the certificate",
             "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             "records":[]}
    for p in args.primes:
        start=time.monotonic()
        inv,table=scaled_correlations(p)
        pairs=[(2,2),(2,3),(p-1,p-1)]
        rows=[origin(p,inv,table,R,S) for R,S in pairs]
        result={"p":p,"rows":rows,"elapsed_seconds":time.monotonic()-start}
        receipt["records"].append(result)
        args.output.write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps(result),flush=True)


if __name__=='__main__':
    main()
