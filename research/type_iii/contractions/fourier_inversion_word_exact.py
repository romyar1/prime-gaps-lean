#!/usr/bin/env python3
"""Exact fixed-prime checks of the corrected C / rank-four / Kl2 word."""

from hashlib import sha256
import json
from pathlib import Path
from pair_contraction_exact import (
    add, scale, constant, star, product, assert_equal,
    raw_tables, direct_correlation_scaled,
)


def matrix_product(a,b,p):
    units=range(1,p)
    out={}
    for i in units:
        for j in units:
            value=[0]*p
            for k in units:
                value=add(value,product(a[i,k],b[k,j]))
            out[i,j]=value
    return out


def check(p,s):
    inv,k2,k3=raw_tables(p)
    units=range(1,p)
    t=-inv[s]%p
    # traw=p*T; T=(rawKl2(A*B)+1)/p is exactly involutive.
    traw={(A,B):add(k2[A*B%p],constant(p,1)) for A in units for B in units}
    tsq=matrix_product(traw,traw,p)
    for A in units:
        for B in units:
            assert_equal(tsq[A,B],constant(p,p*p*int(A==B)),("T involution",p,A,B))
    def braw(c):
        out={}
        for A in units:
            for B in units:
                value=[0]*p
                for x in units:
                    if (1+c*x)%p:
                        y=x*inv[(1+c*x)%p]%p
                        value=add(value,product(traw[A,x],traw[y,B]))
                out[A,B]=value
                # p^2*C_c = p*(p^2*B_c) + p*Traw(A,-1/c)
                #              + p*Traw(B,1/c) -(p+1)^2.
                rhs=add(add(scale(value,p),scale(traw[A,-inv[c]%p],p)),
                        add(scale(traw[B,inv[c]],p),constant(p,-(p+1)**2)))
                lhs=direct_correlation_scaled(p,k3,A,B,c)
                assert_equal(lhs,rhs,("actual corrected C",p,c,A,B))
        return out
    bs,bt=braw(s),braw(t)
    rraw={}
    for A in units:
        for B in units:
            value=[0]*p
            for x in units:
                value=add(value,product(traw[A,x],traw[inv[x],B]))
            rraw[A,B]=value
            raw4=[0]*p
            for u in units:
                for v in units:
                    for w in units:
                        raw4[(u+v+w+A*B*inv[u*v*w%p])%p]+=1
            assert_equal(value,add(raw4,constant(p,p+1)),("rank four",p,A,B))
    word=matrix_product(matrix_product(bs,rraw,p),bt,p)
    for A in units:
        for B in units:
            rhs=scale(add(k2[(-A*inv[s]-s*B)%p],constant(p,1)),p**5)
            assert_equal(word[A,B],rhs,("Bruhat Kl2 word",p,s,A,B))
    return {"p":p,"s":s,"t_minus_inverse_s":t,
            "unit_matrix_entries":(p-1)**2,
            "involution":"PASS","actual_C_normalizations":"PASS",
            "rank_four_kernel":"PASS","three_operator_Kl2_word":"PASS"}


def main():
    result={"status":"EXACT_SELECTED_OPERATOR_WORD_IDENTITIES_ONLY",
            "four_cycle_fourier_bound_proved":False,
            "arithmetic":"integer cyclotomic coefficient vectors",
            "source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
            "records":[check(5,2),check(7,2)]}
    Path(__file__).with_suffix(".json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()
