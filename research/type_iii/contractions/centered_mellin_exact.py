#!/usr/bin/env python3
"""Exact normalization checks for the symbolic centered Mellin expansion.

One full Gauss-coefficient check uses p=3 and its real quadratic character.
One p=5 example compares the quadratic and quartic energies at fixed a=2.
These are fixed examples, not a parameter scan or an asymptotic estimate.
"""

from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path

from pair_contraction_exact import (
    add, scale, constant, star, product, assert_equal,
    raw_tables, direct_correlation_scaled,
)


def poly_sum(rows, p):
    out = [0]*p
    for row in rows:
        out = add(out, row)
    return out


def poly_prod(rows, p):
    out = constant(p, 1)
    for row in rows:
        out = product(out, row)
    return out


def rational_integer(row):
    assert len(set(row[1:])) == 1, row
    return row[0] - row[1]


def diagonal_energy(p):
    n = p-1
    aa = Fraction(p-2) + Fraction(1, p**4)
    bb = p**4 - 3*p**3 + p**2 + 1
    return ((n-2)*bb**2+2*aa*bb)/n**5


def p3_gauss_check():
    p, size, a, chi = 3, 2, 2, 1
    units = range(1, p)
    inv, s2, l3 = raw_tables(p)
    c = {(A,B):direct_correlation_scaled(p,l3,A,B,1) for A in units for B in units}
    char = lambda j, A: 1 if j % 2 == 0 or A == 1 else -1
    tau = [poly_sum([scale([int(t == k) for k in range(p)], char(j,t))
                     for t in units], p) for j in range(size)]
    # p*F_j = tau(bar chi_j)^3; the two p=3 characters are real.
    ff = [poly_prod([t,t,t], p) for t in tau]
    for A in units:
        for B in units:
            rhs = poly_sum([
                scale(poly_prod([ff[r],star(ff[s]),tau[(r-s)%size]],p),
                      char(r,A)*char(s,B))
                for r in range(size) for s in range(size)], p)
            assert_equal(scale(c[A,B],size**2),rhs,("C Mellin",A,B))

    pair = {(A,B):product(c[A,B],star(c[a*A%p,B])) for A in units for B in units}
    m = {A:poly_sum([scale(pair[A,B],char(chi,B)) for B in units],p) for A in units}
    energy = poly_sum([product(row,star(row)) for row in m.values()],p)
    z = []
    diagonal = [0]*p
    for eta in range(size):
        terms = []
        for r in range(size):
            for s in range(size):
                term = scale(poly_prod([
                    ff[(eta+r)%size],star(ff[r]),star(ff[s]),ff[(chi+s)%size],
                    tau[(eta+r-s)%size],star(tau[(r-chi-s)%size]),
                ],p),char(r,a))
                terms.append(term)
                diagonal=add(diagonal,product(term,star(term)))
        z.append(poly_sum(terms,p))
    for A in units:
        assert_equal(scale(m[A],size**3),
                     poly_sum([scale(z[eta],char(eta,A)) for eta in range(size)],p),
                     ("row Mellin product",A))
    assert_equal(scale(energy,size**5),
                 poly_sum([product(row,star(row)) for row in z],p),
                 "energy Gauss expansion")
    ev = Fraction(rational_integer(energy),p**8)
    dv = Fraction(rational_integer(diagonal),p**8*size**5)
    assert dv == diagonal_energy(p)

    all_ratio_energy=[0]*p
    for row_ratio in units:
        for A in units:
            value=poly_sum([
                scale(product(c[A,B],star(c[row_ratio*A%p,B])),char(chi,B))
                for B in units],p)
            all_ratio_energy=add(all_ratio_energy,product(value,star(value)))
    full=Fraction(rational_integer(all_ratio_energy),p**8)
    kappa=Fraction(p*p+p+1,p*p)
    jacobi=Fraction(1)
    trace_formula=(p**4*size-4*kappa*p**3*size+2*kappa**2*p*p+
                   kappa**2*(2*p**3+p*p*(jacobi-Fraction(2,p))**2))
    assert full == trace_formula
    return {"p":p,"a":a,"character_order":2,
            "correlation_Mellin_checks":4,"row_product_Mellin_checks":2,
            "Gauss_energy_identity":"PASS","energy":str(ev),
            "diagonal_energy":str(dv),"off_diagonal_energy":str(ev-dv),
            "all_row_ratio_energy":str(full),"all_ratio_trace_identity":"PASS"}


def p5_energy_comparison():
    p, ratio=5,2
    inv,s2,l3=raw_tables(p)
    units=range(1,p)
    c={(A,B):direct_correlation_scaled(p,l3,A,B,1) for A in units for B in units}
    records=[]
    for order in (2,4):
        total=[0]*p
        for A in units:
            pair={B:product(c[A,B],star(c[ratio*A%p,B])) for B in units}
            # Generator 2 has successive powers 1,2,4,3. Pair products are real.
            if order==2:
                val=add(add(pair[1],scale(pair[2],-1)),add(pair[4],scale(pair[3],-1)))
                total=add(total,product(val,star(val)))
            else:
                real=add(pair[1],scale(pair[4],-1))
                imag=add(pair[3],scale(pair[2],-1))
                total=add(total,add(product(real,star(real)),product(imag,star(imag))))
        value=Fraction(rational_integer(total),p**8)
        records.append({"p":p,"a":ratio,"character_order":order,
                        "energy":str(value),"diagonal_energy":str(diagonal_energy(p)),
                        "off_diagonal_energy":str(value-diagonal_energy(p))})
    assert records[0]["energy"] != records[1]["energy"]
    return records


def main():
    result={"status":"EXACT_SELECTED_MELLIN_IDENTITIES_ONLY",
            "uniform_centered_origin_bound_proved":False,
            "arithmetic":"integer cyclotomic vectors and exact fractions",
            "source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
            "p3_full_normalization":p3_gauss_check(),
            "p5_nonflat_energy_example":p5_energy_comparison()}
    Path(__file__).with_suffix(".json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()
