#!/usr/bin/env python3
"""Selected exact checks of the centered actual Type III Fourier identity.

Uses integer cyclotomic coefficient vectors from pair_contraction_exact.py.
The physical four-cycle is constructed with all four fixed indices. These
are checks of finitely many identities, not a uniform Fourier-bound test.
"""

from fractions import Fraction
from hashlib import sha256
import json
from math import gcd
from pathlib import Path

from pair_contraction_exact import (
    add, scale, constant, rotate, star, product, assert_equal,
    raw_tables, direct_correlation_scaled,
)


def rational_integer(poly):
    """Return the exact rational integer represented by this vector."""
    assert len(set(poly[1:])) == 1, ("not rational", poly)
    return poly[0] - poly[1]


def selected_case(p, alpha, m, mp, n, np):
    inv, s2, l3 = raw_tables(p)
    units = range(1, p)
    size = p - 1
    a, b = m * inv[mp] % p, n * inv[np] % p
    assert a != 1 and b != 1
    lam = pow(alpha, 3, p) * inv[m*m*n % p] % p
    cap = p*p+p+1
    c = {(A, B): direct_correlation_scaled(p, l3, A, B, 1)
         for A in units for B in units}
    u = {A: add(scale(s2[-A % p], p), constant(p, -1)) for A in units}

    # Praw=p^4 P, Graw=p^4 sum_B P, Qraw=(p-1)*p^4 Q.
    pair = {(A, B): product(c[A, B], star(c[a*A % p, B]))
            for A in units for B in units}
    gram = {A: scale(add(constant(p, p**3),
                         product(u[A], star(u[a*A % p]))), -cap)
            for A in units}
    centered = {(A, B): add(scale(pair[A, B], size), scale(gram[A], -1))
                for A in units for B in units}
    for A in units:
        actual = [0]*p
        for B in units:
            actual = add(actual, pair[A, B])
        assert_equal(actual, gram[A], ("row mean", p, A))

    # Independent quadratic Kl2 Fourier identity, including the zero mode.
    sq = [product(row, row) for row in s2]
    for xi in range(p):
        lhs = [0]*p
        for t in range(p):
            lhs = add(lhs, rotate(sq[t], -xi*t))
        if xi == 0:
            rhs = constant(p, p*size)
        else:
            rhs = scale(add(rotate(s2[inv[xi]*inv[xi] % p], 2*inv[xi]),
                            constant(p, -1)), p)
        assert_equal(lhs, rhs, ("quadratic Kl2 Fourier", p, xi))
    fourth = [0]*p
    for row in sq:
        fourth = add(fourth, product(row, star(row)))
    fourth_value = rational_integer(fourth)
    assert fourth_value <= 5*p**3
    u_fourth = [0]*p
    for row in u.values():
        norm_sq = product(row, star(row))
        u_fourth = add(u_fourth, product(norm_sq, norm_sq))
    u_fourth_value = Fraction(rational_integer(u_fourth), p**4)
    assert u_fourth_value <= 16*p**3

    records = []
    for h, k in ((0, 0), (1, 0), (1, 2)):
        physical = [0]*p
        for x in units:
            for y in units:
                A = alpha*y*inv[m*x*x % p] % p
                B = alpha*x*inv[n*y*y % p] % p
                cycle = product(pair[A, B], star(pair[A, b*B % p]))
                physical = add(physical, rotate(cycle, h*x+k*y))
        fiber = [0]*p
        residual = [0]*p
        error = [0]*p
        fiber_card = 0
        for A in units:
            for B in units:
                target = lam*inv[A*A*B % p] % p
                cycle = product(pair[A, B], star(pair[A, b*B % p]))
                centered_cycle = product(centered[A, B],
                                         star(centered[A, b*B % p]))
                correction = add(
                    add(scale(product(gram[A], star(pair[A, b*B % p])), size),
                        scale(product(star(gram[A]), pair[A, B]), size)),
                    scale(product(gram[A], star(gram[A])), -1),
                )
                for x in units:
                    if pow(x, 3, p) != target:
                        continue
                    y = m*inv[alpha]*A*x*x % p
                    phase = h*x+k*y
                    fiber = add(fiber, rotate(cycle, phase))
                    residual = add(residual, rotate(centered_cycle, phase))
                    error = add(error, rotate(correction, phase))
                    fiber_card += 1
        assert fiber_card == size**2
        assert_equal(physical, fiber, ("physical fiber", p, h, k))
        assert_equal(scale(physical, size**2), add(residual, error),
                     ("centered actual Fourier", p, h, k))
        origin_checked = False
        if h == 0 and k == 0 and gcd(3, size) == 1:
            origin = [0]*p
            for A in units:
                origin = add(origin, scale(product(gram[A], star(gram[A])), size))
            assert_equal(error, origin, ("cube-bijective origin error", p))
            origin_checked = True
        records.append({
            "h": h, "k": k, "physical_fiber_identity": "PASS",
            "centered_identity": "PASS",
            "cube_bijective_origin_error_identity": origin_checked,
        })
    return {
        "p": p, "alpha": alpha, "m": m, "m_prime": mp, "n": n, "n_prime": np,
        "row_ratio_a": a, "column_ratio_b": b,
        "cubic_fiber_maximum": gcd(3, size),
        "row_mean_checks": size,
        "quadratic_kl2_fourier_checks": p,
        "full_kl2_fourth_moment_exact": fourth_value,
        "unit_U_fourth_moment_exact": str(u_fourth_value),
        "frequencies": records,
    }


def main():
    # Fixed instances cover characteristic 3, bijective cubes, and cubic fibers.
    cases = ((3, 1, 1, 2, 1, 2),
             (5, 2, 1, 2, 1, 3),
             (7, 3, 2, 3, 1, 2))
    result = {
        "status": "EXACT_SELECTED_CENTERING_IDENTITIES_ONLY",
        "uniform_four_cycle_bound_proved": False,
        "arithmetic": "integer cyclotomic coefficient vectors and exact fractions",
        "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "helper_source_sha256": sha256(
            Path(__file__).with_name("pair_contraction_exact.py").read_bytes()).hexdigest(),
        "records": [selected_case(*case) for case in cases],
    }
    output = Path(__file__).with_suffix(".json")
    output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
