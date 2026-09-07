#!/usr/bin/env python3
"""Exact checks of the Type III common-column contraction.

All character arithmetic is in Z[z]/(1+z+...+z^(p-1)), using integer
coefficient lists. No complex floats or numerical norm bounds enter a
check. Correlations are constructed directly from the two-unit Kl3
definition, not from the contraction being tested.

This verifies finitely many instances of the identities in the adjacent
note; it is neither a Lean proof nor a uniform Fourier-bound certificate.
"""

import argparse
from fractions import Fraction
from hashlib import sha256
import json
from math import gcd, isqrt
from pathlib import Path
import time


def add(a, b):
    return [x + y for x, y in zip(a, b)]


def scale(a, n):
    return [n * x for x in a]


def constant(p, n):
    return [n] + [0] * (p - 1)


def rotate(a, n):
    p = len(a)
    n %= p
    return a[-n:] + a[:-n] if n else a[:]


def star(a):
    p = len(a)
    return [a[-j % p] for j in range(p)]


def product(a, b):
    p = len(a)
    out = [0] * p
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[(i + j) % p] += x * y
    return out


def assert_equal(a, b, context):
    # A degree <=p-1 polynomial vanishes at zeta_p iff all its
    # coefficients are the same. This is exact reduction by Phi_p.
    delta = [x - y for x, y in zip(a, b)]
    assert len(set(delta)) == 1, (context, delta)


def raw_tables(p):
    inv = [0] + [pow(a, -1, p) for a in range(1, p)]
    s2 = [[0] * p for _ in range(p)]
    l3 = [[0] * p for _ in range(p)]
    for t in range(p):
        for u in range(1, p):
            s2[t][(u + t * inv[u]) % p] += 1
            for v in range(1, p):
                l3[t][(u + v + t * inv[u * v % p]) % p] += 1
    return inv, s2, l3


def direct_correlation_scaled(p, l3, a, b, c):
    """p^2*C(a,b,c), directly from the original h,u,v sum."""
    out = [0] * p
    for h in range(1, p):
        out = add(out, rotate(product(l3[a * h % p],
                                      star(l3[b * h % p])), c * h))
    return out


def test_prime(p, general_frequency):
    started = time.monotonic()
    inv, s2, l3 = raw_tables(p)
    units = range(1, p)
    kappa_numerator = p * p + p + 1
    kappa = Fraction(kappa_numerator, p * p)
    table = {(a, b): direct_correlation_scaled(p, l3, a, b, 1)
             for a in units for b in units}

    def corr(a, b, c):
        c %= p
        if c == 0:
            return constant(p, p**3 * int(a == b) - kappa_numerator)
        return table[a * inv[c] % p, b * inv[c] % p]

    def unit_fourier(a, c):
        """p*F_c(a)."""
        c %= p
        if c == 0:
            return constant(p, -1)
        return add(scale(s2[-a * inv[c] % p], p), constant(p, -1))

    controls = 0
    for a in units:
        for c in range(p):
            direct = [0] * p
            for h in units:
                direct = add(direct, rotate(l3[a * h % p], c * h))
            assert_equal(direct, unit_fourier(a, c), ("unit Fourier", p, a, c))
            controls += 1
        for b in units:
            for c in (range(p) if general_frequency else (0, 1)):
                assert_equal(direct_correlation_scaled(p, l3, a, b, c),
                             corr(a, b, c), ("correlation normalization", p, a, b, c))
                controls += 1
            assert_equal(table[a, b], star(table[a, b]), ("reality", p, a, b))
            controls += 1

    contraction_checks = 0
    frequencies = range(p) if general_frequency else (1,)
    for a in units:
        for a_prime in units:
            for beta in units:
                for c in frequencies:
                    for d in frequencies:
                        lhs = [0] * p
                        for b in units:
                            lhs = add(lhs, product(corr(a, b, c),
                                                   star(corr(a_prime, beta * b % p, d))))
                        new_c = (c - d * inv[beta]) % p
                        rhs = add(scale(corr(a, a_prime * inv[beta] % p, new_c), p**3),
                                  scale(product(unit_fourier(a, c),
                                                star(unit_fourier(a_prime, d))),
                                        -kappa_numerator))
                        assert_equal(lhs, rhs, ("contraction", p, a, a_prime, beta, c, d))
                        contraction_checks += 1

    pair_checks = 0
    physical_checks = 0
    for a in units:
        for b in units:
            lhs = [0] * p
            for x in units:
                for y in units:
                    lhs = add(lhs, product(table[x, y], table[a*x % p, b*y % p]))
            expected = (p**3 * int(a == 1 and b == 1) - p**2 * int(a == b)
                        - p**2 * kappa * (int(a == 1) + int(b == 1))
                        + 2*p*kappa + kappa*kappa)
            numerator = p**4 * expected
            assert numerator.denominator == 1
            assert_equal(lhs, constant(p, numerator.numerator), ("two-factor origin", p, a, b))
            pair_checks += 1
            if gcd(3, p-1) == 1:
                physical = [0] * p
                for r1 in units:
                    for r2 in units:
                        x = r2 * inv[r1*r1 % p] % p
                        y = r1 * inv[r2*r2 % p] % p
                        physical = add(physical, product(table[x, y],
                                                        table[a*x % p, b*y % p]))
                assert_equal(physical, lhs, ("actual torus pair origin", p, a, b))
                physical_checks += 1

    # The signed average of actual unpulled four-cycles contracts twice.
    # Multiplication by p^8 clears every denominator on both sides.
    four_cycle_average_checks = 0
    for beta in range(2, p):
        lhs = [0] * p
        for a in units:
            for x in units:
                for y in units:
                    cycle = product(table[x, y], star(table[a*x % p, y]))
                    cycle = product(cycle, table[a*x % p, beta*y % p])
                    cycle = product(cycle, star(table[x, beta*y % p]))
                    lhs = add(lhs, cycle)
        rhs = [0] * p
        for y in units:
            qy = add(scale(s2[y], p), constant(p, -1))
            qby = add(scale(s2[beta*y % p], p), constant(p, -1))
            term = add(constant(p, p**3), product(qy, qby))
            rhs = add(rhs, scale(product(term, term), kappa_numerator**2))
        assert_equal(lhs, rhs, ("signed four-cycle average", p, beta))
        four_cycle_average_checks += 1

    # Exact Hilbert--Schmidt mass obtained by the unshifted contraction.
    mass = Fraction(p**3 - 3*p**2, 1) + Fraction(2, p) + kappa*kappa
    return {"p": p,
            "arithmetic": "integer cyclotomic coefficient vectors; exact Fraction display",
            "frequency_coverage": "all c,d in F_p" if general_frequency else "c=d=1",
            "contraction_parameter_coverage": "all A,A',beta in F_p^*",
            "normalization_and_reality_checks": controls,
            "contraction_checks": contraction_checks,
            "two_factor_origin_checks": pair_checks,
            "actual_torus_two_factor_origin_checks": physical_checks,
            "signed_four_cycle_average_checks": four_cycle_average_checks,
            "full_unit_matrix_frobenius_square_exact": str(mass),
            "elapsed_seconds": time.monotonic() - started}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--primes", type=int, nargs="+", default=[2, 3, 5, 7, 11])
    parser.add_argument("--all-frequencies-through", type=int, default=5)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    result = {"status": "EXACT_FINITE_CONTRACTION_IDENTITIES_ONLY",
              "uniform_bound_proved_by_this_script": False,
              "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
              "records": []}
    for p in args.primes:
        assert p >= 2 and all(p % d for d in range(2, isqrt(p) + 1)), p
        row = test_prime(p, p <= args.all_frequencies_through)
        result["records"].append(row)
        args.output.write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps(row), flush=True)


if __name__ == '__main__':
    main()
