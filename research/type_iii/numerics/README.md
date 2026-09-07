# Type III finite-sum diagnostics

The computations here stress-test the **actual** distinct-index four-cycle
in [`TypeIIILocal.lean`](../../../formal/TypeIIILocal.lean). They do not
establish a uniform bound, and they do not supply
`HasFiniteExceptionalTypeIIIInput`.

The accompanying note
[`cyclotomic_covariance.md`](cyclotomic_covariance.md) gives exact derivations
of the cyclotomic covariance, rationality of the origin, its reduced
denominator `p^8`, nonvanishing and exact integrality denominator at every
frequency, and the reduction to row/column ratios and cube classes.
Those arguments are independent of the finite searches. The
[formalization map](../../../docs/type-iii.md) records which supporting
identities and conditional deductions have Lean proofs.

## What was checked

Every Fourier transform uses the **positive** character and the
**unnormalized** two-dimensional counting measure from the Lean definition.
The recorded Fourier coefficients are divided by `p^3`.

For each prime listed in the following table, the computation covers all
nonzero residue parameters satisfying `m != m'` and `n != n'`, and every
frequency. This follows from the exact parameter reduction in Section 5 of
the note: set `alpha=m=1`, let `n` run through all cube classes, and let the
ratios `R=m'/m`, `T=n'/n` run through all nonzero residues other than one.
The coverage is at these listed primes, not at every prime below 101.

| Prime | Normalized parameter sets | Fourier coefficients evaluated | Largest `abs(W_hat)/p^3` |
| ---: | ---: | ---: | ---: |
| 5 | 9 | 225 | 0.219355 |
| 7 | 75 | 3,675 | 4.618963 |
| 11 | 81 | 9,801 | 3.134243 |
| 17 | 225 | 65,025 | 2.573656 |
| 31 | 2,523 | 2,424,603 | 4.921642 |
| 61 | 10,443 | 38,858,403 | 6.875846 |
| 101 | 9,801 | 99,980,001 | 4.489283 |

This totals **141,341,733 Fourier coefficients**. All were below `7p^3`
in this finite sample. This observation is not a proof of any proposed
constant, even at an unlisted prime.

There is also an exhaustive **origin-only** calculation at the primes in
the next table. It tests every pair of distinct ratios and all cube classes,
including ratios outside the structured families used in the larger
full-spectrum samples.

| Prime | Normalized parameter sets | Largest `abs(W_hat(0,0))/p^3` |
| ---: | ---: | ---: |
| 5 | 9 | 0.219355 |
| 7 | 75 | 4.618963 |
| 11 | 81 | 3.134243 |
| 17 | 225 | 2.573656 |
| 31 | 2,523 | 4.921642 |
| 61 | 10,443 | 6.875846 |
| 101 | 9,801 | 4.489283 |
| 211 | 131,043 | 7.131543 |
| 1009 | 3,042,147 | 9.311258 |
| 1201 | 4,312,803 | 10.144299 |

At `p=1201`, a maximizing example in the trivial cube class is
`R=1158`, `T=1200=-1`. Its absolute origin coefficient is about
`0.00844655 p^4`. This search did not reveal a family with a nonvanishing
`p^4` leading term in the distinct branch. A finite search cannot exclude
such a family.

The structured full-spectrum cases include both signs, a sign in one
coordinate, equal ratios, reciprocal ratios, opposite ratios, negative
reciprocal ratios, squared ratios, and pairs of cube roots or their
negatives. They use fixed bases `2,3,5,7` where applicable, plus `(2,3)` and
`(3,5)` as generic comparisons. The larger-prime results are:

| Prime | Sampled normalized parameter sets | Largest `abs(W_hat)/p^3` |
| ---: | ---: | ---: |
| 211 | 141 | 5.617253 |
| 401 | 31 | 4.728308 |
| 809 | 31 | 7.626239 |
| 1009 | 141 | 5.941272 |
| 1201 | 141 | 8.563201 |
| 2003 | 31 | 6.310895 |
| 4001 | 31 | 6.037147 |

All three cube classes are included whenever `p=1 mod 3`. For `p=2 mod 3`
there is only one. The numerical evidence found no counterexample, and
does not prove the target.

## Normalization controls and exact small-prime checks

The repeated branch provides a control that the diagnostic detects a
`p^4` origin. At `p=2003`, the exact same implementation produces an origin
near `3p^4` when both pairs repeat, and near `p^4` when only the row repeats.
The explicit numerical values are in
[`repeated_origin_control.json`](repeated_origin_control.json).

At `p=5,7,11`, the fast correlation table and Fourier transform were checked
against direct evaluation of the original two-unit `Kl3` definition and
the original four-cycle. The maximum absolute residual in the direct
Fourier comparison was `4.45e-12`. The largest transpose/negation residual
in the fast correlation table, including the run at `p=4001`, was
`3.38e-14` after dividing the entries by `sqrt(p)`.

[`exact_origin_check.py`](exact_origin_check.py) uses only integer
arithmetic in its certificate. At each of `p=5,7,11,17`, it evaluates the
origin for `(R,T)=(2,2),(2,3),(-1,-1)` in the group ring of the cyclic group
of order `p`. It verifies the coefficient identities implying rationality,
and that the numerator of `p^8 W_hat(0,0)` is congruent to one modulo `p`.
Its exact values agree with the independent floating calculation to less
than `2.67e-15` after division by `p^3`. The use of a float for the optional
display ratio does not enter the integer checks.

These are diagnostic residuals, not interval-arithmetic error bounds. No
floating computation here is described as a formally verified inequality.

## Efficient evaluation

Let `Kl2` have the usual `p^(-1/2)` normalization and set

```text
q(t) = 1_{t!=0} Kl2(1/t) - p^(-3/2).
```

For `z!=0`, its positive additive transform is `sqrt(p) Kl3(z)`; at zero
the transform vanishes. The fast table therefore uses the exact identity

```text
C(A,B,1) = sum_u q(u/A) q((u+1)/B).
```

It stores `C(1/u,1/v,1)/sqrt(p)` on the unit square, and zero on its axes.
The actual physical pullback has indices

```text
u = m r1^2/(alpha r2),     v = n r2^2/(alpha r1).
```

The product of four normalized entries is `W/p^2`, so the positive
`ifft2` multiplied by `p` is exactly `W_hat/p^3` in exact arithmetic.

For all origin ratios, use multiplicative coordinates `u=g^i,v=g^j` and
put `d=gcd(3,p-1)`. The physical torus has `d` preimages exactly when
`2i+j=c mod d`, for the cube class `n=g^c`. For fixed row shift `r`, set

```text
N_r(i,j) = C_normalized(g^i,g^j) C_normalized(g^(i+r),g^j),
Omega_c(i,j) = d * 1_{2i+j=c mod d}.
```

The origin divided by `p^3` at the column shift `s` is

```text
(1/p) sum_{i,j} Omega_c(i,j) N_r(i,j) N_r(i,j+s).
```

A one-dimensional multiplicative FFT evaluates every `s` together.
The strongest value in each class is independently rechecked by the
physical two-dimensional sum. This avoids a naive separate `p^2`-point
sum for all `p^2` ratio pairs.

## Reproduction

Run from this directory with Python 3 and NumPy available. The exact origin
script needs only Python's standard library.

```sh
python3 structured_fourier_screen.py --all-cosets
python3 structured_fourier_screen.py --primes 1009 1201 2003 4001 --all-cosets --all-origins-through 1201 --output structured_extended.json
python3 exhaustive_spectrum_screen.py
python3 exact_origin_check.py
python3 repeated_origin_control.py
```

The scripts record their own source hashes in the receipts. The full
receipts are
[`structured_fourier_screen.json`](structured_fourier_screen.json),
[`structured_extended.json`](structured_extended.json),
[`exhaustive_spectrum_screen.json`](exhaustive_spectrum_screen.json),
[`exact_origin_check.json`](exact_origin_check.json), and
[`repeated_origin_control.json`](repeated_origin_control.json).

## Analytic next steps

The covariance and parameter reduction simplify the exact target but do not
replace its missing cancellation. The published-input route is described
[separately](../published_inputs/README.md). A proof of the distinct branch still needs a uniform
`O(p^3)` bound away from boundedly many frequencies, with `O(p^3.5)` at those
exceptions. The repeated branch still needs its bounded-degree curve and
the nonzero-frequency estimate. Rationality at the origin is not an upper
bound there, and the exact denominator result is compatible with either
`p^3` or `p^4` growth.
