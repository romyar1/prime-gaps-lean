#!/usr/bin/env python3
"""Floating-point stress test of the actual TypeIIILocal.lean finite sums.

The fast correlation construction is the rank-two Fourier identity used in
the earlier correlation_fourier_screen.py. This script instead evaluates the
two-variable toric pullback in TypeIIILocal.lean, with positive Fourier phase.
It does not prove or disprove any uniform asymptotic inequality by itself.

For p <= 11 an independent direct Kl_3 sum checks the normalization and indices.
An optional multiplicative FFT computes all distinct-ratio origin values.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import time

os.environ.setdefault("OPENBLAS_NUM_THREADS", "2")
os.environ.setdefault("VECLIB_MAXIMUM_THREADS", "2")
os.environ.setdefault("OMP_NUM_THREADS", "2")
import numpy as np


def prime(p: int) -> bool:
    return p >= 2 and all(p % d for d in range(2, math.isqrt(p) + 1))


def inverse_table(p: int) -> np.ndarray:
    inv = np.zeros(p, dtype=np.int64)
    inv[1] = 1
    for a in range(2, p):
        inv[a] = p - (p // a) * int(inv[p % a]) % p
    assert np.all(np.arange(1, p) * inv[1:] % p == 1)
    return inv


def primitive_root(p: int) -> int:
    n = p - 1
    factors = []
    q = 2
    while q * q <= n:
        if n % q == 0:
            factors.append(q)
            while n % q == 0:
                n //= q
        q += 1
    if n > 1:
        factors.append(n)
    return next(g for g in range(1, p) if all(pow(g, (p-1)//q, p) != 1 for q in factors))


def make_correlation(p: int, inv: np.ndarray) -> tuple[np.ndarray, dict]:
    """Return C[u,v] = correlation(1/u, 1/v, 1) / sqrt(p), zero on axes."""
    phase = np.exp(2j * np.pi * inv / p)
    phase[0] = 0
    k2 = np.sqrt(p) * np.fft.ifft(phase)
    q = k2.real[inv] - p ** (-1.5)
    q[0] = -p ** (-1.5)
    unit = np.arange(1, p, dtype=np.int64)
    u = np.arange(p, dtype=np.int64)[:, None]
    left = q[(u * unit) % p]
    right = q[((u + 1) * unit) % p]
    out = np.zeros((p, p))
    out[1:, 1:] = (left.T @ right) / np.sqrt(p)
    checks = {
        "k2_imaginary_residual": float(np.abs(k2.imag).max()),
        "q_mean_residual": float(abs(q.sum())),
        "q_norm_residual": float(abs(q @ q - (p-1-1/p-1/p**2))),
    }
    neg = (-np.arange(p)) % p
    checks["transpose_negation_residual"] = float(np.abs(out - out.T[np.ix_(neg, neg)]).max())
    assert max(checks.values()) < 2e-7
    return out, checks


def direct_check(p: int, inv: np.ndarray, corr: np.ndarray) -> dict:
    """Use the original u,v Kl_3 definition, independently of rank-two FFT."""
    units = np.arange(1, p, dtype=np.int64)
    roots = np.exp(2j * np.pi * np.arange(p) / p)
    u, v = units[:, None], units[None, :]
    values = np.array([
        roots[(u + v + t * inv[u * v % p]) % p].sum() / p for t in range(p)
    ])
    h = units
    mat = values[units[:, None] * h % p]
    direct = (mat * roots[h]) @ mat.conj().T
    fast = corr[np.ix_(inv[units], inv[units])] * np.sqrt(p)
    residual = float(np.abs(direct - fast).max())
    assert residual < 1e-9
    r1, r2 = np.indices((p, p))
    support = (r1 != 0) & (r2 != 0)
    R, S = 2 % p, (p-1)
    mindex = r1*r1*inv[r2] % p
    nindex = r2*r2*inv[r1] % p
    fast_w = (corr[mindex, nindex] * corr[R*mindex % p, nindex]
              * corr[R*mindex % p, S*nindex % p] * corr[mindex, S*nindex % p])
    slow_w = np.zeros((p, p), dtype=np.complex128)
    for x, y in zip(r1[support], r2[support]):
        A, B = y * inv[x*x % p] % p, x * inv[y*y % p] % p
        a, aa, b, bb = int(A)-1, int(A*inv[R] % p)-1, int(B)-1, int(B*inv[S] % p)-1
        slow_w[x,y] = direct[a,b] * direct[aa,b].conjugate() * direct[aa,bb] * direct[a,bb].conjugate()
    w_residual = float(np.abs(slow_w - p*p*fast_w).max())
    slow_hat = np.array([[np.sum(slow_w * roots[(h*r1+k*r2) % p])
                          for k in range(p)] for h in range(p)])
    fast_hat = np.fft.ifft2(fast_w) * p**4
    hat_residual = float(np.abs(slow_hat-fast_hat).max())
    assert w_residual < 1e-8 and hat_residual < 1e-7
    return {"direct_correlation_residual": residual,
            "direct_fourcycle_residual": w_residual,
            "direct_positive_fourier_residual": hat_residual}


def case_list(p: int, inv: np.ndarray, exhaustive: bool) -> list[tuple[int, int, list[str]]]:
    cases: dict[tuple[int,int], list[str]] = {}
    def add(r: int, s: int, name: str) -> None:
        r, s = r % p, s % p
        if r > 1 and s > 1:
            cases.setdefault((r,s), []).append(name)
    if exhaustive:
        for r in range(2,p):
            for s in range(2,p):
                add(r,s,"exhaustive")
    else:
        add(-1,-1,"both_signs")
        for a in [2,3,5,7]:
            a %= p
            if not a:
                continue
            add(a,a,f"equal_{a}")
            add(a,int(inv[a]),f"reciprocal_{a}")
            add(a,-a,f"opposite_{a}")
            add(a,-int(inv[a]),f"negative_reciprocal_{a}")
            add(a,-1,f"column_sign_{a}")
            add(-1,a,f"row_sign_{a}")
            add(a,a*a,f"squared_{a}")
        add(2,3,"generic_2_3")
        add(3,5,"generic_3_5")
        g = primitive_root(p)
        if (p-1) % 3 == 0:
            omega = pow(g, (p-1)//3, p)
            for r in [omega, omega*omega % p, -omega, -omega*omega % p]:
                for s in [omega, omega*omega % p, -omega, -omega*omega % p]:
                    add(r,s,"cubic_or_negative_cubic")
    return [(r,s,names) for (r,s),names in sorted(cases.items())]


def spectrum_row(p: int, inv: np.ndarray, corr: np.ndarray, R: int, S: int,
                 names: list[str], coset: int = 0, base_indices=None) -> dict:
    if base_indices is None:
        r1,r2 = np.indices((p,p), dtype=np.int64)
        ix = r1*r1*inv[r2] % p
        iy = r2*r2*inv[r1] % p
    else:
        ix,iy = base_indices
    # m=1, n=g^coset. For p=1 mod 3 these sample all degree-three toric image classes.
    n = pow(primitive_root(p), coset, p)
    iy = n*iy % p
    w = corr[ix,iy] * corr[R*ix % p,iy] * corr[R*ix % p,S*iy % p] * corr[ix,S*iy % p]
    # w=W/p^2, and ifft2(w)=sum W e(+)/p^4. Thus p*ifft2(w)=W_hat/p^3.
    hat = p*np.fft.ifft2(w)
    abs_hat = np.abs(hat)
    top_count = min(12, p*p)
    indices = np.argpartition(abs_hat.ravel(), -top_count)[-top_count:]
    indices = indices[np.argsort(abs_hat.ravel()[indices])[::-1]]
    top = []
    for flat in indices:
        h,k = np.unravel_index(flat, (p,p))
        z = hat[h,k]
        top.append({"frequency":[int(h),int(k)],"real_over_p3":float(z.real),
                    "imag_over_p3":float(z.imag),"abs_over_p3":float(abs(z))})
    return {
        "m_ratio":R,"n_ratio":S,"families":names,"m":1,"n":n,"alpha":1,
        "cube_coset":coset,
        "origin_real_over_p3":float(hat[0,0].real),
        "origin_imag_over_p3":float(hat[0,0].imag),
        "origin_abs_over_p4":float(abs(hat[0,0])/p),
        "max_over_p3":float(abs_hat.max()),
        "max_over_p3p5":float(abs_hat.max()/np.sqrt(p)),
        "rms_over_p3":float(np.sqrt(np.mean(abs_hat**2))),
        "mean_w_over_p2":float(w.mean()),
        "physical_fourcycle_min_over_p2":float(w.min()),
        "physical_fourcycle_max_over_p2":float(w.max()),
        "counts_above_multiple_p3":{str(t):int((abs_hat > t).sum()) for t in [2,4,6,8,10,16]},
        "largest_frequencies":top,
    }


def all_origin_ratios(p: int, corr: np.ndarray) -> dict:
    """All R,S distinct cases, using multiplicative FFT with toric class weights."""
    g = primitive_root(p)
    powers = np.array([pow(g,i,p) for i in range(p-1)], dtype=np.int64)
    table = corr[np.ix_(powers,powers)]
    ix,iy = np.indices(table.shape, dtype=np.int64)
    multiplicity = math.gcd(3,p-1)
    masks = [multiplicity*((2*ix+iy-c) % multiplicity == 0) for c in range(multiplicity)]
    rows = []
    for c,mask in enumerate(masks):
        vals = np.zeros(table.shape)
        for r in range(p-1):
            prod = table * np.roll(table,-r,axis=0)
            f = np.fft.fft(prod,axis=1)
            wf = np.fft.fft(prod*mask,axis=1)
            vals[r,:] = np.fft.ifft((wf.conjugate()*f).sum(axis=0)).real / p
        vals[0,:] = np.nan
        vals[:,0] = np.nan
        flat = np.nanargmax(np.abs(vals))
        r,s = np.unravel_index(flat,vals.shape)
        top = np.argsort(np.nan_to_num(np.abs(vals),nan=-1).ravel())[-20:][::-1]
        rows.append({
            "cube_coset":c,
            "max_abs_origin_over_p3":float(abs(vals[r,s])),
            "max_abs_origin_over_p4":float(abs(vals[r,s])/p),
            "max_ratios":[int(powers[r]),int(powers[s])],
            "largest":[{"m_ratio":int(powers[a]),"n_ratio":int(powers[b]),
                        "origin_real_over_p3":float(vals[a,b])}
                       for a,b in [np.unravel_index(k,vals.shape) for k in top]],
        })
    return {"ratio_pairs_per_coset":(p-2)**2,"rows":rows}


def run(p: int, args) -> dict:
    assert prime(p) and p > 3
    started = time.monotonic()
    inv = inverse_table(p)
    corr,checks = make_correlation(p,inv)
    if p <= 11:
        checks.update(direct_check(p,inv,corr))
    cases = case_list(p,inv,p <= args.exhaustive_through)
    r1,r2 = np.indices((p,p),dtype=np.int64)
    base = (r1*r1*inv[r2] % p,r2*r2*inv[r1] % p)
    cosets = range(3 if args.all_cosets and (p-1)%3 == 0 else 1)
    rows = [spectrum_row(p,inv,corr,r,s,names,c,base) for c in cosets for r,s,names in cases]
    out = {"p":p,"p_mod_3":p%3,"checks":checks,
           "sample_count":len(rows),"max_kernel_over_sqrt_p":float(np.abs(corr).max()),
           "rows":rows}
    if p <= args.all_origins_through:
        out["all_origins"] = all_origin_ratios(p,corr)
        # Independently validate the multiplicative FFT's three strongest cases by physical sums.
        cross = []
        for r in out["all_origins"]["rows"]:
            R,S = r["max_ratios"]
            direct = spectrum_row(p,inv,corr,R,S,["multiplicative_FFT_validation"],r["cube_coset"],base)
            delta = abs(abs(direct["origin_real_over_p3"])-r["max_abs_origin_over_p3"])
            assert delta < 1e-7
            cross.append(delta)
        checks["multiplicative_FFT_origin_residuals"] = cross
    out["elapsed_seconds"] = time.monotonic()-started
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--primes",nargs="+",type=int,default=[5,7,11,17,31,61,101,211,401,809])
    parser.add_argument("--exhaustive-through",type=int,default=31)
    parser.add_argument("--all-origins-through",type=int,default=211)
    parser.add_argument("--all-cosets",action="store_true")
    parser.add_argument("--output",type=Path,default=Path(__file__).with_suffix(".json"))
    args = parser.parse_args()
    receipt = {
        "status":"FINITE_FLOATING_POINT_STRESS_TEST_ONLY",
        "target":"TypeIIILocal.lean: FiniteExceptionalFourierBound for distinct nonzero indices",
        "convention":"positive phase, unnormalized two-dimensional Fourier transform",
        "normalizations":"corr table = C(1/u,1/v,1)/sqrt(p); recorded hat = actual W_hat/p^3",
        "limitations":"Finite samples do not establish uniform constants or an asymptotic counterexample.",
        "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "numpy_version":np.__version__,
        "records":[],
    }
    args.output.parent.mkdir(parents=True,exist_ok=True)
    for p in args.primes:
        row = run(p,args)
        receipt["records"].append(row)
        args.output.write_text(json.dumps(receipt,indent=2)+"\n")
        worst = max(row["rows"],key=lambda r:r["max_over_p3"])
        origin = max(row["rows"],key=lambda r:abs(r["origin_real_over_p3"]))
        print(json.dumps({"p":p,"samples":row["sample_count"],
             "elapsed_seconds":row["elapsed_seconds"],
             "worst":{"ratios":[worst["m_ratio"],worst["n_ratio"]],"cube_coset":worst["cube_coset"],
                      "max_over_p3":worst["max_over_p3"],"top":worst["largest_frequencies"][:2]},
             "worst_origin":{"ratios":[origin["m_ratio"],origin["n_ratio"]],
                      "origin_over_p3":origin["origin_real_over_p3"]},
             "all_origin_maxima":[{"cube_coset":r["cube_coset"],"ratios":r["max_ratios"],
                 "max_over_p3":r["max_abs_origin_over_p3"]}
                 for r in row.get("all_origins",{}).get("rows",[])]}),flush=True)


if __name__ == "__main__":
    main()
