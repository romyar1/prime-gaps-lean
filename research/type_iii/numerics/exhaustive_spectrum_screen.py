#!/usr/bin/env python3
"""Exhaustive finite-prime spectra for distinct ratios, with a compact receipt.

All residue parameters reduce to the ratios and cube classes described in
README.md; each run checks every normalized parameter choice and frequency.
The calculations are floating-point diagnostics, not uniform estimates.
"""

import argparse
import hashlib
import heapq
import json
from pathlib import Path
import time

from structured_fourier_screen import (inverse_table, make_correlation,
                                      spectrum_row, np)


def run(p):
    started = time.monotonic()
    inv = inverse_table(p)
    corr, checks = make_correlation(p, inv)
    r1,r2 = np.indices((p,p), dtype=np.int64)
    base = (r1*r1*inv[r2] % p, r2*r2*inv[r1] % p)
    num_cosets = 3 if (p-1)%3 == 0 else 1
    top = []
    thresholds = [2,4,6,8,10,16]
    coeff_counts = dict.fromkeys(thresholds,0)
    max_exception_counts = dict.fromkeys(thresholds,0)
    sequence = 0
    worst_origin = None
    for c in range(num_cosets):
        for R in range(2,p):
            for S in range(2,p):
                row = spectrum_row(p,inv,corr,R,S,["all_distinct_parameters"],c,base)
                sequence += 1
                candidate = (row["max_over_p3"],sequence,row)
                if len(top) < 20:
                    heapq.heappush(top,candidate)
                elif candidate[:2] > top[0][:2]:
                    heapq.heapreplace(top,candidate)
                if worst_origin is None or abs(row["origin_real_over_p3"]) > abs(worst_origin["origin_real_over_p3"]):
                    worst_origin = row
                for t in thresholds:
                    n = row["counts_above_multiple_p3"][str(t)]
                    coeff_counts[t] += n
                    max_exception_counts[t] = max(max_exception_counts[t],n)
    return {"p":p,"checks":checks,"normalized_parameter_sets":sequence,
            "fourier_coefficients_evaluated":sequence*p*p,
            "maximum_over_p3":max(x[0] for x in top),
            "coefficient_counts_above_multiple_p3":coeff_counts,
            "max_count_for_single_parameter_set_above_multiple_p3":max_exception_counts,
            "worst_origin":worst_origin,
            "largest_parameter_spectra":[x[2] for x in sorted(top,reverse=True)],
            "elapsed_seconds":time.monotonic()-started}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--primes",type=int,nargs="+",default=[61,101])
    parser.add_argument("--output",type=Path,default=Path(__file__).with_suffix(".json"))
    args=parser.parse_args()
    receipt={"status":"EXHAUSTIVE_AT_LISTED_PRIMES_FLOATING_POINT_ONLY",
             "normalization":"Actual positive-phase W_hat divided by p^3.",
             "all_parameter_reduction":"m=alpha=1, n runs through cube classes, R,S run through F_p^* minus{1}.",
             "limitations":"This finite search neither proves uniform bounds nor identifies optimal constants.",
             "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             "dependency_sha256":hashlib.sha256(Path(__file__).with_name('structured_fourier_screen.py').read_bytes()).hexdigest(),
             "records":[]}
    for p in args.primes:
        row=run(p)
        receipt["records"].append(row)
        args.output.write_text(json.dumps(receipt,indent=2)+"\n")
        print(json.dumps({k:v for k,v in row.items() if k not in ["worst_origin","largest_parameter_spectra"]}),flush=True)


if __name__=="__main__":
    main()
