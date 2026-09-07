#!/usr/bin/env python3
"""Positive repeated-index controls for the Type III normalization.

The repeated cases are permitted to have an origin of order p^4. Comparing
them with distinct cases checks that the diagnostic can see that scale.
"""

import hashlib
import json
from pathlib import Path

from structured_fourier_screen import inverse_table, make_correlation, np


def main():
    receipt={"status":"FINITE_FLOATING_POINT_NORMALIZATION_CONTROLS_ONLY",
             "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             "dependency_sha256":hashlib.sha256(Path(__file__).with_name('structured_fourier_screen.py').read_bytes()).hexdigest(),
             "records":[]}
    for p in [101,401,1201,2003]:
        inv=inverse_table(p)
        corr,checks=make_correlation(p,inv)
        r1,r2=np.indices((p,p),dtype=np.int64)
        u=r1*r1*inv[r2]%p
        v=r2*r2*inv[r1]%p
        rows=[]
        for R,S,name in [(1,1,"both_repeated"),(1,2,"row_repeated"),(2,3,"distinct_generic"),(p-1,p-1,"distinct_both_signs")]:
            w=corr[u,v]*corr[R*u%p,v]*corr[R*u%p,S*v%p]*corr[u,S*v%p]
            rows.append({"m_ratio":R,"n_ratio":S,"case":name,
                         "origin_over_p3":float(w.sum()/p),
                         "origin_over_p4":float(w.mean())})
        receipt["records"].append({"p":p,"checks":checks,"rows":rows})
        print(json.dumps({"p":p,"rows":rows}),flush=True)
    Path(__file__).with_suffix('.json').write_text(json.dumps(receipt,indent=2)+'\n')


if __name__=='__main__':
    main()
