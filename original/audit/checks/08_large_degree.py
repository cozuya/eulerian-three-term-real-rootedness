"""Check 08 - large-degree spot checks (exact).  Purely a falsification attempt: a failure
here would refute Candidate A; a pass proves nothing beyond the listed cases.

  * Corollary 3.2 (the only Eulerian-specific input) by Sturm-Tarski for selected large n
  * P_n on the boundary c = b^2/4+b+3: n-1 distinct negative roots, selected large n
  * (5.5) on the negative half for the same n, on the boundary
"""
import json
import sys
import time
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from eul import *  # noqa

NS = [int(a) for a in sys.argv[1:]] or [60, 80, 100, 130, 160]
NMAX = max(NS) + 1
t0 = time.time()
A = eulerian_polys_recurrence(NMAX)
C = cayley_polys(NMAX)
ZP = fmpq_poly([1, 1])


def strip_z(p):
    co = p.coeffs()
    return (fmpq_poly(co[1:]), True) if co[0] == 0 else (p, False)


rows = []
for n in NS:
    t1 = time.time()
    m = n - 2
    f, g, h = C[m], C[m + 1], C[m + 2]
    p = (m - 1) // 2
    fpos, _ = strip_z(f)
    assert count_distinct_real_roots(fpos, Q(0), Q(1)) == p
    assert tarski_query(h * g, fpos, Q(0), Q(1)) == p                 # Corollary 3.2 at level n
    row = {'n': n, 'positive_roots_of_C_{n-2}': p, 'cor_3_2': True, 'boundary_cases': []}
    for b in (Fraction(0), Fraction(1), Fraction(100)):
        c = b * b / 4 + b + 3
        P = A[n] + Q(b) * A[n - 1] + Q(c) * A[n - 2]
        assert count_distinct_real_roots(P, '-inf', Q(0)) == n - 1
        q = g + Q(b / 2 + 1) * ZP * f
        Pz = h + Q(b) * ZP * g + Q(c) * ZP * ZP * f
        assert tarski_query(Pz * f, q, Q(-1), Q(0)) == -(p + 1)       # (5.5) on the boundary
        row['boundary_cases'].append(str(b))
    row['seconds'] = round(time.time() - t1, 1)
    rows.append(row)
    print(json.dumps(row), flush=True)

print(json.dumps({'check': '08_large_degree', 'status': 'PASS', 'n_values': NS,
                  'seconds': round(time.time() - t0, 1)}))
