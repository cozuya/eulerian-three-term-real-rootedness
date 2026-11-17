"""Check 05 - Candidate A sections 5-6: separator q, the two families of test points, the
sign pattern, the root count, and the boundary cases.  All exact (Sturm / Sturm-Tarski /
rational isolating intervals).  Finite ranges only -- this cannot prove the theorem.

Per (m, b):      q has degree m, m simple roots in (-1,1), pattern q f q ... f q,
                 and exactly p+1 negative roots  (p = floor((m-1)/2)).
Per (m, b, c):   (5.5)  P f < 0 at every negative root of q          [Tarski query]
                 (5.6)  P g > 0 at every positive root of f          [Tarski query]
                 P(0) = -b f'(0) when f is odd
                 full order on (-1,1):  P-root, T, P-root, ..., T, P-root  with the m test
                 points T = {negative roots of q} U {non-negative roots of f}
                 and P_n(x) squarefree with n-1 negative roots         [Sturm in x]
Boundary cases:  n=3 (double root on the boundary, non-real just above it)
                 b=0 with n even (Case III): real-rooted; root at x=-1; the roots are in
                 fact simple because the only possible double root needs
                 c = c*_n = -C_n'(0)/C_{n-2}'(0) = T_{n+1}/T_{n-1} >= 8 > 3  (auditor's remark)
Large degrees:   Sturm counts on and inside the boundary up to n = NBIG.
"""
import json
import random
import sys
import time
from fractions import Fraction
from math import factorial
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from eul import *  # noqa

t0 = time.time()
M_PATTERN = 22       # full merged-order pattern for m <= M_PATTERN
M_TARSKI = 34        # Tarski-query sign checks for m <= M_TARSKI
NBIG = 90            # plain Sturm root counts up to this n
A = eulerian_polys_recurrence(NBIG + 1)
C = cayley_polys(NBIG + 1)
ZP = fmpq_poly([1, 1])


def strip_z(p):
    co = p.coeffs()
    return (fmpq_poly(co[1:]), True) if co[0] == 0 else (p, False)


def bound(b):
    b = Fraction(b)
    return b * b / 4 + b + 3


def Pz(m, b, c):
    return C[m + 2] + Q(b) * ZP * C[m + 1] + Q(c) * ZP * ZP * C[m]


def Px(n, b, c):
    return A[n] + Q(b) * A[n - 1] + Q(c) * A[n - 2]


B_GRID = [Fraction(0), Fraction(1, 10 ** 9), Fraction(1, 1000), Fraction(1, 4), Fraction(1), Fraction(2),
          Fraction(10), Fraction(100), Fraction(10 ** 6), Fraction(10 ** 12)]
T_GRID = [Fraction(0), Fraction(1, 3), Fraction(1) - Fraction(1, 10 ** 9), Fraction(1)]

stats = {'q_structure': 0, 'tarski_5_5': 0, 'tarski_5_6': 0, 'zero_point': 0, 'full_pattern': 0,
         'sturm_x': 0}

# ------------------------------------------------------------------ structure + signs
for m in range(2, M_TARSKI + 1):
    f, g, h = C[m], C[m + 1], C[m + 2]
    f_odd = (m % 2 == 0)                       # deg f = m-1
    p = (m - 1) // 2
    fpos, _ = strip_z(f)
    assert (count_distinct_real_roots(fpos, Q(0), Q(1)) if fpos.degree() > 0 else 0) == p
    for b in B_GRID:
        al = b / 2 + 1
        q = g + Q(al) * ZP * f
        assert q.degree() == m and is_squarefree(q) and coprime(q, f)
        assert count_distinct_real_roots(q, Q(-1), Q(1)) == m
        assert q(Q(0)) != 0
        assert count_distinct_real_roots(q, Q(-1), Q(0)) == p + 1
        if m <= M_PATTERN:
            order = merged_root_order({'q': q, 'f': f}, Q(-1), Q(1))
            assert order == ['q'] + ['f', 'q'] * (m - 1), (m, b)
        stats['q_structure'] += 1
        for t in T_GRID:
            c = t * bound(b)
            P = Pz(m, b, c)
            assert P.degree() == m + 1
            # (5.5)
            assert tarski_query(P * f, q, Q(-1), Q(0)) == -(p + 1), (m, b, c)
            stats['tarski_5_5'] += 1
            # (5.6)
            if p:
                assert tarski_query(P * g, fpos, Q(0), Q(1)) == p, (m, b, c)
                # equivalently sign P = -sign f' there
                assert tarski_query(P * f.derivative(), fpos, Q(0), Q(1)) == -p
                stats['tarski_5_6'] += 1
            if f_odd:
                assert P(Q(0)) == -Q(b) * f.derivative()(Q(0))
                assert sgn(f.derivative()(Q(0))) == (-1) ** p
                stats['zero_point'] += 1
            # endpoint signs
            assert sgn(P(Q(-1))) == (-1) ** (m + 1) and P(Q(1)) > 0
            # full pattern (needs P(0) != 0 when f is odd, i.e. b > 0)
            if m <= M_PATTERN and b in (Fraction(0), Fraction(1, 1000), Fraction(1), Fraction(100)) \
                    and t in (Fraction(0), Fraction(1)) and not (f_odd and b == 0):
                order = merged_root_order({'P': P, 'q': q, 'f': f}, Q(-1), Q(1))
                qi = [i for i, l in enumerate(order) if l == 'q']
                fi = [i for i, l in enumerate(order) if l == 'f']
                tests = set(qi[:p + 1]) | set(fi[len(fi) - (p + (1 if f_odd else 0)):])
                seq = ['P' if order[i] == 'P' else 'T' for i in range(len(order)) if order[i] == 'P' or i in tests]
                assert len(tests) == m
                assert seq == ['P'] + ['T', 'P'] * m, (m, b, c, seq)
                stats['full_pattern'] += 1

# ------------------------------------------------------------------ Sturm counts in x, big n
random.seed(7)
rand_params = []
for _ in range(12):
    b = Fraction(random.randint(0, 4000), random.randint(1, 400))
    c = bound(b) * Fraction(random.randint(0, 1000), 1000)
    rand_params.append((b, c))
simple_ok = 0
for n in range(4, NBIG + 1):
    grid = [(b, t * bound(b)) for b in B_GRID for t in T_GRID] + rand_params
    if n > 40:   # thin the grid at high degree, always keeping the boundary
        grid = [(b, bound(b)) for b in B_GRID] + rand_params[:4]
    for b, c in grid:
        P = Px(n, b, c)
        assert P.degree() == n - 1 and P.leading_coefficient() == 1
        assert count_distinct_real_roots(P, '-inf', Q(0)) == n - 1, (n, b, c)   # n-1 distinct negative roots
        stats['sturm_x'] += 1
        simple_ok += 1

# ------------------------------------------------------------------ n = 3
n3 = []
for b in B_GRID:
    c = bound(b)
    P = Px(3, b, c)
    assert P == (fmpq_poly([Q(b / 2 + 2), 1])) ** 2
    assert count_distinct_real_roots(P) == 1 and real_root_multiset_count(P) == 2
    above = Px(3, b, c + Fraction(1, 10 ** 12))
    assert count_distinct_real_roots(above) == 0
    below = Px(3, b, c - Fraction(1, 10 ** 12))
    assert count_distinct_real_roots(below, '-inf', Q(0)) == 2
    n3.append(str(b))

# ------------------------------------------------------------------ Case III: b = 0, n even
def tangent_numbers(K):
    """T_1, T_3, ..., from tan x = sum T_{2k+1} x^{2k+1}/(2k+1)!  (Seidel/boustrophedon-free: use
    the ODE y' = 1 + y^2 on exact rational power series)."""
    L = 2 * K + 2
    y = [Fraction(0)] * (L + 1)
    for k in range(L):
        # (k+1) y_{k+1} = [k==0] + sum_{i+j=k} y_i y_j
        conv = sum(y[i] * y[k - i] for i in range(k + 1))
        y[k + 1] = (Fraction(1 if k == 0 else 0) + conv) / (k + 1)
    return {j: int(y[j] * factorial(j)) for j in range(1, L + 1, 2)}


Tn = tangent_numbers(NBIG // 2 + 2)
assert [Tn[1], Tn[3], Tn[5], Tn[7], Tn[9]] == [1, 2, 16, 272, 7936]
case3 = []
for n in range(4, NBIG + 1, 2):
    cstar = -C[n].derivative()(Q(0)) / C[n - 2].derivative()(Q(0))
    assert cstar == Q(Tn[n + 1], Tn[n - 1])                # closed form of the only double-root value
    assert cstar >= 8
    for c in [Fraction(0), Fraction(1, 2), Fraction(5, 4), Fraction(2), Fraction(3)]:
        P = Px(n, 0, c)
        assert P(Q(-1)) == 0
        assert real_root_multiset_count(P, '-inf', Q(0)) == n - 1      # real-rooted (with multiplicity)
        assert is_squarefree(P)                                        # ...and in fact simple
    # at c = c*_n the root x=-1 really is double (shows the threshold is exact, and outside the region)
    Pd = Px(n, 0, Fraction(int(cstar.p), int(cstar.q)))
    assert Pd(Q(-1)) == 0 and Pd.derivative()(Q(-1)) == 0
    if n <= 12:
        case3.append({'n': n, 'c_star': str(cstar)})

# ------------------------------------------------------------------ per-degree thresholds (diagnostic)
def realrooted(n, b, c):
    return real_root_multiset_count(Px(n, b, c)) == n - 1


thr = []
for n in range(3, 13):
    for b in [Fraction(0), Fraction(1), Fraction(10)]:
        lo, hi = bound(b), bound(b) * 4 + 64
        while realrooted(n, b, hi):
            hi *= 2
        if not realrooted(n, b, lo):
            thr.append({'n': n, 'b': str(b), 'FAIL_AT_BOUNDARY': True})
            continue
        for _ in range(40):
            mid = (lo + hi) / 2
            if realrooted(n, b, mid):
                lo = mid
            else:
                hi = mid
        thr.append({'n': n, 'b': str(b), 'claimed_bound': float(bound(b)), 'first_failure_above_bound_near': float(hi)})

print(json.dumps({'check': '05_root_count', 'status': 'PASS', 'seconds': round(time.time() - t0, 1),
                  'ranges': {'tarski_m': [2, M_TARSKI], 'pattern_m': [2, M_PATTERN], 'sturm_n': [4, NBIG]},
                  'counts': stats, 'n3_boundary_b': n3, 'case_III_c_star': case3,
                  'per_degree_threshold_diagnostic': thr}, indent=1))
