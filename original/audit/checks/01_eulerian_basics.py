"""Check 01 - Eulerian preliminaries and the Cayley coordinate change (Candidate A sec. 2,
Candidate B 'Eulerian preliminaries').  All exact.

What is certified here, for the stated finite ranges only:
  * three independent constructions of A_n agree (S_n enumeration, closed form, recurrence)
  * degree n-1, monic, constant term 1, positive palindromic coefficients, A_n(1)=n!
  * A_n squarefree with n-1 distinct real roots, all negative (my own Sturm counts)
  * strict interlacing of A_n and A_{n+1} with the exact gap pattern claimed
  * C_j: two constructions agree; degree, leading coeff j!, parity, C_j(+-1), zero at 0
  * roots of C_j: j-1 distinct, all inside (-1,1)
"""
import json
import sys
from math import factorial
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from eul import *  # noqa

NB = 8      # brute force over S_n
N = 60      # recurrence / closed form / root counts
NI = 40     # interlacing pattern

res = {}

# --- three constructions
A = eulerian_polys_recurrence(N)
Acf = eulerian_polys_closed_form(N)
for n in range(N + 1):
    assert A[n] == Acf[n], n
for n in range(NB + 1):
    assert [int(c.p) for c in A[n].coeffs()] == eulerian_coeffs_bruteforce(n), n
assert [int(c.p) for c in A[2].coeffs()] == [1, 1]
assert [int(c.p) for c in A[3].coeffs()] == [1, 4, 1]
res['constructions_agree'] = {'bruteforce_n': [0, NB], 'closed_form_vs_recurrence_n': [0, N]}

# --- shape
for n in range(1, N + 1):
    co = [int(c.p) for c in A[n].coeffs()]
    assert len(co) == n and co[-1] == 1 and co[0] == 1
    assert all(c > 0 for c in co) and co == co[::-1]
    assert A[n](Q(1)) == factorial(n)
res['shape_checked_n'] = [1, N]

# --- real, simple, negative roots
for n in range(2, N + 1):
    p = A[n]
    assert is_squarefree(p)
    assert count_distinct_real_roots(p) == n - 1
    assert count_distinct_real_roots(p, '-inf', Q(0)) == n - 1
res['simple_negative_roots_n'] = [2, N]

# --- strict interlacing pattern: A_{j+1}, A_j, A_{j+1}, ..., A_j, A_{j+1}
for j in range(2, NI):
    lo = -Q(4) * factorial(j + 1)  # crude Cauchy-type bound: all roots > -(1+max coeff)
    lo = -(Q(1) + max(abs(c) for c in A[j + 1].coeffs()))
    order = merged_root_order({'lo': A[j], 'hi': A[j + 1]}, lo, Q(0))
    expect = ['hi'] + ['lo', 'hi'] * (j - 1)
    assert order == expect, (j, order)
res['consecutive_interlacing_pattern_j'] = [2, NI - 1]

# --- Cayley polynomials
C = cayley_polys(N)
for j in range(1, N + 1):
    assert C[j] == cayley_from_A(A[j], j), j                 # T-recurrence == substitution
    assert C[j].degree() == j - 1
    assert C[j].leading_coefficient() == factorial(j)
    assert C[j](Q(1)) == 2 ** (j - 1) and C[j](Q(-1)) == (-2) ** (j - 1)
    # parity C_j(-z) = (-1)^(j-1) C_j(z)
    co = C[j].coeffs()
    assert all(co[k] == 0 for k in range(len(co)) if (k - (j - 1)) % 2 != 0)
    # zero at zero exactly when j even, and simple
    if j % 2 == 0:
        assert co[0] == 0 and co[1] != 0
    else:
        assert co[0] != 0
    if j >= 2:
        assert is_squarefree(C[j])
        assert count_distinct_real_roots(C[j], Q(-1), Q(1)) == j - 1
res['cayley_checked_j'] = [1, N]

# small explicit values quoted in the submissions
assert C[2] == fmpq_poly([0, 2]) and C[3] == fmpq_poly([-2, 0, 6])
assert C[4] == fmpq_poly([0, -16, 0, 24])

print(json.dumps({'check': '01_eulerian_basics', 'status': 'PASS', **res}, indent=1))
