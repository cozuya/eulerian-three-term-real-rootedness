"""Check 06 - Candidate B: partial theorem, full-bound reduction, finite certificates and
the auxiliary obstruction.  All exact.  Finite ranges cannot prove an all-degree statement.

Part 1  generic algebra (sympy, F and G treated as arbitrary):
          partial-fraction form of R and of R' for symbolic roots
          derivative reciprocity
          F*P - [(d^2-bd-xd+c) F^2 + q W] = (G+dF)(G-dF+(x+b)F)         [B's root identity]
          F*P = Q_d^2 + (c-d^2-2) F^2 - N       with b = 2d-2             [B's (7) == A's (5.4)]
          pairing identity behind (8) and the factorisation of t^4-4t^2+4t-1
Part 2  actual Eulerian triples, m in [1, M]:
          H F = G^2 + x G F + q (G'F - G F'),  palindromicity,  N two forms agree
          R' >= 1  <=>  W - F^2 >= 0 on R (identically 0 for m=1, strictly > 0 for m>=2)
          Q = G + dF: m distinct negative roots, pattern Q F Q ... F Q
          P F < 0 at every root of Q (Tarski), also the sharper P/F <= r
          P_n has n-1 distinct negative roots on and inside B's boundary (Sturm)
Part 3  B's finite certificates for the full bound, recomputed without B's intervals,
        and extended beyond m=15 as a diagnostic on B's open inequality (6)
Part 4  the auxiliary obstruction, recomputed with my own Sturm count
"""
import json
import sys
import time
from fractions import Fraction
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parent))
from eul import *  # noqa

t0 = time.time()
ARCHIVE = Path(sys.argv[1]) if len(sys.argv) > 1 else None

# =============================================================== Part 1: generic algebra
x, b, c, d, t, a = sp.symbols('x b c d t a')
qx = x * (1 - x)
# R and R' for symbolic roots (m = 4: three roots)
a1, a2, a3 = sp.symbols('a1 a2 a3')
mm = 4
Fs = (x - a1) * (x - a2) * (x - a3)
Gs = (1 + mm * x) * Fs + qx * sp.diff(Fs, x)
Rs = Gs / Fs
Rpf = x + 1 + sum((1 - ai) * x / (x - ai) for ai in (a1, a2, a3))
assert sp.cancel(Rs - Rpf) == 0
assert sp.cancel(sp.diff(Rs, x) - (1 - sum(ai * (1 - ai) / (x - ai) ** 2 for ai in (a1, a2, a3)))) == 0
# derivative reciprocity: differentiating R(1/x) = R(x)/x gives -R'(1/x)/x^2 = R'(x)/x - R(x)/x^2.
# With R' = W/F^2, W = G'F - GF', and F,G palindromic of degrees m-1,m this is the polynomial
# identity  rev_{2m-2}(W) = G F - x W,  which is checked on the actual triples in Part 2.
# root identity and (7), F,G,W generic, H := (G^2 + x G F + q W)/F
F, G, W = sp.symbols('F G W')
H = (G ** 2 + x * G * F + qx * W) / F
P = H + b * G + c * F
assert sp.expand(sp.cancel(F * P) - ((d ** 2 - b * d - x * d + c) * F ** 2 + qx * W)
                 - (G + d * F) * (G - d * F + (x + b) * F)) == 0
Nsym = G ** 2 - F * H + 2 * F * G - 2 * F ** 2
assert sp.expand(sp.cancel((F * P).subs(b, 2 * d - 2)) - ((G + d * F) ** 2 + (c - d ** 2 - 2) * F ** 2 - sp.cancel(Nsym))) == 0
assert sp.expand(sp.cancel(Nsym) - (-qx * W + (2 - x) * G * F - 2 * F ** 2)) == 0
# B's partial bound: d = (b+1)/2 gives d^2-(b+1)d+c-(1-r) = c-1-(b+1)^2/4+r
r = sp.symbols('r')
dd = (b + 1) / 2
assert sp.expand(dd ** 2 - (b + 1) * dd + c - (1 - r) - (c - 1 - (b + 1) ** 2 / 4 + r)) == 0
assert sp.expand((b ** 2 / 4 + b + 3) - (1 + (b + 1) ** 2 / 4) - (b / 2 + sp.Rational(7, 4))) == 0
# (8): one root -a contributes t(a+1)(t^2+2t-a)/(a-t)^2 to N/F^2 at x=-t
term = lambda s: t * (s + 1) * (t ** 2 + 2 * t - s) / (s - t) ** 2
ai = -a
one = (x * (1 - ai) * (2 * x - x ** 2 - ai) / (x - ai) ** 2).subs(x, -t)
assert sp.cancel(one - term(a)) == 0
pair = t * (a + 1) ** 2 * a * (t ** 4 - 4 * t ** 2 + 2 * (a + 1 / a) * t - 1) / ((a - t) ** 2 * (a * t - 1) ** 2)
assert sp.cancel(term(a) + term(1 / a) - pair) == 0
assert sp.expand(t ** 4 - 4 * t ** 2 + 4 * t - 1 - (t - 1) ** 2 * (t ** 2 + 2 * t - 1)) == 0
# N/F^2 = (2-x)R - qR' - 2 has no non-sum part
assert sp.expand((2 - x) * (1 + x) - qx - 2) == 0

# =============================================================== Part 2: Eulerian triples
M = 40
NBIG = 90
A = eulerian_polys_recurrence(NBIG + 1)
QX = fmpq_poly([0, 1, -1])
B_GRID = [Fraction(0), Fraction(1, 10 ** 9), Fraction(1, 3), Fraction(1), Fraction(2), Fraction(10),
          Fraction(100), Fraction(10 ** 6)]


def bbound(bv):
    return 1 + (Fraction(bv) + 1) ** 2 / 4


stats = {'triples': 0, 'separator': 0, 'tarski': 0, 'sturm': 0}
for m in range(1, M + 1):
    Fm, Gm, Hm = A[m], A[m + 1], A[m + 2]
    Wm = Gm.derivative() * Fm - Gm * Fm.derivative()
    assert Hm * Fm == Gm * Gm + X * Gm * Fm + QX * Wm
    for pol in (Fm, Gm, Hm):
        co = pol.coeffs()
        assert co == co[::-1]
    wco = Wm.coeffs() + [Q(0)] * (2 * m - 1 - len(Wm.coeffs()))
    assert len(wco) == 2 * m - 1
    assert fmpq_poly(wco[::-1]) == Gm * Fm - X * Wm                  # R'(1/x) = R(x) - x R'(x)
    N1 = Gm * Gm - Fm * Hm + 2 * Fm * Gm - 2 * Fm * Fm
    N2 = -QX * Wm + fmpq_poly([2, -1]) * Gm * Fm - 2 * Fm * Fm
    assert N1 == N2
    D = Wm - Fm * Fm                      # R' - 1 = D / F^2
    if m == 1:
        assert D.is_zero() and N1.is_zero()
    else:
        assert real_root_multiset_count(D) == 0 and D(Q(0)) > 0     # R' > 1 everywhere off poles
    stats['triples'] += 1
    for bv in B_GRID:
        dv = (bv + 1) / 2
        Qm = Gm + Q(dv) * Fm
        assert Qm.degree() == m and is_squarefree(Qm) and coprime(Qm, Fm)
        assert count_distinct_real_roots(Qm, '-inf', Q(0)) == m
        if 2 <= m <= 20:
            lo = -(Q(2) + max(abs(cc) for cc in Qm.coeffs()))
            order = merged_root_order({'Q': Qm, 'F': Fm}, lo, Q(0))
            assert order == ['Q'] + ['F', 'Q'] * (m - 1)
        stats['separator'] += 1
        for frac in (Fraction(0), Fraction(1, 2), Fraction(1)):
            cv = frac * bbound(bv)
            Pm = Hm + Q(bv) * Gm + Q(cv) * Fm
            assert tarski_query(Pm * Fm, Qm, '-inf', Q(0)) == -m          # P/F < 0 at every root of Q
            sharper = tarski_query((Pm - X * Fm) * Fm, Qm, '-inf', Q(0))  # sign of P/F - r
            if m == 1 and frac == 1:
                assert sharper == 0                                       # equality P/F = r exactly
            else:
                assert sharper == -m
            stats['tarski'] += 1
for n in range(3, NBIG + 1):
    for bv in B_GRID:
        for frac in ((Fraction(0), Fraction(1, 2), Fraction(1)) if n <= 40 else (Fraction(1),)):
            cv = frac * bbound(bv)
            Pm = A[n] + Q(bv) * A[n - 1] + Q(cv) * A[n - 2]
            assert count_distinct_real_roots(Pm, '-inf', Q(0)) == n - 1
            stats['sturm'] += 1

# =============================================================== Part 3: certificates
supplied = None
if ARCHIVE is not None:
    supplied = json.loads((ARCHIVE / 'candidate_B' / 'eulerian_attempt' / 'exact_reduction_checks.json').read_text())
    sup_rows = {row['m']: row for row in supplied['finite_degree_certificates']}
cert = []
MC = 40
first_fail = None
for m in range(2, MC + 1):
    Fm, Gm, Hm = A[m], A[m + 1], A[m + 2]
    Nm = Gm * Gm - Fm * Hm + 2 * Fm * Gm - 2 * Fm * Fm
    assert Nm.degree() == 2 * m - 1 and Nm.leading_coefficient() < 0 and Nm(Q(0)) == 0
    assert is_squarefree(Nm)
    Em = fmpq_poly(Nm.coeffs()[1:])                  # N_m / x
    assert Em(Q(0)) != 0
    nneg = count_distinct_real_roots(Em, '-inf', Q(0))
    Q1 = Gm + Fm
    # isolate the largest root beta of Q1 and decide on which side of alpha it lies
    lo = -(Q(2) + max(abs(cc) for cc in Q1.coeffs()))
    ivs = isolate_roots(Q1, lo, Q(0))
    assert len(ivs) == m
    iv = ivs[-1]
    for _ in range(200):
        if Em(iv[0]) != 0 and Em(iv[1]) != 0 and count_distinct_real_roots(Em, iv[0], iv[1]) == 0:
            break
        iv = refine(Q1, iv)
    else:
        raise RuntimeError('could not separate beta from the roots of N')
    roots_right_of_beta = count_distinct_real_roots(Em, iv[1], Q(0))
    ok = (nneg == 1 and roots_right_of_beta == 1 and Em(iv[0]) != 0 and sgn(Nm(iv[0])) > 0)
    # ok  <=>  N_m > 0 on (-inf, alpha), exactly one negative root alpha, and beta < alpha
    if supplied is not None and m in sup_rows:
        assert [str(v) for v in Nm.coeffs()[::-1]] == sup_rows[m]['N_coefficients_highest_first']
        al_lo, al_hi = [Fraction(s) for s in sup_rows[m]['N_negative_root_interval']]
        be_lo, be_hi = [Fraction(s) for s in sup_rows[m]['Q1_largest_root_interval']]
        assert be_lo < be_hi < al_lo < al_hi < 0
        assert count_distinct_real_roots(Em, Q(al_lo), Q(al_hi)) == 1
        assert count_distinct_real_roots(Q1, Q(be_lo), Q(be_hi)) == 1
        assert count_distinct_real_roots(Q1, Q(be_hi), Q(0)) == 0
    cert.append({'m': m, 'n': m + 2, 'N_negative_roots': nneg, 'beta_lt_alpha': bool(ok)})
    if not ok and first_fail is None:
        first_fail = m
assert all(row['beta_lt_alpha'] for row in cert if row['m'] <= 15)      # B's stated range

# n=4 discriminant positivity on the full region (B's symbolic n=4 certificate), redone
bs, cs, ts = sp.symbols('b c t')
A4 = 1 + 11 * x + 11 * x ** 2 + x ** 3
A3 = 1 + 4 * x + x ** 2
A2 = 1 + x
D4 = sp.discriminant(A4 + bs * A3 + cs * A2, x)
bnd = bs ** 2 / 4 + bs + 3
pos = sp.Poly(sp.cancel((1 + ts) ** 3 * D4.subs(cs, bnd * ts / (1 + ts))), bs, ts)
assert all(co > 0 for co in pos.coeffs())
assert sp.expand(sp.factor(D4.subs(cs, bnd)) - (bs + 1) * (bs ** 4 + 40 * bs ** 3 + 616 * bs ** 2 + 4064 * bs + 8400) / 4) == 0

# =============================================================== Part 4: the obstruction
Tk = lambda k, p: fmpq_poly([1, k]) * p + QX * p.derivative()
h0 = fmpq_poly([1, 1]) ** 10
Fo = Tk(11, h0)
Go = Tk(12, Fo)
Ho = Tk(13, Go)
Po = Ho + 4 * Go + 11 * Fo
S = fmpq_poly([16, 686, 5657, 13796, 3206, 158, 1])
assert Po == fmpq_poly([1, 1]) ** 7 * S
assert Fraction(4) ** 2 / 4 + 4 + 3 == 11                       # (4,11) is on the proposed boundary
assert 11 > bbound(4)                                           # ...and outside B's own region
assert is_squarefree(S)
s_real = count_distinct_real_roots(S)
assert s_real == 4 and S(Q(-1)) != 0
assert real_root_multiset_count(Po) == 11 and Po.degree() == 13
# why it is not an Eulerian triple, and which of A's hypotheses it violates
assert Fo == fmpq_poly([1, 1]) ** 9 * fmpq_poly([1, 22, 1])     # 9-fold root at x=-1: not simple
assert Fo != A[12] and Fo.degree() == A[12].degree()
# B's own region on the same (non-Eulerian) triple: still real-rooted at B's boundary
Pb = Ho + 4 * Go + Q(bbound(4)) * Fo
assert real_root_multiset_count(Pb) == 13

print(json.dumps({'check': '06_candidate_B', 'status': 'PASS', 'seconds': round(time.time() - t0, 1),
                  'generic_identities': 'all exact zero',
                  'eulerian_triples_m': [1, M], 'counts': stats, 'sturm_n': [3, NBIG],
                  'certificates_recomputed_m': [2, MC],
                  'supplied_certificate_json_cross_checked': supplied is not None,
                  'certificate_pattern_holds_for_all_m_up_to': (MC if first_fail is None else first_fail - 1),
                  'first_m_where_pattern_fails': first_fail,
                  'n4_discriminant_positive_on_region': True,
                  'obstruction': {'P_degree': 13, 'real_roots_with_multiplicity': 11, 'sextic_real_roots': s_real,
                                  'F_has_9fold_root': True, 'c_outside_B_region': True}}, indent=1))
