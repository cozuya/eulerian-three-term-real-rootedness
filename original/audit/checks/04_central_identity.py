"""Check 04 - Candidate A section 5: the central polynomial identity (5.4) and the
dictionary between A's Cayley picture and B's x-picture.  All exact.

  * (5.4) proved symbolically for an ARBITRARY smooth f, with g=Tf and h=T(Tf) obtained by
    applying T twice (the submission's expanded formula for h is checked, not assumed)
  * P(z) = h + b(z+1)g + c(z+1)^2 f is the Cayley transform of P_n, for actual n
  * degrees, leading coefficients, endpoint values of P and q
  * A's q is the Cayley transform of B's separator Q_d with d = alpha = 1 + b/2
  * A's bracket and B's N_m are the same object:
        (1+z)^(2m) N_m(x(z)) = (1-z^2) * [ (1-z^2)(f'^2 - f f'') - 2 f f' ]
    i.e. N_m/F^2 = -x E, so A's (5.4) and B's (7) are one identity in two coordinates.
"""
import json
import sys
from fractions import Fraction
from math import factorial
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parent))
from eul import *  # noqa

# ---------- symbolic, generic f
z, al, c = sp.symbols('z alpha c')
f = sp.Function('f')(z)
Tsym = lambda p: (z ** 2 - 1) * sp.diff(p, z) + 2 * z * p
g = Tsym(f)
h = Tsym(g)
b = 2 * al - 2
P = h + b * (z + 1) * g + c * (z + 1) ** 2 * f
q = g + al * (z + 1) * f
f1, f2 = sp.diff(f, z), sp.diff(f, z, 2)
rhs = q ** 2 + (z + 1) ** 2 * (c - al ** 2 - 2) * f ** 2 - (1 - z ** 2) * ((1 - z ** 2) * (f1 ** 2 - f * f2) - 2 * f * f1)
assert sp.expand(P * f - rhs) == 0
assert sp.expand(h - ((z ** 2 - 1) ** 2 * f2 + 6 * z * (z ** 2 - 1) * f1 + (6 * z ** 2 - 2) * f)) == 0
# B's N in Cayley form equals (1-z^2)*bracket, generic f
Ncay = g ** 2 - f * h + 2 * (1 + z) * f * g - 2 * (1 + z) ** 2 * f ** 2
assert sp.expand(Ncay - (1 - z ** 2) * ((1 - z ** 2) * (f1 ** 2 - f * f2) - 2 * f * f1)) == 0
# bound rewrite
bb = sp.symbols('b')
assert sp.expand((bb / 2 + 1) ** 2 + 2 - (bb ** 2 / 4 + bb + 3)) == 0

# ---------- actual Eulerian polynomials
N = 40
A = eulerian_polys_recurrence(N)
C = cayley_polys(N)
ZP = fmpq_poly([1, 1])


def cayley(p, deg):
    """(1+z)^deg * p((z-1)/(z+1)) for a polynomial p of degree <= deg."""
    out = fmpq_poly([0])
    zm = fmpq_poly([-1, 1])
    for k, e in enumerate(p.coeffs()):
        out += e * zm ** k * ZP ** (deg - k)
    return out


for n in range(3, N + 1):
    m = n - 2
    fm, gm, hm = C[m], C[m + 1], C[m + 2]
    F, G, H = A[m], A[m + 1], A[m + 2]
    # P is linear in (b,c): three exact evaluations determine it
    for bv, cv in [(0, 0), (1, 0), (0, 1), (Fraction(7, 3), Fraction(22, 5))]:
        Pn = H + Q(bv) * G + Q(cv) * F
        Pz = hm + Q(bv) * ZP * gm + Q(cv) * ZP * ZP * fm
        assert cayley(Pn, n - 1) == Pz
        assert Pz.degree() == m + 1
        assert Pz.leading_coefficient() == factorial(m + 2) + Q(bv) * factorial(m + 1) + Q(cv) * factorial(m)
        assert Pz(Q(1)) == 2 ** (m + 1) * (1 + Q(bv) + Q(cv))
        assert Pz(Q(-1)) == (-2) ** (m + 1)
    for av in [1, Fraction(3, 2), 5, 1000]:
        qz = gm + Q(av) * ZP * fm
        assert cayley(G + Q(av) * F, m) == qz             # A's q  <->  B's Q_d, d = alpha
        assert qz.degree() == m and qz.leading_coefficient() == factorial(m + 1) + Q(av) * factorial(m)
        assert qz(Q(1)) == 2 ** m * (1 + Q(av)) and qz(Q(-1)) == (-2) ** m == -2 * fm(Q(-1))
    # B's N_m versus A's bracket
    Nm = G * G - F * H + 2 * F * G - 2 * F * F
    d1, d2 = fm.derivative(), fm.derivative().derivative()
    W = fmpq_poly([1, 0, -1])
    Br = W * (d1 * d1 - fm * d2) - 2 * fm * d1
    assert cayley(Nm, 2 * m) == W * Br

print(json.dumps({'check': '04_central_identity', 'status': 'PASS',
                  'generic_f_identity_5_4': 'exact zero',
                  'h_formula': 'exact zero',
                  'N_m_equals_(1-z^2)*bracket_generic_f': 'exact zero',
                  'cayley_dictionary_checked_n': [3, N]}, indent=1))
