"""Check 02 - Candidate A, Lemma 3.1 (positive residues) and Corollary 3.2.  Exact unless
labelled 'diagnostic'.

For each n in [3, N]:
  (a) set-up: F_n=(z^2-1)C_{n-2}, F_n'=C_{n-1}, equal degree/parity, rho_n = n(n-1) > 0
  (b) EXACT positivity of every residue, certified through the equivalent root pattern in
      t=z^2:  zeros and poles of C_n/F_n alternate  N,D,N,D,...,N,D  on (0,1], last pole t=1.
      (With rho>0 and simple poles this pattern is equivalent to all lambda_j>0; the
      equivalence is the elementary sign count written out in AUDIT.md.)
  (c) EXACT Corollary 3.2 by a Sturm-Tarski query:  C_n*C_{n-1} > 0 at every positive root
      of C_{n-2}.
  (d) EXACT signs used inside the induction step, at every positive root xi of F_n':
          F_n''(xi) F_n(xi) < 0          (3.3)
          F_{n+1}'(xi) F_n(xi) > 0       (3.4)
          C_{n+1}(xi) F_n(xi) > 0        (3.5)
          C_{n+1}(xi) F_{n+1}'(xi) > 0   (residue sign)
  (e) endpoint residue C_{n+1}(1)/F_{n+1}'(1) > 0 and the cancellation at zero.
Symbolic: the rational identity behind (3.5) for a generic three-term expansion, and the
residue <-> lambda conversion.
Diagnostic (60-digit floats, not a certificate): the lambda_j themselves and formula (3.5).
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from eul import *  # noqa

N = 46
C = cayley_polys(N + 2)
Z2M1 = fmpq_poly([-1, 0, 1])


def strip_z(p):
    """Remove one factor z if p(0)=0 (returns (quotient, removed?))."""
    co = p.coeffs()
    if co[0] == 0:
        return fmpq_poly(co[1:]), True
    return p, False


def to_t(p):
    """Even polynomial p(z) -> polynomial in t=z^2."""
    co = p.coeffs()
    assert all(co[k] == 0 for k in range(1, len(co), 2))
    return fmpq_poly(co[0::2])


rows = []
for n in range(3, N + 1):
    Fn = Z2M1 * C[n - 2]
    # (a)
    assert Fn.derivative() == C[n - 1]
    assert Fn.degree() == C[n].degree() == n - 1
    rho = C[n].leading_coefficient() / Fn.leading_coefficient()
    assert rho == n * (n - 1) and rho > 0
    num, s1 = strip_z(C[n])
    den, s2 = strip_z(Fn)
    assert s1 == s2 == (n % 2 == 0)              # common simple zero at 0 iff n even
    assert num(Q(0)) != 0 and den(Q(0)) != 0     # ...and it is simple in both
    Nt, Dt = to_t(num), to_t(den)                # ratio is even: both are polys in t
    assert Dt(Q(1)) == 0
    k = Dt.degree()
    assert Nt.degree() == k
    # (b) pattern in t on (0,2): N D N D ... N D   (k pairs), the last D being t=1
    order = merged_root_order({'N': Nt, 'D': Dt}, Q(0), Q(2))
    assert order == ['N', 'D'] * k, (n, order)
    assert count_distinct_real_roots(Dt, Q(0), Q(1, 1) + Q(1, 10 ** 6)) == k   # all poles in (0,1]
    # (c) Corollary 3.2
    f0, _ = strip_z(C[n - 2])
    npos = count_distinct_real_roots(f0, Q(0), Q(1)) if f0.degree() > 0 else 0
    assert npos == (n - 3) // 2
    if npos:
        assert tarski_query(C[n] * C[n - 1], f0, Q(0), Q(1)) == npos
    # (d) signs in the induction step n -> n+1 at positive roots xi of F_n' = C_{n-1}
    d0, _ = strip_z(C[n - 1])
    kpos = count_distinct_real_roots(d0, Q(0), Q(1)) if d0.degree() > 0 else 0
    Fn1 = Z2M1 * C[n - 1]
    if kpos:
        F2 = Fn.derivative().derivative()
        assert tarski_query(F2 * Fn, d0, Q(0), Q(1)) == -kpos
        assert tarski_query(Fn1.derivative() * Fn, d0, Q(0), Q(1)) == kpos
        assert tarski_query(C[n + 1] * Fn, d0, Q(0), Q(1)) == kpos
        assert tarski_query(C[n + 1] * Fn1.derivative(), d0, Q(0), Q(1)) == kpos
    # (3.3) at ALL critical points (both signs of xi), as the proof's formula predicts
    assert tarski_query(Fn.derivative().derivative() * Fn, C[n - 1], Q(-1), Q(1)) == -(n - 2)
    # (e) endpoint
    assert C[n + 1](Q(1)) == 2 * C[n](Q(1)) > 0
    assert Fn1.derivative()(Q(1)) == 2 * Fn.derivative()(Q(1)) > 0
    rows.append({'n': n, 'rho': int(rho.p), 'poles_in_t': k, 'positive_roots_of_C_{n-2}': npos,
                 'pattern_NDND': True, 'cor_3_2_exact': True})

# ---- symbolic identities (sympy)
import sympy as sp

z, rho, l1, l2, l3, a1, a2, a3, xi, r = sp.symbols('z rho l1 l2 l3 a1 a2 a3 xi r')
R = rho + l1 / (z ** 2 - a1) + l2 / (z ** 2 - a2) + l3 / (z ** 2 - a3)
lhs = (z ** 2 - 1) * sp.diff(R, z) + 2 * z * R
rhs = 2 * z * (rho + l1 * (1 - a1) / (z ** 2 - a1) ** 2 + l2 * (1 - a2) / (z ** 2 - a2) ** 2
               + l3 * (1 - a3) / (z ** 2 - a3) ** 2)
assert sp.cancel(lhs - rhs) == 0
# residue r at +xi and -r at -xi combine to 2*xi*r/(z^2-xi^2)
assert sp.cancel(r / (z - xi) - r / (z + xi) - 2 * xi * r / (z ** 2 - xi ** 2)) == 0
# base case
assert sp.cancel((6 * z ** 2 - 2) / (z ** 2 - 1) - (6 + 4 / (z ** 2 - 1))) == 0

# ---- diagnostic: actual lambda_j with 60-digit floats
import mpmath as mp

mp.mp.dps = 60
diag = []
for n in range(3, 41):
    Fn = Z2M1 * C[n - 2]
    num, _ = strip_z(C[n])
    den, _ = strip_z(Fn)
    Nt, Dt = to_t(num), to_t(den)
    dco = [mp.mpf(int(c.p)) / mp.mpf(int(c.q)) for c in Dt.coeffs()]
    nco = [mp.mpf(int(c.p)) / mp.mpf(int(c.q)) for c in Nt.coeffs()]
    roots = mp.polyroots(dco[::-1], maxsteps=2000, extraprec=600) if len(dco) > 2 else [-dco[0] / dco[1]]
    lam = []
    for a in roots:
        assert abs(mp.im(a)) < mp.mpf(10) ** -40
        a = mp.re(a)
        dN = mp.polyval(nco[::-1], a)
        dD = mp.polyval([c * i for i, c in enumerate(dco)][:0:-1], a)
        lam.append(dN / dD)
    assert all(l > 0 for l in lam), n
    diag.append({'n': n, 'min_lambda': mp.nstr(min(lam), 8), 'max_lambda': mp.nstr(max(lam), 8)})

print(json.dumps({'check': '02_residue_lemma', 'status': 'PASS', 'exact_range_n': [3, N],
                  'rows_first': rows[:4], 'rows_last': rows[-2:],
                  'symbolic_identities': ['(3.5) generic 3-term', 'residue pairing', 'base case n=3'],
                  'diagnostic_lambda_range_n': [3, 40], 'diagnostic_sample': diag[:3] + diag[-2:]}, indent=1))
