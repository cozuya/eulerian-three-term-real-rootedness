"""Check 03 - Candidate A, Lemma 4.1:  E(z) = (1-z^2) V(z) - 2 L(z) > 0 on (-1,0).

Symbolic (exact) parts:
  * contribution of a root at 0 and of a pair +-sqrt(a), derived here from scratch
  * N(u,a) = a(1-u)^3(1+u) + (1-a)u^2(1+2u-u^2)
  * E f^2 = (1-z^2)(f'^2 - f f'') - 2 f f'   (the bracket used in the central identity)
Exact stress tests:
  * random symmetric rational root sets, random rational z in (-1,0): E>0 every time
  * Eulerian f=C_m: the polynomial numerator  Br = (1-z^2)(f'^2-ff'')-2ff'  is > 0 on
    (-1,0) -- certified by Sturm: Br has no root in (-1,0) and is positive at one point
Sharpness / non-extension (the audit brief asks not to extend to z>0 without proof):
  * f=z: E(1/2) = -1 < 0
  * Eulerian f=C_m: Br has exactly one root in (0,1) and is negative beyond it, for every
    m tested  -> the positive half-interval genuinely needs a different argument.
"""
import json
import random
import sys
from fractions import Fraction
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parent))
from eul import *  # noqa

z, u, a, s = sp.symbols('z u a s')

# --- pair +-s, a = s^2
pair = (1 - z ** 2) * (1 / (z - s) ** 2 + 1 / (z + s) ** 2) - 2 * (1 / (z - s) + 1 / (z + s))
Nua = u ** 2 * (1 + 2 * u - u ** 2) + a * (1 - 2 * u - u ** 2)
assert sp.cancel(pair.subs(z, -u) - (2 * Nua / (u ** 2 - a) ** 2).subs(a, s ** 2)) == 0
assert sp.expand(Nua - (a * (1 - u) ** 3 * (1 + u) + (1 - a) * u ** 2 * (1 + 2 * u - u ** 2))) == 0
# --- root at zero
zero = (1 - z ** 2) / z ** 2 - 2 / z
assert sp.cancel(zero.subs(z, -u) - (1 + 2 * u - u ** 2) / u ** 2) == 0
# 1+2u-u^2 = 2-(1-u)^2 > 0 on (0,1)
assert sp.expand(1 + 2 * u - u ** 2 - (2 - (1 - u) ** 2)) == 0
# --- bracket = f^2 E for a generic function
f = sp.Function('f')(z)
L = sp.diff(f, z) / f
V = -sp.diff(L, z)
assert sp.simplify(f ** 2 * ((1 - z ** 2) * V - 2 * L)
                   - ((1 - z ** 2) * (sp.diff(f, z) ** 2 - f * sp.diff(f, z, 2)) - 2 * f * sp.diff(f, z))) == 0

# --- exact random stress test
random.seed(20261114)
trials = 0
minE = None
for _ in range(4000):
    k = random.randint(0, 6)
    roots = []
    for _ in range(k):
        r = Fraction(random.randint(1, 999), 1000)
        roots += [r, -r]
    if random.random() < 0.5 or not roots:
        roots.append(Fraction(0))
    zz = -Fraction(random.randint(1, 9999), 10000)
    if zz in roots:
        continue
    E = (1 - zz ** 2) * sum(1 / (zz - r) ** 2 for r in roots) - 2 * sum(1 / (zz - r) for r in roots)
    assert E > 0
    minE = E if minE is None else min(minE, E)
    trials += 1

# --- Eulerian f: bracket polynomial on (-1,0) and on (0,1)
M = 40
C = cayley_polys(M + 1)
W = fmpq_poly([1, 0, -1])     # 1 - z^2
eul_rows = []
for m in range(2, M + 1):
    fm = C[m]
    d1, d2 = fm.derivative(), fm.derivative().derivative()
    Br = W * (d1 * d1 - fm * d2) - 2 * fm * d1
    # (-1,0): no root, and positive.  Br(-1) = 2 f(-1) f'(-1)... just test endpoints are not roots.
    assert Br(Q(-1)) != 0
    # Br(0) may vanish (f odd or even gives f(0)f'(0)=0 and then Br(0)=f'(0)^2 - f(0)f''(0) > 0)
    assert Br(Q(0)) > 0
    assert real_root_multiset_count(Br, Q(-1), Q(0)) == 0
    assert Br(Q(-1, 2)) > 0
    npos = count_distinct_real_roots(Br, Q(0), Q(1)) if Br(Q(1)) != 0 else None
    eul_rows.append({'m': m, 'Br_roots_in_(-1,0)': 0, 'Br_distinct_roots_in_(0,1)': npos,
                     'sign_Br(1)': sgn(Br(Q(1)))})
    assert npos == 1 and sgn(Br(Q(1))) < 0          # exactly one sign change on (0,1): + then -

# --- explicit failure on the positive side for the simplest admissible f
Ehalf = (1 - Fraction(1, 4)) * 4 - 2 * 2
assert Ehalf == -1

print(json.dumps({'check': '03_logderiv_lemma', 'status': 'PASS',
                  'symbolic': ['pair formula', 'N(u,a) decomposition', 'root at zero', 'bracket = f^2 E'],
                  'random_exact_trials': trials, 'min_E_seen': float(minE),
                  'eulerian_bracket_positive_on_(-1,0)_for_m': [2, M],
                  'eulerian_bracket_exactly_one_root_in_(0,1)_then_negative_for_m': [2, M],
                  'sample': eul_rows[:3] + eul_rows[-2:],
                  'positive_side_counterexample': 'f=z, z=1/2: E=-1'}, indent=1))
