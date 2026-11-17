"""Check 00 - self-test of the audit toolkit (eul.py) against independent references.

My Sturm counts, multiplicity-aware counts, Sturm-Tarski queries and merged root orders are
compared with (i) polynomials built from known rational roots, where every answer is known
by construction, and (ii) sympy's own exact root counter on random integer polynomials.
"""
import json
import random
import sys
from fractions import Fraction
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parent))
from eul import *  # noqa

random.seed(12345)
xs = sp.symbols('x')
n_known = n_sympy = n_tarski = n_order = 0

# (i) known rational roots, with multiplicities and extra complex pairs
for _ in range(300):
    roots = sorted({Fraction(random.randint(-40, 40), random.randint(1, 9)) for _ in range(random.randint(1, 6))})
    mult = [random.randint(1, 3) for _ in roots]
    p = fmpq_poly([random.choice([1, 2, 3])])
    for r, mu in zip(roots, mult):
        p *= fmpq_poly([-Q(r), 1]) ** mu
    for _ in range(random.randint(0, 2)):                   # irreducible quadratics: no real roots
        s, t = random.randint(-5, 5), random.randint(1, 6)
        p *= fmpq_poly([s * s + t, -2 * s, 1])
    assert count_distinct_real_roots(p) == len(roots)
    assert real_root_multiset_count(p) == sum(mult)
    a, b = Fraction(-7, 2) + Fraction(1, 1000), Fraction(11, 3) + Fraction(1, 997)
    if all(r != a and r != b for r in roots):
        inside = [(r, mu) for r, mu in zip(roots, mult) if a < r < b]
        assert count_distinct_real_roots(p, Q(a), Q(b)) == len(inside)
        assert real_root_multiset_count(p, Q(a), Q(b)) == sum(mu for _, mu in inside)
        # Tarski query against direct evaluation at the known roots
        g = fmpq_poly([random.randint(-9, 9) for _ in range(random.randint(1, 5))])
        if not g.is_zero():
            expect = sum(sgn(g(Q(r))) for r, _ in inside)
            assert tarski_query(g, p, Q(a), Q(b)) == expect
            n_tarski += 1
    n_known += 1

# (ii) random integer polynomials versus sympy
for _ in range(200):
    deg = random.randint(1, 9)
    co = [random.randint(-12, 12) for _ in range(deg)] + [random.choice([-3, -1, 1, 2])]
    p = fmpq_poly(co)
    sp_p = sp.Poly(sum(c * xs ** i for i, c in enumerate(co)), xs)
    sqf = sp_p.sqf_list()[1]
    assert count_distinct_real_roots(p) == sum(fac.count_roots() for fac, _ in sqf)
    assert real_root_multiset_count(p) == sum(mu * fac.count_roots() for fac, mu in sqf)
    n_sympy += 1

# (iii) merged root order with known roots
for _ in range(100):
    pool = random.sample(range(-60, 60), 9)
    A_, B_, C_ = pool[:3], pool[3:6], pool[6:]
    mk = lambda rs: eval('*'.join(['fmpq_poly([%d,7])' % (-r) for r in rs]))   # roots r/7
    order = merged_root_order({'A': mk(A_), 'B': mk(B_), 'C': mk(C_)}, Q(-100), Q(100))
    truth = [lab for _, lab in sorted([(r, 'A') for r in A_] + [(r, 'B') for r in B_] + [(r, 'C') for r in C_])]
    assert order == truth
    n_order += 1

print(json.dumps({'check': '00_selftest', 'status': 'PASS', 'known_root_cases': n_known,
                  'tarski_cases': n_tarski, 'sympy_comparisons': n_sympy, 'merged_order_cases': n_order}, indent=1))
