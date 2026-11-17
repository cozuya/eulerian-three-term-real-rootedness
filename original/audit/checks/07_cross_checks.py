"""Check 07 - does Candidate A 'prove too much'?  And are A and B compatible?  All exact.

A valid proof must break when its conclusion is false.  B's obstruction shows the conclusion
is false for a non-Eulerian reciprocal triple.  Sections 4-6 of A never use the Eulerian
sequence (only simple symmetric roots in (-1,1) and endpoint signs), so for a non-Eulerian
triple WITH simple roots whose combination is not real-rooted, the Eulerian-specific input
(Lemma 3.1 / Corollary 3.2) must be the step that fails.  This script checks exactly that.

Part A  B's obstruction in Cayley coordinates: seed (2z)^10, f = 2^10 z^9 (12 z^2 - 10).
        A's hypotheses fail at the first step: f does not have simple roots.
Part B  simple-root perturbations of that seed: c0 = prod (z^2 - eps_i^2).
          - conclusion still false (P not real-rooted)               [so A must break]
          - A's generic steps hold: q structure, (5.5) on the negative half
          - A's Eulerian step fails: h g < 0 at some positive root of f   (Cor. 3.2 analogue)
          - Lemma 3.1's base fails: a negative residue for c2/((z^2-1) c0)
          - Lemma 3.1's induction STEP is generic: whenever all residues at one level are
            positive, they are positive at the next (checked on Eulerian and random seeds)
Part C  region inclusion and the role of each candidate's test points on Eulerian data:
          on the right half, at B's test points (positive roots of q) the sign information
          comes from N_m >= 0, an inequality B could not prove in general;
          A instead uses the positive roots of f, where only Cor. 3.2 is needed.
"""
import json
import random
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from eul import *  # noqa

ZP = fmpq_poly([1, 1])
Z2M1 = fmpq_poly([-1, 0, 1])


def strip_z(p):
    co = p.coeffs()
    k = 0
    while co[k] == 0:
        k += 1
    return fmpq_poly(co[k:]), k


def analyse(c0, b, c):
    """c0 plays the role of C_{m-1}; f=T c0, g=T f, h=T g; returns exact diagnostics."""
    f, g = T(c0), None
    g = T(f)
    h = T(g)
    m = f.degree() + 1
    al = Fraction(b) / 2 + 1
    P = h + Q(b) * ZP * g + Q(c) * ZP * ZP * f
    q = g + Q(al) * ZP * f
    out = {'m': m, 'deg_P': P.degree()}
    out['f_simple_roots'] = is_squarefree(f)
    out['P_real_roots_with_multiplicity'] = real_root_multiset_count(P)
    out['P_real_rooted'] = out['P_real_roots_with_multiplicity'] == P.degree()
    if not out['f_simple_roots']:
        return out
    p = (m - 1) // 2
    fpos, _ = strip_z(f)
    out['f_roots_in_(-1,1)'] = count_distinct_real_roots(f, Q(-1), Q(1))
    out['q_roots_in_(-1,1)'] = count_distinct_real_roots(q, Q(-1), Q(1))
    out['q_negative_roots'] = count_distinct_real_roots(q, Q(-1), Q(0))
    out['generic_step_5_5_holds'] = tarski_query(P * f, q, Q(-1), Q(0)) == -out['q_negative_roots']
    out['positive_f_roots'] = p
    out['cor32_sum_sign_hg'] = tarski_query(h * g, fpos, Q(0), Q(1))
    out['cor32_holds'] = out['cor32_sum_sign_hg'] == p
    out['step_5_6_sum_sign_Pg'] = tarski_query(P * g, fpos, Q(0), Q(1))
    # Lemma 3.1 at the level below:  residues of g / ((z^2-1) c0) at positive roots of c0 are g/f
    c0pos, _ = strip_z(c0)
    k0 = count_distinct_real_roots(c0pos, Q(0), Q(1)) if c0pos.degree() > 0 else 0
    out['level_below_positive_poles'] = k0
    out['level_below_residue_sign_sum'] = tarski_query(g * f, c0pos, Q(0), Q(1)) if k0 else 0
    return out


res = {}

# ---------------- Part A: the obstruction itself
c0 = fmpq_poly([0] * 10 + [1024])                      # (2z)^10  <->  (x+1)^10
f = T(c0)
assert f == fmpq_poly([0] * 9 + [1]) * fmpq_poly([-10, 0, 12]) * 1024
A_out = analyse(c0, 4, 11)
assert A_out['f_simple_roots'] is False and A_out['P_real_roots_with_multiplicity'] == 11 and A_out['deg_P'] == 13
res['obstruction_in_cayley_form'] = A_out

# ---------------- Part B: simple-root perturbations
pert = []
for scale in (50, 20, 10):
    c0 = fmpq_poly([1])
    for i in range(1, 6):
        e = Q(i, scale)
        c0 *= fmpq_poly([-e * e, 0, 1])
    o = analyse(c0, 4, 11)
    o['eps_scale'] = f'i/{scale}, i=1..5'
    assert o['f_simple_roots'] and o['f_roots_in_(-1,1)'] == 11 and o['q_roots_in_(-1,1)'] == 12
    assert o['generic_step_5_5_holds']                   # A's generic machinery is fine here
    if not o['P_real_rooted']:
        assert not o['cor32_holds']                      # ...so the Eulerian-specific step must fail
        assert o['level_below_residue_sign_sum'] < o['level_below_positive_poles']
    pert.append(o)
assert not pert[0]['P_real_rooted']
res['simple_root_perturbations'] = pert

# the logical contrapositive, checked on many symmetric seeds, half of them CLUSTERED near 0
# (the regime of B's obstruction, where non-real-rooted combinations actually occur):
#   generic steps + Cor.3.2 analogue  ==>  real-rooted
# so no seed may have the Cor.3.2 analogue true while P fails to be real-rooted.
random.seed(99)
tested = violations = cor_true = notreal = 0
for trial in range(600):
    clustered = trial % 2 == 0
    k = random.randint(3, 6) if clustered else random.randint(1, 5)
    c0 = fmpq_poly([1])
    used = set()
    for _ in range(k):
        e = Fraction(random.randint(1, 60), 1000) if clustered else Fraction(random.randint(1, 95), 100)
        if e in used:
            continue
        used.add(e)
        c0 *= fmpq_poly([-Q(e * e), 0, 1])
    if random.random() < 0.5:
        c0 *= fmpq_poly([0, 1])
    b = Fraction(random.randint(0, 80), 10)
    al = b / 2 + 1
    frac = Fraction(1) if clustered else Fraction(random.randint(0, 100), 100)
    cc = (al * al + 2) * frac
    if c0.degree() % 2 == 0 and b == 0:      # f odd and b = 0: Case III, skip (needs the limit)
        continue
    o = analyse(c0, b, cc)
    assert o['f_simple_roots'] and o['generic_step_5_5_holds']
    tested += 1
    cor_true += o['cor32_holds']
    notreal += (not o['P_real_rooted'])
    if o['cor32_holds'] and not o['P_real_rooted']:
        violations += 1
assert violations == 0 and notreal > 0
res['random_non_eulerian_seeds'] = {'tested': tested, 'cor32_analogue_true': cor_true,
                                    'P_not_real_rooted': notreal,
                                    'cor32_true_but_not_real_rooted': violations}

# Lemma 3.1 induction step is generic: positivity at one level => positivity at the next
checked = holds_next = 0
random.seed(5)
for _ in range(300):
    k = random.randint(1, 4)
    c0 = fmpq_poly([1])
    used = set()
    for _ in range(k):
        e = Fraction(random.randint(1, 95), 100)
        if e in used:
            continue
        used.add(e)
        c0 *= fmpq_poly([-Q(e * e), 0, 1])
    if random.random() < 0.5:
        c0 *= fmpq_poly([0, 1])
    c1 = T(c0); c2 = T(c1); c3 = T(c2)
    c0pos, _ = strip_z(c0)
    c1pos, _ = strip_z(c1)
    k0 = count_distinct_real_roots(c0pos, Q(0), Q(1)) if c0pos.degree() > 0 else 0
    k1 = count_distinct_real_roots(c1pos, Q(0), Q(1)) if c1pos.degree() > 0 else 0
    level0 = (tarski_query(c2 * c1, c0pos, Q(0), Q(1)) == k0) if k0 else True
    level1 = (tarski_query(c3 * c2, c1pos, Q(0), Q(1)) == k1) if k1 else True
    if level0:
        checked += 1
        holds_next += level1
        assert level1, 'induction step failed on a non-Eulerian seed'
res['lemma_3_1_step_is_generic'] = {'seeds_with_positive_residues': checked, 'next_level_positive': holds_next}

# ---------------- Part C: Eulerian data, regions and test points
bsym_ok = all((Fraction(b) ** 2 / 4 + Fraction(b) + 3) - (1 + (Fraction(b) + 1) ** 2 / 4) == Fraction(b) / 2 + Fraction(7, 4)
              for b in (0, Fraction(1, 3), 5, 10 ** 6))
assert bsym_ok
C = cayley_polys(42)
W = fmpq_poly([1, 0, -1])
rows = []
for m in range(2, 41):
    f, g, h = C[m], C[m + 1], C[m + 2]
    d1, d2 = f.derivative(), f.derivative().derivative()
    Br = W * (d1 * d1 - f * d2) - 2 * f * d1                  # = f^2 E ;  (1+z)^{2m} N_m = (1-z^2) Br
    p = (m - 1) // 2
    q1 = g + ZP * f                                           # alpha = 1 (b = 0): the extreme separator
    npos_q = count_distinct_real_roots(q1, Q(0), Q(1))
    # B's route: needs Br >= 0 at the positive roots of q (all alpha >= 1); true here for alpha=1:
    b_route = tarski_query(Br, q1, Q(0), Q(1)) == npos_q
    # A's route: Cor 3.2 at positive roots of f
    fpos, _ = strip_z(f)
    a_route = (tarski_query(h * g, fpos, Q(0), Q(1)) == p) if p else True
    assert a_route
    rows.append({'m': m, 'B_needs_Br>=0_at_positive_q_roots(alpha=1)': b_route, 'A_needs_cor32': a_route})
res['eulerian_test_points_m_2_40'] = {'B_route_inequality_holds_all': all(r['B_needs_Br>=0_at_positive_q_roots(alpha=1)'] for r in rows),
                                      'A_route_cor32_holds_all': True}

print(json.dumps({'check': '07_cross_checks', 'status': 'PASS', **res}, indent=1))
