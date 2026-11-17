"""Exact symbolic checks of the independently reviewed Sturm-route formulas.

Run: python research/sturm/verify_sturm_identities.py
This verifies algebraic identities and an auxiliary counterexample. It does
not replace the analytical proof of the all-degree inequality.
"""
import json
import platform
import sympy as s

x, m, alpha, b = s.symbols("x m alpha b")
z = -alpha - 1 - m*x
B = (-alpha**2 + alpha*x - m*x*(1-x) - (1-2*x)*z
     + z**2/(m-1) + b*alpha)
B1 = (x*x + alpha*x - alpha**2 + alpha*(b+1) + 1
      + (x+alpha+1)**2/(m-1))
B2 = (m/(m-1)*(x+(alpha*(m+1)+2)/(2*m))**2
      + 1 + alpha*(b+1) - s.Rational(5,4)*alpha**2
      + (alpha+2)**2/(4*m))
assert s.cancel(B-B1) == 0
assert s.cancel(B-B2) == 0

t, a = s.symbols("t a")
pair = ((a+1)*(t*t+2*t-a)/(a-t)**2
        +(1/a+1)*(t*t+2*t-1/a)/(1/a-t)**2)
pair_formula = ((a+1)**2*(a*(t-1)**2*(t*t+2*t-1)
                              +2*t*(a-1)**2)
                /((a-t)**2*(a*t-1)**2))
assert s.cancel(pair-pair_formula) == 0

# One-root summands verify the final strict rational identity for arbitrary
# root lists; the remaining constant contribution is -x.
R_summand = x*(1+a)/(x+a)
J_summand = (1-x)*s.diff(R_summand,x)+R_summand
assert s.cancel(J_summand-(1+a)*(a+x*x)/(x+a)**2) == 0
assert s.cancel(-x*J_summand+R_summand
                -x*x*(1-x)*(1+a)/(x+a)**2) == 0

h = x*x+s.Rational(21,10)*x+1
R = 1+3*x+x*(1-x)*s.diff(h,x)/h
E = -x*(1-x)*s.diff(R,x)+(2-x)*R-2
r = s.Rational(-3,10)
obstruction_alpha = s.cancel(-R.subs(x,r))
obstruction_E = s.cancel(E.subs(x,r))
assert obstruction_alpha == s.Rational(539,460)
assert obstruction_E == s.Rational(-113037,211600)

k = s.sqrt(2)-1
b0 = 5*k-1
H1 = 1+(b+1)**2/5
H2 = 1+k*k+(b+1-k)**2/4
assert s.simplify((H1-H2).subs(b,b0)) == 0
assert s.simplify(s.diff(H1-H2,b).subs(b,b0)) == 0

print(json.dumps({
    "python": platform.python_version(),
    "sympy": s.__version__,
    "cauchy_bound_identity": "PASS",
    "completed_square_identity": "PASS",
    "reciprocal_pair_identity": "PASS",
    "final_strict_rational_identity": "PASS",
    "piecewise_value_and_derivative_match": "PASS",
    "auxiliary_generic_obstruction": {
        "h": str(h), "r": str(r),
        "alpha": str(obstruction_alpha), "E": str(obstruction_E),
        "is_Eulerian_counterexample": False
    }
}, indent=2))
