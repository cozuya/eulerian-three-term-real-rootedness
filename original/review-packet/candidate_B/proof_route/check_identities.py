#!/usr/bin/env python3
"""Exact symbolic verification of the identities in partial_theorem.md."""
import json, platform
from pathlib import Path
import sympy as s
x,b,c,d=s.symbols('x b c d')
q=x*(1-x)
A=[s.Integer(1),s.Integer(1)]
for k in range(1,13):
    A.append(s.expand((1+k*x)*A[k]+q*s.diff(A[k],x)))
checks=[]
for m in range(1,11):
    F,G,H=A[m:m+3]
    # Avoid a rational simplification across unknown roots: verify numerators.
    W=s.expand(s.diff(G,x)*F-G*s.diff(F,x))
    assert s.expand(H*F-G*G-x*G*F-q*W)==0
    R=G/F
    assert s.cancel(R.subs(x,1/x)-R/x)==0
    assert s.cancel(s.diff(R,x).subs(x,1/x)-R+x*s.diff(R,x))==0
    # Pointwise identity modulo Q=G+dF, obtained by substituting R=-d.
    P=H+b*G+c*F
    reciprocal_deriv=s.cancel(s.diff(R,x).subs(x,1/x))
    identity=s.cancel(P/F-(d*d-(b+1)*d+c-(1-x)*reciprocal_deriv))
    numerator=s.Poly(s.together(identity).as_numer_denom()[0],x)
    rem=s.rem(numerator,s.Poly(G+d*F,x))
    assert s.simplify(rem.as_expr())==0
    checks.append({'m':m,'quotient_identity':True,'reciprocity':True,'derivative_reciprocity':True,'root_identity_mod_Q':True})
# Exact repeated-root-aware root count on a small adversarial independent set.
root_checks=[]
for n in range(3,13):
    for bv in [s.Rational(0),s.Rational(1,3),s.Rational(2),s.Rational(100)]:
        cv=1+(bv+1)**2/4
        p=s.Poly(A[n]+bv*A[n-1]+cv*A[n-2],x)
        factors=s.sqf_list(p)[1]
        total=sum(mult*factor.count_roots(-s.oo,s.oo) for factor,mult in factors)
        assert total==n-1
        assert s.gcd(p,p.diff()).degree()==0
        root_checks.append({'n':n,'b':str(bv),'c':str(cv),'real_roots_with_multiplicity':int(total),'degree':n-1,'square_free':True})
result={'python':platform.python_version(),'sympy':s.__version__,'symbolic_checks':checks,'exact_root_checks':root_checks}
path=Path(__file__).with_name('identity_check_output.json')
path.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'symbolic_indices':len(checks),'exact_root_checks':len(root_checks),'all_passed':True,'output':str(path),'python':platform.python_version(),'sympy':s.__version__}))
