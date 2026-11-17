#!/usr/bin/env python3
"""Exact checks of the full-bound reduction for finitely many degrees.

These are finite-degree certificates for all real coefficient parameters,
not a proof of the original all-degree conjecture.
"""
import itertools
import json
import platform
from pathlib import Path
import sympy as s

OUT = Path(__file__).resolve().parent
x,b,c,t,a=s.symbols('x b c t a')
A=[s.Poly(1,x,domain=s.QQ),s.Poly(1,x,domain=s.QQ)]
for k in range(1,18):
    A.append(s.Poly((1+k*x)*A[k].as_expr()+x*(1-x)*A[k].diff().as_expr(),x,domain=s.QQ))

# Independent descent enumeration confirms the convention and recurrence.
enumeration=[]
for n in range(1,8):
    coeff=[0]*n
    for p in itertools.permutations(range(n)):
        coeff[sum(p[i]>p[i+1] for i in range(n-1))]+=1
    assert coeff==list(reversed(A[n].all_coeffs()))
    enumeration.append({'n':n,'coefficients_constant_first':coeff,'passed':True})

# A fully symbolic proof for n=4 over the entire proposed parameter region.
bound=b*b/4+b+3
D=s.discriminant(A[4].as_expr()+b*A[3].as_expr()+c*A[2].as_expr(),x)
positive=s.Poly(s.cancel((1+t)**3*D.subs(c,bound*t/(1+t))),b,t)
assert all(co>0 for co in positive.coeffs())
boundary=s.factor(D.subs(c,bound))
assert s.expand(boundary-(b+1)*(b**4+40*b**3+616*b*b+4064*b+8400)/4)==0

# Exact algebra for the reciprocal-pair part of the unproved all-degree lemma.
term=lambda z:t*(z+1)*(t*t+2*t-z)/(z-t)**2
pair=t*(a+1)**2*a*(t**4-4*t*t+2*(a+1/a)*t-1)/((a-t)**2*(a*t-1)**2)
assert s.factor(term(a)+term(1/a)-pair)==0
assert s.expand(t**4-4*t*t+4*t-1-(t-1)**2*(t*t+2*t-1))==0

# For each fixed m certify N_m has exactly one negative root alpha, and
# the largest root beta of Q_1=A_(m+1)+A_m lies strictly to its left.
# N_m is positive on (-infinity,alpha), whereas R>-1 to the right of beta.
# Hence the strengthened inequality holds wherever R<=-1, for these m.
certificates=[]
for m in range(2,16):
    F,G,H=A[m:m+3]
    N=G*G-F*H+2*F*G-2*F*F
    p=s.Poly(x*(1-x),x)
    N2=-p*(G.diff()*F-G*F.diff())+s.Poly(2-x,x)*F*G-2*F*F
    assert N==N2
    assert N.degree()==2*m-1 and N.LC()<0
    assert s.gcd(N,N.diff()).degree()==0
    assert N.count_roots(-s.oo,0)==2  # includes the endpoint zero
    nonzero=N.exquo(s.Poly(x,x))
    assert nonzero.count_roots(-s.oo,0)==1
    intervals=N.intervals(eps=s.Rational(1,10**15))
    neg=[(iv,mult) for iv,mult in intervals if iv[1]<0]
    assert len(neg)==1 and neg[0][1]==1
    alpha=neg[0][0]
    Q=G+F
    qiv=Q.intervals(eps=s.Rational(1,10**15))
    assert len(qiv)==m and all(mult==1 and iv[1]<0 for iv,mult in qiv)
    beta=qiv[-1][0]
    assert beta[1]<alpha[0]
    row={'m':m,'n':m+2,'N_coefficients_highest_first':[str(z) for z in N.all_coeffs()],
         'N_degree':N.degree(),'N_square_free':True,'N_strictly_negative_roots':1,
         'N_negative_root_interval':[str(z) for z in alpha],
         'Q1_largest_root_interval':[str(z) for z in beta],
         'intervals_strictly_ordered':True,'full_bound_reduction_certified':True}
    certificates.append(row)
    print('certified full-bound reduction for n',m+2,flush=True)

out={'python':platform.python_version(),'sympy':s.__version__,
     'permutation_enumeration':enumeration,
     'n4_discriminant':str(D),'n4_positive_substitution':str(positive.as_expr()),
     'n4_substitution':'c=(b**2/4+b+3)*t/(1+t), b,t>=0; equality handled separately',
     'n4_boundary_discriminant':str(boundary),
     'reciprocal_pair_identity_verified':True,
     'full_bound_all_real_parameter_degrees':[3]+[r['n'] for r in certificates],
     'finite_degree_certificates':certificates,
     'scope':'Finite degrees only; m=1 (n=3) is the elementary discriminant case.'}
(OUT/'exact_reduction_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(certificates),'finite-degree certificates; not an all-degree proof',flush=True)
