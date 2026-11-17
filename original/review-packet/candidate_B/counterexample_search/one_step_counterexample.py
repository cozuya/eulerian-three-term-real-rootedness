#!/usr/bin/env python3
"""Exact certificate against the generic one-step extension, NOT against Eulerian conjecture."""
import sympy as s,json
from pathlib import Path
x=s.symbols('x');q=x*(1-x);OUT=Path(__file__).parent
f=(x+1)**10;F=s.expand((1+11*x)*f+q*s.diff(f,x));G=s.expand((1+12*x)*F+q*s.diff(F,x));H=s.expand((1+13*x)*G+q*s.diff(G,x));P=s.Poly(H+4*G+11*F,x)
expected=s.Poly(x**6+158*x**5+3206*x**4+13796*x**3+5657*x**2+686*x+16,x)
assert s.expand(P.as_expr()-(x+1)**7*expected.as_expr())==0
sturm=[]
for e in s.sturm(expected.as_expr(),x):
 p=s.Poly(e,x,domain=s.QQ).clear_denoms()[1].primitive()[1]
 sign=int(s.sign(p.LC()));sturm.append({'degree':p.degree(),'primitive_polynomial':str(p.as_expr()),'minus_infinity_sign':sign*(-1)**p.degree(),'plus_infinity_sign':sign})
def variations(signs):return sum(a!=b for a,b in zip(signs,signs[1:]))
vminus=variations([z['minus_infinity_sign'] for z in sturm]);vplus=variations([z['plus_infinity_sign'] for z in sturm]);count=vminus-vplus
out={'scope':'Falsifies proposed extension to one recurrence applied to arbitrary reciprocal negative-rooted input. Does NOT falsify original Eulerian conjecture.','seed_polynomial':str(f),'b':'4','c':'11','F':str(s.factor(F)),'G':str(s.factor(G)),'H':str(s.factor(H)),'P_factorization':str(s.factor(P.as_expr())),'sextic_square_free':s.gcd(expected,expected.diff()).degree()==0,'sturm_chain':sturm,'variations_minus_infinity':vminus,'variations_plus_infinity':vplus,'sextic_real_roots':count,'P_degree':P.degree(),'P_real_roots_with_multiplicity':count+7,'counterexample_certified':count==4}
(OUT/'one_step_counterexample.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
