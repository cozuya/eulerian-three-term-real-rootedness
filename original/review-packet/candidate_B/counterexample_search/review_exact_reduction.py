#!/usr/bin/env python3
"""Independently recheck finite-degree reduction certificates via integer recurrence and Sturm signs."""
from pathlib import Path
import json,sympy as s
OUT=Path(__file__).resolve().parent
SOURCE=OUT.parent/'eulerian_attempt'/'exact_reduction_checks.json'
data=json.loads(SOURCE.read_text());x=s.symbols('x')
# Independent integer coefficient construction (constant coefficient first),
# not polynomial differentiation.
rows=[[1],[1]]
for n in range(1,17):
 a=rows[n];rows.append([(k+1)*(a[k] if k<len(a) else 0)+(n-k+1)*(a[k-1] if k>0 else 0) for k in range(n+1)])
def poly(cs):return s.Poly.from_list(list(reversed(cs)),x,domain=s.QQ)
def variations(signs):
 ss=[v for v in signs if v]
 return sum(a!=b for a,b in zip(ss,ss[1:]))
def chain(p):return [s.Poly(e,x,domain=s.QQ) for e in s.sturm(p.as_expr(),x)]
def v(st,z):
 if z==-s.oo:signs=[int(s.sign(q.LC()))*((-1)**q.degree()) for q in st]
 else:signs=[int(s.sign(q.eval(z))) for q in st]
 return variations(signs),signs
checked=[]
for row in data['finite_degree_certificates']:
 m=row['m'];F,G,H=[poly(rows[k]) for k in [m,m+1,m+2]]
 N=G*G-F*H+2*F*G-2*F*F
 assert [str(z) for z in N.all_coeffs()]==row['N_coefficients_highest_first']
 assert N.degree()==2*m-1 and N.LC()<0 and N.eval(0)==0
 E=N.exquo(s.Poly(x,x));assert E.eval(0)!=0
 se=chain(E);vn,sn=v(se,-s.oo);vz,sz=v(se,s.Rational(0));assert vn-vz==1
 al,au=[s.Rational(z) for z in row['N_negative_root_interval']]
 bl,bu=[s.Rational(z) for z in row['Q1_largest_root_interval']]
 assert bl<bu<al<au<0
 assert E.eval(al)!=0 and E.eval(au)!=0
 va,_=v(se,al);vb,_=v(se,au);assert va-vb==1
 Q=G+F;sq=chain(Q)
 vl,_=v(sq,bl);vu,_=v(sq,bu);v0,_=v(sq,s.Rational(0));assert vl-vu==1 and vu-v0==0
 assert Q.eval(bl)!=0 and Q.eval(bu)!=0
 assert N.eval(bl)>0 and N.eval(bu)>0
 checked.append({'m':m,'n':m+2,'coefficient_reconstruction_passed':True,'N_over_x_sturm_signs_minus_infinity':sn,'N_over_x_sturm_signs_at_zero':sz,'N_over_x_negative_root_count':vn-vz,'N_over_x_variations_minus_infinity':vn,'N_over_x_variations_at_zero':vz,'alpha_interval_count':va-vb,'beta_interval_count':vl-vu,'Q_roots_between_beta_interval_and_zero':vu-v0,'N_positive_on_beta_interval_endpoints':True,'interval_order_verified':True})
 print('independently verified reduction n',m+2,flush=True)
result={'scope':'Finite degrees n4 through17 only; n3 separately elementary. Does not prove all-degree conjecture.','method':'Independent integer Eulerian coefficient recurrence, then direct exact Sturm sign-variation counts on stored certificate polynomials and intervals.','checks_completed':len(checked),'all_passed':True,'results':checked}
(OUT/'exact_reduction_review_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',len(checked),'finite-degree certificate audits',flush=True)
