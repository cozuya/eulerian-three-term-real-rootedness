import sympy as s,json,sys
z=s.symbols('z');a=s.Rational(3,20);f=z*z-a
T=lambda p:s.expand((z*z-1)*s.diff(p,z)+2*z*p)
g=T(f);h=T(g);F=(z*z-1)*f
pf=20+4/(z*z-1)+s.Rational(1,10)/(z*z-a)
assert s.cancel(h/F-pf)==0
Q=s.Poly(20*(g+(z+1)*f),z)
N=s.Poly(10*((1-z*z)*(s.diff(f,z)**2-f*s.diff(f,z,2))-2*f*s.diff(f,z)),z)
l,u=s.Rational(6395,10000),s.Rational(6396,10000)
assert Q.eval(l)<0<Q.eval(u)
assert Q.count_roots(l,u)==1
assert N.eval(l)<0 and N.count_roots(l,u)==0
assert f.subs(z,l)>0
P=s.Poly(h+3*(z+1)**2*f,z)
assert P.count_roots(-s.oo,s.oo)==4
out={'python':sys.version,'sympy':s.__version__,'C':str(f),'T2C_over_F':str(pf),'Q_integer':str(Q.as_expr()),'E_numerator_integer':str(N.as_expr()),'isolating_interval':[str(l),str(u)],'Q_left':str(Q.eval(l)),'Q_right':str(Q.eval(u)),'Q_root_count':int(Q.count_roots(l,u)),'E_numerator_left':str(N.eval(l)),'E_numerator_roots_in_interval':int(N.count_roots(l,u)),'original_analogue_real_root_count':int(P.count_roots(-s.oo,s.oo)),'conclusion':'Positive square-variable residues do not imply the proposed H>=0 auxiliary inequality at every Q_alpha root, even alpha=1. This is not a counterexample to the Eulerian target.'}
print(json.dumps(out,indent=2))
