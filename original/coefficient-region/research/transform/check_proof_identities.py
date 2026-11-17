import sympy as s,json,sys,platform
z,alpha,c,F,F1,F2=s.symbols('z alpha c F F1 F2')
b=2*alpha-2
G=(z*z-1)*F1+2*z*F
H=(z*z-1)**2*F2+6*z*(z*z-1)*F1+(6*z*z-2)*F
Q=G+alpha*(z+1)*F
P=H+b*(z+1)*G+c*(z+1)**2*F
rhs=Q*Q+(z+1)**2*(c-alpha*alpha-2)*F*F-(1-z*z)*((1-z*z)*(F1*F1-F*F2)-2*F*F1)
assert s.expand(P*F-rhs)==0
u,a=s.symbols('u a')
N=u*u*(1+2*u-u*u)+a*(1-2*u-u*u)
Npos=a*(1-u)**3*(1+u)+(1-a)*u*u*(1+2*u-u*u)
assert s.expand(N-Npos)==0
r=s.symbols('r')
Epair=(1-z*z)*(1/(z-r)**2+1/(z+r)**2)-2*(1/(z-r)+1/(z+r))
assert s.cancel(Epair.subs(z,-u)-2*N.subs(a,r*r)/(u*u-r*r)**2)==0
rho,lam=s.symbols('rho lam')
R=rho+lam/(z*z-a)
assert s.cancel((z*z-1)*s.diff(R,z)+2*z*R-2*z*(rho+lam*(1-a)/(z*z-a)**2))==0
x=s.symbols('x'); A=[s.Integer(1),s.Integer(1)]
for n in range(1,13):A.append(s.expand((1+n*x)*A[-1]+x*(1-x)*s.diff(A[-1],x)))
Cs=[None]+[s.cancel((z+1)**(n-1)*A[n].subs(x,(z-1)/(z+1))).expand() for n in range(1,14)]
for n in range(1,13):
 assert s.expand(Cs[n+1]-s.diff((z*z-1)*Cs[n],z))==0
for n in range(3,13):
 Fn=(z*z-1)*Cs[n-2]
 assert s.expand(s.diff(Fn,z)-Cs[n-1])==0
 assert s.LC(s.Poly(Cs[n],z))==s.factorial(n)
 assert s.cancel((Cs[n]/Fn).subs(z,-z)-Cs[n]/Fn)==0
print(json.dumps({'python':sys.version,'sympy':s.__version__,'platform':platform.platform(),'symbolic_checks':{'main_polynomial_identity':'exact zero','positive_pair_decomposition':'exact zero','paired_log_derivative_formula':'exact zero','residue_induction_formula':'exact zero'},'eulerian_cayley_recurrence_n':list(range(1,13)),'residue_setup_n':list(range(3,13))},indent=2))
