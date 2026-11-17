import json,platform,sys
import sympy as s
x,y,b,c=s.symbols('x y b c')
A=[s.Integer(1),s.Integer(1)]
for n in range(1,10):
 A.append(s.expand((1+n*x)*A[-1]+x*(1-x)*s.diff(A[-1],x)))
def B(n):
 return s.cancel((1+y)**(n-1)*A[n].subs(x,(y-1)/(y+1))).expand()
def L(f):
 return s.expand((y*y-1)**2*s.diff(f,y,2)+(y*y-1)*((6+b)*y+b)*s.diff(f,y)+((6+2*b+c)*y*y+(2*b+2*c)*y+c-2)*f)
checks=[]
for n in range(3,11):
 rhs=B(n)+b*(1+y)*B(n-1)+c*(1+y)**2*B(n-2)
 assert s.expand(L(B(n-2))-rhs)==0
 checks.append(n)
bad=s.Poly(L(y*y-s.Rational(1,100)).subs({b:0,c:3}),y)
assert bad.count_roots(-s.oo,s.oo)==2
ks=[]
for m in range(2,7):
 f,g,h=A[m:m+3]
 H=s.expand(g*g+2*f*g-2*f*f-f*h)
 H2=s.expand(x*x*(1-x)**2*(s.diff(f,x)**2-f*s.diff(f,x,2))+x*(1-x*x)*f*s.diff(f,x)+(m-1)*x*f*f)
 assert H==H2
 K=s.Poly(s.cancel(H/x),x)
 ks.append({'m':m,'K':str(K.as_expr()),'distinct_real_roots':int(K.count_roots(-s.oo,s.oo))})
out={'python':sys.version,'sympy':s.__version__,'platform':platform.platform(),'transformation_identity_checked_n':checks,'generic_preserver_obstruction':{'F':'y**2-1/100','b':0,'c':3,'output':str(bad.as_expr()),'degree':bad.degree(),'distinct_real_roots':int(bad.count_roots(-s.oo,s.oo)),'squarefree':s.gcd(bad,bad.diff()).degree()==0},'turan_identity_and_root_counts':ks}
print(json.dumps(out,indent=2))
