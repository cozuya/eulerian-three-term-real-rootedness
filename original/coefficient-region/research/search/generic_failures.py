import sympy as s,json,sys
from pathlib import Path
x=s.symbols('x');h=(1+x)**10
R=1+11*x+x*(1-x)*s.diff(h,x)/h
E=-x*(1-x)*s.diff(R,x)+(2-x)*R-2
r=s.factor(R.subs(x,-s.Rational(1,10)))
e=s.factor(E.subs(x,-s.Rational(1,10)))
f=(1+x)**2;m=3
g=s.expand((1+m*x)*f+x*(1-x)*s.diff(f,x))
k=s.expand((1+(m+1)*x)*g+x*(1-x)*s.diff(g,x))
p=s.Poly(k+3*f,x)
sturm=[s.Poly(q,x) for q in s.sturm(p.as_expr(),x)]
def sig(v): return 1 if v>0 else -1 if v<0 else 0
neg=[sig(q.LC())*((-1)**q.degree()) for q in sturm]
pos=[sig(q.LC()) for q in sturm]
def variations(v):
 v=[z for z in v if z];return sum(a!=b for a,b in zip(v,v[1:]))
result=dict(python=sys.version,sympy=s.__version__,auxiliary_counterexample=dict(h=str(h),x='-1/10',R=str(r),E=str(e)),generic_operator_counterexample=dict(m=m,f=str(f),b=0,c=3,output=str(p.as_expr()),sturm=[str(q.as_expr()) for q in sturm],signs_minus_infinity=neg,signs_plus_infinity=pos,variations_minus_infinity=variations(neg),variations_plus_infinity=variations(pos),real_count=variations(neg)-variations(pos)))
print(json.dumps(result,indent=2))
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2))
assert r < -1 and e < 0
assert result['generic_operator_counterexample']['real_count']==2
