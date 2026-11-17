import sympy as s
x,b,c=s.symbols('x b c')
a=[s.Integer(1),s.Integer(1)]
for n in range(1,8): a.append(s.expand((1+n*x)*a[n]+x*(1-x)*s.diff(a[n],x)))
for n in (3,4,5):
 p=a[n]+b*a[n-1]+c*a[n-2]
 disc=s.factor(s.discriminant(p,x))
 print('N',n,'POLY',p)
 print('DISC',disc)
 print('BOUNDARYDISC',s.factor(disc.subs(c,b*b/4+b+3)))
