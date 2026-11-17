import numpy as np,json
from numpy.polynomial import Polynomial as P
rng=np.random.default_rng(20261115)
z=P([0,1]);p=z*z-1
T=lambda f:p*f.deriv()+2*z*f
records=[];valid=0
for d in range(2,11):
 for it in range(3000):
  ps=np.sort(rng.uniform(.02,.98,d//2));rs=np.sort(np.r_[-ps, [0] if d%2 else [], ps]);f=P.fromroots(rs);g=T(f);h=T(g)
  lamb=[]
  for r in ps:
   val=6*r+(r*r-1)*2*sum(1/(r-s) for s in rs if s!=r)
   lamb.append(val)
  if min(lamb)<=1e-6:continue
  valid+=1
  for alpha in [1,1.25,2,4,10,100]:
   q=g+alpha*(z+1)*f
   for r in q.roots():
    if abs(r.imag)>1e-7:raise RuntimeError('unexpected q')
    r=r.real
    if not (0<r<1):continue
    L=sum(1/(r-s) for s in rs);S=sum(1/(r-s)**2 for s in rs)
    E=(1-r*r)*S-2*L
    if E< -1e-6:
     rec={'degree':d,'positive_roots':ps.tolist(),'alpha':alpha,'Qroot':r,'E':E,'residues_test':lamb};print(json.dumps(rec),flush=True);records.append(rec);break
   if records:break
  if records:break
 if records:break
print(json.dumps({'valid_polys':valid,'counterexamples':records}),flush=True)
