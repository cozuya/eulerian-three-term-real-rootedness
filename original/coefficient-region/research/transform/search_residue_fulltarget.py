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
   b=2*alpha-2;c=alpha*alpha+2
   target=h+b*(z+1)*g+c*(z+1)**2*f
   roots=target.roots()
   if max(abs(r.imag) for r in roots)>1e-6:
    rec={'degree':d,'positive_roots':ps.tolist(),'alpha':alpha,'roots':[[r.real,r.imag] for r in roots],'residues_test':lamb};print(json.dumps(rec),flush=True);records.append(rec)
   if records:break
  if records:break
 if records:break
print(json.dumps({'valid_polys':valid,'counterexamples':records}),flush=True)
