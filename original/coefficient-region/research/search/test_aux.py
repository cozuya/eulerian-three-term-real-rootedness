from fractions import Fraction
import json,sys,time
from pathlib import Path
# Increasing coefficient order; all comparisons exact.
def add(a,b):
 c=[0]*max(len(a),len(b))
 for i,v in enumerate(a): c[i]+=v
 for i,v in enumerate(b): c[i]+=v
 while len(c)>1 and not c[-1]:c.pop()
 return c
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,u in enumerate(a):
  for j,v in enumerate(b):c[i+j]+=u*v
 return c
def scale(a,k):return [k*v for v in a]
def der(a):return [i*v for i,v in enumerate(a)][1:]
def evaluate(a,p,q):
 v=a[-1];qpower=q
 for coeff in reversed(a[:-1]):
  v=v*p+coeff*qpower;qpower*=q
 return v
A=[[1],[1]]
for n in range(1,101):
 old=A[n];new=[0]*(len(old)+1)
 for j,v in enumerate(old):
  new[j]+=(j+1)*v;new[j+1]+=(n-j)*v
 A.append(new)
xs=set()
for i in range(-240,241): xs.add(Fraction(-round(10**(i/20)*10**15),10**15))
for q in [1,2,3,5,7,11,100,1000]:
 for p in range(1,201):xs.add(Fraction(-p,q))
# Probe much larger and smaller points for extreme roots.
for k in range(1,102):
 for p in [1,3,5,7]:xs.add(Fraction(-p*2**k));xs.add(Fraction(-p,2**k))
xs=sorted(x for x in xs if x<0)
records=[]
for m in range(1,101):
 h,g=A[m],A[m+1]
 w=add(mul(der(g),h),scale(mul(g,der(h)),-1))
 H=add(add(mul([0,-1,1],w),mul([2,-1],mul(g,h))),scale(mul(h,h),-2))
 bad=None;eligible=0;negative_elsewhere=0
 for xx in xs:
  p,q=xx.numerator,xx.denominator
  hv=evaluate(h,p,q);gv=evaluate(g,p,q)
  if hv==0:continue
  E=evaluate(H,p,q)
  pred=hv*(gv+q*hv)<=0
  if pred:
   eligible+=1
   if E<0:bad=dict(x=str(xx),h=str(hv),g=str(gv),H=str(E));break
  elif E<0:negative_elsewhere+=1
 rec=dict(m=m,points=len(xs),eligible=eligible,negative_elsewhere=negative_elsewhere,bad=bad)
 records.append(rec);print(rec,flush=True)
 Path(__file__).with_name('aux_screen.json').write_text(json.dumps(dict(python=sys.version,records=records),indent=2))
 if bad:break
