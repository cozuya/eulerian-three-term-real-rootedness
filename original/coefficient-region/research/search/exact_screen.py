import sympy as s, time, json, platform, sys, argparse
from pathlib import Path
parser=argparse.ArgumentParser()
parser.add_argument('--limit',type=int,default=None,help='Run only the first N scheduled cases; 145 reproduces the completed attempt.')
args=parser.parse_args()
x=s.symbols('x')
a=[s.Poly(1,x),s.Poly(1,x)]
for n in range(1,65):
 a.append(s.Poly((1+n*x)*a[n].as_expr()+x*(1-x)*a[n].diff().as_expr(),x))
records=[]
cases=[]
for n in [3,4,5,10,20,21,25,30,40,50,64]:
 for b in [s.Rational(1,10**4),s.Rational(1,7),3,20,10**3,2**n,3**n,10**12]:
  for t in [s.Rational(99,100),1]: cases.append((n,s.Rational(b),t))
if args.limit is not None: cases=cases[:args.limit]
for j,(n,b,t) in enumerate(cases):
 c=t*(b*b/4+b+3)
 p=a[n]+b*a[n-1]+c*a[n-2]
 st=time.time()
 factors=p.sqf_list()[1]
 realcount=sum(mult*factor.count_roots(-s.oo,s.oo) for factor,mult in factors)
 rec=dict(n=n,b=str(b),c=str(c),t=str(t),degree=p.degree(),real_count=int(realcount),seconds=time.time()-st)
 records.append(rec)
 print(j+1,len(cases),rec,flush=True)
 if realcount!=p.degree():
  print('FAILURE',p.as_expr(),flush=True)
  break
 Path(__file__).with_name('exact_screen.json').write_text(json.dumps(dict(python=sys.version,sympy=s.__version__,records=records),indent=2))
print('DONE',len(records),flush=True)
