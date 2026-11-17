import sympy as s,json,time,argparse
from pathlib import Path
parser=argparse.ArgumentParser()
parser.add_argument('--max-m',type=int,default=30,help='Largest m; 27 reproduces the completed attempt.')
args=parser.parse_args()
x=s.symbols('x');A=[s.Poly(1,x),s.Poly(1,x)]
for n in range(1,31): A.append(s.Poly((1+n*x)*A[n].as_expr()+x*(1-x)*A[n].diff().as_expr(),x))
records=[]
for m in range(2,args.max_m+1):
 h,g=A[m],A[m+1]
 H=s.Poly(-x*(1-x)*(g.diff()*h-g*h.diff()).as_expr()+(2-x)*(g*h).as_expr()-2*(h*h).as_expr(),x).exquo(s.Poly(x,x))
 start=time.time()
 cnt=H.count_roots(-s.oo,0)
 intervals=H.intervals(eps=s.Rational(1,10**9)) if m<=12 else []
 neg=[(str(p),str(q),mult) for (p,q),mult in intervals if q<0]
 record=dict(m=m,negative_roots=int(cnt),negative_intervals=neg,seconds=time.time()-start)
 records.append(record);print(record,flush=True)
 Path(__file__).with_name('aux_counts.json').write_text(json.dumps(records,indent=2))
