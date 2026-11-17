"""Exact checks of the full proof's algebra and hybrid testpoint signs.

Algebraic testpoints are represented by exact rational isolating intervals.
Horner interval arithmetic proves the test-polynomial's sign throughout each
interval; no floating-point root approximations are used.
"""
import sympy as s,json,sys,time
from pathlib import Path

z=s.symbols('z')
F,D,DD,alpha,c=s.symbols('F D DD alpha c')
a=z*z-1
g=a*D+2*z*F
h=a*a*DD+6*z*a*D+(6*z*z-2)*F
Q=g+alpha*(1+z)*F
P=h+(2*alpha-2)*(1+z)*g+c*(1+z)**2*F
identity=s.expand(P*F-Q*Q-(1+z)**2*(c-alpha*alpha-2)*F*F
    +(1-z*z)*((1-z*z)*(D*D-F*DD)-2*F*D))
assert identity==0
w=s.symbols('w')
assert s.expand(w*w*(1+2*w-w*w)+(1-2*w-w*w)-(1-w)**3*(1+w))==0

C=[None,s.Poly(1,z)]
for n in range(1,15):
    C.append(s.Poly((z*z-1)*C[n].diff().as_expr()+2*z*C[n].as_expr(),z))

def sign(v):return 1 if v>0 else -1 if v<0 else 0

def interval_multiply(a,b):
    vals=[u*v for u in a for v in b]
    return min(vals),max(vals)

def polynomial_interval(p,interval):
    lo=hi=p.LC()
    for coeff in p.all_coeffs()[1:]:
        lo,hi=interval_multiply((lo,hi),interval)
        lo+=coeff;hi+=coeff
    return lo,hi

def certified_sign(p,interval):
    lo,hi=polynomial_interval(p,interval)
    if lo>0:return 1
    if hi<0:return -1
    if lo==hi==0:return 0
    raise ValueError(f'Interval too broad for sign: {interval}')

def isolations(p):
    out=p.intervals(eps=s.Rational(1,10**30))
    assert sum(mult for _,mult in out)==p.degree()
    assert all(mult==1 for _,mult in out)
    return [ij for ij,_ in out]

records=[];limit_records=[]
bvalues=[s.Rational(1,10**6),s.Rational(1,100),s.Rational(1,4),1,2,10,100,10**6]
for m in range(2,13):
    f,g,h=C[m],C[m+1],C[m+2]
    f_roots=isolations(f)
    pos_f=[ij for ij in f_roots if ij[0]>0]
    # Independent exact check of the two-step ratio sign at the positive f roots.
    for ij in pos_f:
        assert certified_sign(g,ij)==certified_sign(h,ij)
    bs=bvalues+([s.Integer(0)] if f.degree()%2==0 else [])
    for b in bs:
        al=s.Rational(b,2)+1
        q=g+al*s.Poly(1+z,z)*f
        q_roots=isolations(q)
        neg_q=[ij for ij in q_roots if ij[1]<0]
        pos_q=[ij for ij in q_roots if ij[0]>0]
        if f.degree()%2==0:
            pp=f.degree()//2
            assert len(neg_q)==pp+1 and len(pos_q)==pp
            points=neg_q+pos_f
            expected=[(-1)**i for i in range(1,len(points)+1)]
        else:
            pp=(f.degree()-1)//2
            assert len(neg_q)==pp+1 and len(pos_q)==pp+1
            points=neg_q+[(s.Integer(0),s.Integer(0))]+pos_f
            expected=[(-1)**(i+1) for i in range(1,len(points)+1)]
        for t in [s.Rational(0),s.Rational(1,2),s.Rational(1)]:
            cc=t*(al*al+2)
            p=h+b*s.Poly(1+z,z)*g+cc*s.Poly((1+z)**2,z)*f
            signs=[certified_sign(p,ij) for ij in points]
            assert signs==expected
            assert len(points)==p.degree()-1
            endpoints=[sign(p.eval(-1)),sign(p.eval(1))]
            fullsigns=[endpoints[0]]+signs+[endpoints[1]]
            assert all(u*v==-1 for u,v in zip(fullsigns,fullsigns[1:]))
            record=dict(m=m,n=m+2,b=str(b),c=str(cc),fraction_of_boundary=str(t),
                f_degree=f.degree(),P_degree=p.degree(),negative_Q_roots=len(neg_q),
                positive_f_roots=len(pos_f),testpoint_count=len(points),
                testpoint_intervals=[[str(lo),str(hi)] for lo,hi in points],
                P_signs_at_testpoints=signs,P_endpoint_signs=endpoints,
                sign_change_intervals=p.degree())
            records.append(record)
    # Cases handled by closedness in the proof: b=0 and f odd.
    if f.degree()%2==1:
        for cc in [s.Rational(0),s.Rational(3,2),s.Rational(3)]:
            p=h+cc*s.Poly((1+z)**2,z)*f
            count=sum(mult*factor.count_roots(-1,1) for factor,mult in p.sqf_list()[1])
            assert count==p.degree()
            limit_records.append(dict(m=m,n=m+2,b='0',c=str(cc),P_degree=p.degree(),
                exact_real_root_count_with_multiplicity=int(count)))
    print(json.dumps(dict(m=m,main_cases_so_far=len(records),limit_cases_so_far=len(limit_records))),flush=True)

# The elementary boundary n=3 includes a double root; count it with multiplicity.
for b in [s.Rational(0),s.Rational(1,7),s.Rational(10),s.Rational(10**6)]:
    al=b/2+1;cc=al*al+2
    p=C[3]+b*s.Poly(1+z,z)*C[2]+cc*s.Poly((1+z)**2,z)*C[1]
    count=sum(mult*factor.count_roots(-1,1) for factor,mult in p.sqf_list()[1])
    assert count==2
    limit_records.append(dict(m=1,n=3,b=str(b),c=str(cc),P_degree=p.degree(),
        exact_real_root_count_with_multiplicity=int(count),factorization=str(s.factor(p.as_expr()))))

output=dict(python=sys.version,sympy=s.__version__,generic_symbolic_identity_verified=True,
    pair_positivity_factorization_verified=True,method='exact rational isolating intervals and exact Horner interval arithmetic',
    main_hybrid_cases=len(records),b_zero_or_repeated_boundary_cases=len(limit_records),
    records=records,limit_records=limit_records)
Path(__file__).with_suffix('.json').write_text(json.dumps(output,indent=2))
print('HYBRID PROOF CHECKS ALL PASSED',len(records),len(limit_records),flush=True)
