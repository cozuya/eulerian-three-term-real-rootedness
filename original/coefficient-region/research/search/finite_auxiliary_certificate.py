"""Exact finite auxiliary certificates for m=2,...,27.

This is an exact semialgebraic certificate, not a sample of b,c points.
A positive rescaling of each member of a Sturm remainder chain preserves
all endpoint signs and the Sturm variation theorem. Coefficients and
endpoint sign vectors are retained for independent reproduction.
"""
import argparse,json,sys,time,hashlib
from fractions import Fraction
from pathlib import Path
import sympy as s

x=s.symbols('x')

def eulerian_coefficients(maximum):
    A=[[1],[1]]
    for n in range(1,maximum):
        row=[0]*(len(A[n])+1)
        for j,v in enumerate(A[n]):
            row[j]+=(j+1)*v
            row[j+1]+=(n-j)*v
        A.append(row)
    return A

def plus(a,b):
    ans=[0]*max(len(a),len(b))
    for i,z in enumerate(a):ans[i]+=z
    for i,z in enumerate(b):ans[i]+=z
    while len(ans)>1 and ans[-1]==0:ans.pop()
    return ans

def times(a,b):
    ans=[0]*(len(a)+len(b)-1)
    for i,u in enumerate(a):
        for j,v in enumerate(b):ans[i+j]+=u*v
    return ans

def scale(a,c):return [c*z for z in a]

def value_numerator(coefficients,r):
    p,q=r.numerator,r.denominator
    ans=coefficients[-1]
    qpow=q
    for z in reversed(coefficients[:-1]):
        ans=ans*p+z*qpow
        qpow*=q
    return ans

def sign(z):return 1 if z>0 else -1 if z<0 else 0

def variations(signs):
    nonzero=[z for z in signs if z]
    return sum(a!=b for a,b in zip(nonzero,nonzero[1:]))

def primitive_positive_scale(p):
    """Return a positive rational multiple of p with primitive ZZ coefficients."""
    denominator,p=p.clear_denoms(convert=True)
    assert denominator>0
    content,p=p.primitive()
    assert content>0
    return p

def primitive_sturm(coefficients):
    f=s.Poly.from_list(list(reversed(coefficients)),gens=x,domain=s.ZZ)
    chain=[primitive_positive_scale(f),primitive_positive_scale(f.diff())]
    while True:
        remainder=-(chain[-2].set_domain(s.QQ).rem(chain[-1].set_domain(s.QQ)))
        if remainder.is_zero:break
        chain.append(primitive_positive_scale(remainder))
    return chain

def signs_at(chain,r):
    if r is None:
        return [sign(p.LC())*((-1)**p.degree()) for p in chain]
    z=s.Rational(r.numerator,r.denominator)
    return [sign(p.eval(z)) for p in chain]

def chain_digest(chain):
    payload='\n'.join(','.join(str(v) for v in p.all_coeffs()) for p in chain)
    return hashlib.sha256(payload.encode()).hexdigest()

def certificate(m,A,previous):
    started=time.time()
    h,g,f=A[m],A[m+1],A[m+2]
    H=plus(plus(times(g,g),scale(times(h,f),-1)),plus(scale(times(g,h),2),scale(times(h,h),-2)))
    assert H[0]==0
    K=H[1:]
    assert len(K)-1==2*m-2
    assert K[-1]<0 and K[0]>0
    q=plus(g,h)
    h_chain=primitive_sturm(K)
    h_minus=signs_at(h_chain,None)
    h_zero=signs_at(h_chain,Fraction(0))
    h_vminus,h_vzero=variations(h_minus),variations(h_zero)
    assert h_vminus-h_vzero==1
    assert previous[m]['negative_roots']==1
    # Distinct-root count is sufficient for the inference. This checks squarefreeness too.
    assert h_chain[-1].degree()==0
    # K=H/x is negative before its unique negative root and positive just after it.
    lo,hi=Fraction(-1),Fraction(0)
    assert value_numerator(K,lo)<0 and value_numerator(K,hi)>0
    for _ in range(m+12):
        mid=(lo+hi)/2
        z=value_numerator(K,mid)
        if z<0:lo=mid
        elif z>0:hi=mid
        else:
            # Keep an interval strictly on either side of an exact dyadic root.
            hi=mid
    r0=lo
    H_numerator=value_numerator(H,r0)
    assert H_numerator>0
    q_numerator=value_numerator(q,r0)
    assert q_numerator!=0
    q_chain=primitive_sturm(q)
    q_r0=signs_at(q_chain,r0)
    q_zero=signs_at(q_chain,Fraction(0))
    q_vr0,q_vzero=variations(q_r0),variations(q_zero)
    assert q_vr0-q_vzero==0
    return dict(m=m,n=m+2,H_coefficients_ascending=H,K_H_over_x_coefficients_ascending=K,
        Q1_coefficients_ascending=q,K_degree=len(K)-1,K_leading_sign=sign(K[-1]),
        K_constant_sign=sign(K[0]),K_squarefree=True,
        K_sturm_degrees=[int(z.degree()) for z in h_chain],
        K_sturm_signs_minus_infinity=h_minus,K_sturm_signs_zero=h_zero,
        K_variations_minus_infinity=h_vminus,K_variations_zero=h_vzero,
        K_negative_root_count=h_vminus-h_vzero,K_sturm_chain_sha256=chain_digest(h_chain),
        r0=str(r0),H_at_r0_numerator=H_numerator,H_at_r0_denominator_power=len(H)-1,
        Q1_at_r0_numerator=q_numerator,
        Q1_sturm_degrees=[int(z.degree()) for z in q_chain],
        Q1_sturm_signs_r0=q_r0,Q1_sturm_signs_zero=q_zero,
        Q1_variations_r0=q_vr0,Q1_variations_zero=q_vzero,
        Q1_root_count_r0_to_zero=q_vr0-q_vzero,Q1_sturm_chain_sha256=chain_digest(q_chain),
        seconds=time.time()-started)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--max-m',type=int,default=27)
    parser.add_argument('--output',default=str(Path(__file__).with_suffix('.json')))
    args=parser.parse_args()
    assert 2<=args.max_m<=27
    previous={r['m']:r for r in json.loads(Path(__file__).with_name('aux_counts.json').read_text())}
    A=eulerian_coefficients(args.max_m+2)
    records=[]
    out=dict(python=sys.version,sympy=s.__version__,method='primitive positive-rescaled exact Sturm chains',
        coefficient_order='ascending',records=records)
    for m in range(2,args.max_m+1):
        rec=certificate(m,A,previous)
        records.append(rec)
        Path(args.output).write_text(json.dumps(out,indent=2))
        print(json.dumps(dict(m=m,r0=rec['r0'],K_negative_roots=rec['K_negative_root_count'],
            Q1_roots_to_zero=rec['Q1_root_count_r0_to_zero'],seconds=rec['seconds'])),flush=True)
    print('ALL FINITE AUXILIARY CERTIFICATES VERIFIED',flush=True)

if __name__=='__main__':main()
