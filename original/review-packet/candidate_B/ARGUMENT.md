# All-degree quadratic partial region: complete elementary proof

## Statement
For every pair of real parameters b,c >= 0 satisfying

    c <= 1 + (b+1)^2/4,

and every integer n >= 3, the polynomial

    A_n(x) + b A_{n-1}(x) + c A_{n-2}(x)

has n-1 distinct strictly negative roots. Thus this is an all-degree extension beyond the cited baseline; in particular it proves the entire subfamily b=0, 0<=c<=5/4. It does NOT establish the proposed larger bound c<=b^2/4+b+3.

The proof below applies more generally to any positive-leading-coefficient reciprocal polynomial F of degree m-1 having distinct strictly negative roots, followed by two applications of the Eulerian differential recurrence with indices m and m+1.

## Eulerian preliminaries
Let q(x)=x(1-x). The recurrence is

    A_{k+1}=(1+kx)A_k+q A_k'.

Inductively A_k has degree k-1, leading and constant coefficients 1, positive coefficients, reciprocal symmetry x^(k-1) A_k(1/x)=A_k(x), and distinct strictly negative roots. Degree, coefficients and symmetry follow directly by coefficient comparison in the recurrence. To prove root location, suppose F=A_k has roots a_1<...<a_{k-1}<0. At each a_i, A_{k+1}(a_i)=q(a_i)F'(a_i), whose signs alternate because q(a_i)<0. The signs at -infinity and 0 supply the two exterior roots, giving k distinct negative roots. The base A_1=1, A_2=1+x is immediate.

## Rational quotient identities
Fix m=n-2 >=1 and write

    F=A_m, G=A_{m+1}, H=A_{m+2}, R=G/F.

Let a_1,...,a_{m-1}<0 be the roots of F; the sum below is empty for m=1. From the recurrence and logarithmic derivative,

    R(x)=1+mx+q(x) sum_j 1/(x-a_j)
        =x+1+sum_j (1-a_j)x/(x-a_j).

Consequently, at any real point off the poles,

    R'(x)=1-sum_j a_j(1-a_j)/(x-a_j)^2 >=1.

The inequality is strict when m>=2. Also reciprocity of G and F gives

    R(1/x)=R(x)/x,
    R'(1/x)=R(x)-x R'(x)                         (x !=0).

The next recurrence yields the exact quotient identity

    H/F=R^2+xR+qR'.

All these statements are algebraic identities, not external preservation results.

## A separating polynomial
Set d=(b+1)/2>0 and Q=G+dF. Since the poles of R have negative residues a_j(1-a_j), the strictly increasing function R crosses -d once in each interval separated by the roots of F, including the two exterior intervals. On the rightmost interval R(0)=1>-d, so that root is negative as well. Thus Q has m distinct negative roots r_1<...<r_m, and F strictly interlaces Q. There are no common roots: at each a_j, G(a_j)=q(a_j)F'(a_j)!=0. This also covers m=1, when Q=x+1+d.

At each root r of Q, R(r)=-d. Reciprocity gives

    q(r) R'(r)=(1-r)(-d-R'(1/r)).

Combining the exact identities gives

    [H+bG+cF]/F (r)
      =d^2-(b+1)d+c-(1-r)R'(1/r).

The reciprocal point 1/r cannot be a pole because F is reciprocal and F(r)!=0. Since r<0 and R'(1/r)>=1,

    [H+bG+cF]/F (r)
      <=d^2-(b+1)d+c-(1-r)
      =c-1-(b+1)^2/4+r
      <=r<0.

This is strict even when c=1+(b+1)^2/4, and it applies to arbitrary real b,c in the stated region.

## Root count
P=H+bG+cF is monic of degree m+1 and P(0)=1+b+c>0. Since F strictly interlaces Q and P(r_i)/F(r_i)<0, the signs P(r_i) alternate. Specifically sign F(r_i)=(-1)^(m-i) and sign P(r_i)=(-1)^(m-i+1). Therefore P has one root in (-infinity,r_1), one in each (r_i,r_{i+1}), and one in (r_m,0). There are m+1 such disjoint intervals, equal to the degree of P. All roots are therefore distinct and negative.

## Gap to the requested criterion
The proved upper bound is b^2/4+b/2+5/4. The proposed upper bound is b^2/4+b+3. The remaining vertical gap is b/2+7/4 for every fixed b>=0. This proof gives no conclusion about that gap.

## Full-bound reduction, unproved
Set d=1+b/2. The same separating-polynomial proof would establish the full proposed bound if one proved

    -x(1-x)R'(x)+(2-x)R(x)-2 >=0

for every Eulerian quotient R=A_{m+1}/A_m at every x<0 with R(x)<=-1. Equivalently, at R=-d, one needs

    (1-x)R'(1/x) >= d+2.

The derivative bound R'>=1 used above is insufficient. This strengthened inequality holds for all x<=1-sqrt(2) purely from negative roots and reciprocal pairing, but the remaining interval (1-sqrt(2),0) requires extra structure of the Eulerian sequence. It is false for arbitrary reciprocal negative-rooted F: repeated roots concentrated near -1 supply counterexamples to the larger generic claim. No all-degree proof of the strengthened Eulerian inequality has been obtained in this note.
