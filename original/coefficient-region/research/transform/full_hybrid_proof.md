# Full proof by a hybrid sequence of test points

## Theorem
Let A_0=A_1=1 and A_(n+1)=(1+nx)A_n+x(1-x)A_n'. For fixed real
b,c>=0, every A_n+b A_(n-1)+c A_(n-2), n>=3, is real-rooted if and only
if c<=b^2/4+b+3.

Necessity is the n=3 discriminant. We prove sufficiency below.

## Standard facts and notation
The recurrence and signs at roots prove inductively that A_j is monic
of degree j-1 and has simple negative roots, and that A_j strictly
interlaces A_(j+1). It is reciprocal, either by reversal of permutations
or directly by the recurrence. Set

C_j(z)=(1+z)^(j-1) A_j((z-1)/(z+1)),
T=(z^2-1)D+2z.

Then C_(j+1)=T C_j. The polynomial C_j has degree j-1, positive leading
coefficient, parity j-1, and simple roots in (-1,1). It has a root at
zero exactly when j is even.

The separately proved positive-residue lemma states that for n>=3,
F_n=(z^2-1)C_(n-2),

C_n/F_n=rho+sum_j lambda_j/(z^2-a_j),

where rho>0, lambda_j>0 and 0<a_j<=1. The poles are exactly the positive
squared roots of F_n; the common parity zero at zero is canceled. See
two_step_interlacing_proof.md for its complete elementary inductive proof.
In particular, at any positive root r of C_(n-2),

C_n(r)/C_(n-1)(r)>0.                         (1)

Indeed F_n'(r)=C_(n-1)(r), and the ordinary residue at r is positive.

## A one-sided logarithmic-derivative inequality
Let f be any nonconstant polynomial whose simple roots lie in (-1,1)
and are symmetric under r->-r. For -1<z<0 away from its roots put

L(z)=f'(z)/f(z)=sum_r 1/(z-r),
V(z)=sum_r 1/(z-r)^2.

Then

E(z)=(1-z^2)V(z)-2L(z)>0.                   (2)

Proof: put u=-z in (0,1). A root at zero contributes
(1+2u-u^2)/u^2>0. A root pair +/-sqrt(a), with 0<a<1, contributes

2 N(u,a)/(u^2-a)^2,
N(u,a)=u^2(1+2u-u^2)+a(1-2u-u^2)
      =a(1-u)^3(1+u)+(1-a)u^2(1+2u-u^2)>0.

Summing proves (2). This argument is genuinely one-sided; the analogous
inequality may fail at positive z, even for Eulerian polynomials away
from the particular points needed in the target.

## Sign at negative roots of a shifted consecutive polynomial
Take n>=4, m=n-2, and abbreviate

f=C_m, g=C_(m+1)=Tf, h=C_(m+2)=Tg,
alpha=b/2+1>=1, C=alpha^2+2=b^2/4+b+3.

The Cayley transform of the target is

P(z)=h(z)+b(z+1)g(z)+c(z+1)^2f(z).           (3)

It has degree m+1: its leading coefficient equals the positive value of
the original target at x=1. Define

q(z)=g(z)+alpha(z+1)f(z).                    (4)

This is the Cayley transform of A_(m+1)+alpha A_m, hence it has m simple
roots in (-1,1), strictly interlacing the roots of f. This can also be
seen directly: at each root r of f, q(r)=(r^2-1)f'(r), while q(1)>0 and
q(-1) has sign (-1)^m. Signs give one root in every gap, including the
endpoint gaps.

The following exact polynomial identity is the decisive computation:

P f = q^2+(z+1)^2(c-alpha^2-2)f^2
      -(1-z^2)[(1-z^2)(f'^2-f f'')-2f f'].  (5)

It follows by substituting g=(z^2-1)f'+2zf and
h=(z^2-1)^2f''+6z(z^2-1)f'+(6z^2-2)f into (3), using b=2alpha-2,
and expanding. The identity was also derived independently by the
countersearch reviewer.

At a negative root s of q, f(s)!=0. The square q^2 vanishes, the second
term is nonpositive because c<=alpha^2+2, and the last term is strictly
negative by (2), since its bracket equals f(s)^2 E(s). Therefore

P(s)/f(s)<0,

or equivalently

sign P(s)=-sign f(s)                        (6)

at every negative q root. The sign is strict even on the target boundary.

## Sign at positive roots of f
At a positive root r of f, (1) gives h(r)/g(r)>0. Since b>=0 and r+1>0,

P(r)=h(r)+b(r+1)g(r)

has the same sign as g(r). Also g(r)=(r^2-1)f'(r), so

sign P(r)=-sign f'(r).                      (7)

The c term vanishes. Notice that this uses a different family of test
points on the positive half-interval; no unproved two-sided extension of
(2) is needed.

## Counting all roots
At the endpoints,

sign P(-1)=sign h(-1)=(-1)^(m+1),
P(1)>0.                                    (8)

We place test points between these endpoints as follows.

### Case I: f has even degree 2p (m=2p+1, n odd)
Here p>=1 since n>=4. The roots of f consist of p negative and p positive
roots. The polynomial q has p+1 negative roots and p positive roots.
To justify the extra negative root: q(0)=alpha f(0), and in the central
gap between the closest negative and positive f roots, the sign of q at
0 agrees with its sign at the positive endpoint and is opposite to its
sign at the negative endpoint. Therefore the unique central q root is
negative.

Use all p+1 negative q roots, followed by all p positive f roots. This
gives 2p+1=m test points, exactly degree(P)-1.

At the negative q roots, (6) alternates because f interlaces q. At the
smallest such root, f>0, so P<0, opposite to P(-1)>0. At the largest
negative q root, f has sign (-1)^p, so P has sign (-1)^(p+1).
At the first positive f root, (7) gives sign (-1)^p. Hence the signs
also alternate across the junction. They continue alternating along the
positive f roots. At the largest positive f root, P<0, opposite to
P(1)>0.

There are m+1 intervals between the two endpoints and m test points,
and every interval contains a root. They exhaust the degree of P, so
all its roots are real, simple, and inside (-1,1).

### Case II: f has odd degree 2p+1 (m=2p+2, n even), b>0
There are p negative f roots, a simple zero at 0, and p positive f roots.
Interlacing gives p+1 negative q roots and p+1 positive q roots.
Use the p+1 negative q roots, then 0, then the p positive f roots:
again exactly 2p+2=m test points.

At the smallest negative q root, f<0, so P>0, opposite to P(-1)<0.
The signs along these q roots alternate by (6). At the largest negative
q root, f has sign (-1)^(p+1), so P has sign (-1)^p.
Since f and h are odd and g is even,

P(0)=b g(0)=-b f'(0),

whose sign is (-1)^(p+1). Thus it is opposite to the last negative q
sign. If p>=1, the first positive f point has sign (-1)^p by (7), so
this junction alternates too. The remaining signs alternate through the
positive f roots to P(1)>0. When p=0 there are no positive f test points;
P(0)<0 and P(1)>0 provide the final sign change directly.

Again there are degree(P) disjoint sign-change intervals, proving all
roots real, simple, and inside (-1,1).

### Case III: n even and b=0
Fix 0<=c<=3. Apply Case II to b_epsilon>0 tending to zero with c fixed;
the bound holds because c<=3<b_epsilon^2/4+b_epsilon+3. The original
polynomials in x are monic of fixed degree n-1 and converge coefficientwise.
The set of monic real-rooted polynomials of a fixed degree is closed
(by continuity of the multiset of roots). Their limit is the desired
polynomial. Multiplicities are allowed, so this completes the case.

### The initial degree
For n=3, the polynomial is x^2+(b+4)x+(1+b+c), with discriminant
b^2+4b+12-4c>=0. This includes equality and its repeated root.

Since the Cayley map sends (-1,1) bijectively to (-infinity,0), the
transformed real roots in Cases I-II are precisely real negative roots
of the original target. Together with the limiting case and n=3, this
proves sufficiency for arbitrary real b,c in the full proposed region.
