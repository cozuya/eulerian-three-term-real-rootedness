# Independent Sturm-route review

This file records the separate derivation performed by the `proof_sturm` agent.
The root agent supplied the proposed quadratic subregion; the algebra and sign
argument below were independently derived and checked. No formal verification
is claimed.

## 0. Stronger final subregion: independently audited

The following new result supplied by the root agent was independently expanded
and audited here. It supersedes both earlier subregions below:

    b,c>=0 and c<=1+(b+1)^2/4
      ==> A_n+b*A_{n-1}+c*A_{n-2} has simple negative roots for every n>=3.

Put m=n-2>=1, h=A_m, g=A_{m+1}, f=A_{m+2}, R=g/h. Write the roots of h as
-a_j, a_j>0 (an empty list if m=1). The recurrence gives the exact identity

    R(x)=1+x+sum_j x*(1+a_j)/(x+a_j).

Hence

    R'(x)=1+sum_j a_j*(1+a_j)/(x+a_j)^2,

    J(x):=(1-x)*R'(x)+R(x)
         =2+sum_j (1+a_j)*(a_j+x^2)/(x+a_j)^2.

The earlier recurrence computation gives

    T(x):=R(x)^2-f(x)/h(x)=-x*J(x).

Direct subtraction now yields

    T(x)-(1-R(x))
       =-x+x^2*(1-x)*sum_j (1+a_j)/(x+a_j)^2 >0

for every negative x that is not a pole. This includes m=1: the sum is empty,
but -x remains strictly positive.

Let alpha=(b+1)/2>0 and q=g+alpha*h. The already-established Eulerian
interlacing implies q is monic of degree m, has simple negative roots, and
strictly interlaces h. At any root r of q, R(r)=-alpha, so

    -f(r)/h(r)+b*alpha
       =T(r)-alpha^2+b*alpha
       >1+(b+1)*alpha-alpha^2
       =1+(b+1)^2/4 >=c.

Thus P_n(r)/h(r)<0 at every q root. The degree and sign argument in Section 1
proves the result, now uniformly for all n>=3 with no separate base-case
estimate. It also covers the boundary with simple roots, since the decisive
inequality is strict.

No central lemma is missing from this partial theorem. It uses only the
Eulerian recurrence, its elementary strict-interlacing induction, rational
identities, and the intermediate value theorem. It does not establish the
original sharp conjecture.

## 0a. Second independent audit: two-step interlacing and the strip

The transform agent supplied a specialized self-contained induction proving
two-step Eulerian interlacing. I independently checked its decisive residue
calculation and degree/parity issues as follows.

Define C_n(z)=(z+1)^(n-1)*A_n((z-1)/(z+1)) and
F_n(z)=(z^2-1)*C_{n-2}(z). Then

    C_{n+1}=((z^2-1)*C_n)', F_n'=C_{n-1},
    F_{n+1}=(z^2-1)*F_n'.

The asserted inductive partial fraction form is

    C_n/F_n = rho + sum_j lambda_j/(z^2-a_j),
    rho>0, lambda_j>0, 0<a_j<=1.

The base n=3 is 6+4/(z^2-1). At a positive root xi of F_n' in (0,1),

    C_{n+1}(xi)/F_n(xi)
      =2*xi*[rho+sum_j lambda_j*(1-a_j)/(xi^2-a_j)^2]>0.

At the same point,

    F_{n+1}'(xi)/F_n(xi)
      =(xi^2-1)*F_n''(xi)/F_n(xi)>0,

because F_n'/F_n=0 and F_n''/F_n=-sum_r 1/(xi-r)^2<0. Thus the
residue of C_{n+1}/F_{n+1} at xi is positive. The endpoint xi=1 has positive
residue C_n(1)/F_n'(1). When the polynomials are odd, their simple zero at 0
cancels. Parity then pairs residues at opposite poles, with squared-variable
residue 2*xi*Res>0. Their leading coefficient ratio is positive. This proves
the inductive form. Its strict monotonicity in z^2 and the already-proved
Eulerian real-rootedness give the required alternating squared roots. There
is no reliance on an unproved implication from consecutive interlacing.

Consequently H=(1+x)*A_{n-2} weakly interlaces A_n, strictly if n is odd.
For K=A_n-c*x*A_{n-2}, n>=4, 0<=c<=n-1, I also checked the following
interlacer-continuation argument.

At any root r of g=A_{n-1}, the rational formula above gives
K(r)/h(r)=r*(J(r)-c), where h=A_{n-2}. Each summand in J is strictly larger
than 1 at negative r, since

    (1+a)*(a+r^2)-(r+a)^2=a*(r-1)^2>0.

Thus J(r)>n-1 for n>=4. The signs give strict interlacing of g and K.

At every noncentral root of h, K and A_n agree. For odd n, the additional
H root is -1; here g(-1)=0 and K(-1)/h(-1)=-J(-1)+c<0. Therefore H strictly
interlaces K. For even n, factor a common (x+1) from K and H. At x=-1 the
remaining K factor has value A_n'(-1)+c*A_{n-2}'(-1). Since

    A_n'(-1)/A_{n-2}'(-1)
       =A_{n+1}(-1)/A_{n-1}(-1)<-n,

the sign at -1 remains that at c=0. The last strict inequality follows from
the same J bound applied with h=A_{n-1}, g=A_n at x=-1. All other reduced-H
root signs are fixed. Thus the reduced pair strictly interlaces, and restoring
the common factor gives weak interlacing of H and K.

The two interlacers g and H have nonnegative coefficients; hence their
nonnegative combination b*g+c*H interlaces K (this follows directly by
adding their signed values at the K roots, or by partial fractions).
Therefore K+b*g+c*H=A_n+b*A_{n-1}+c*A_{n-2} is real-rooted whenever
n>=4, b>=0, 0<=c<=n-1. Together with the n=3 discriminant this proves the
all-degree strip 0<=c<=3 for every b>=0, supplementing the quadratic region.

The Ma preprint's Corollary 1 states the same two-step interlacing result and
was directly inspected at
https://www.researchgate.net/publication/413485066_THE_EULERIAN_COMBINATIONS
(Corollary 1, page 17). However, the specialized induction above supplies
the needed fact without an external dependency.

## 1. Earlier rigorous subregion (superseded)

For every real b,c >= 0 with

    c <= 1 + (b+1)^2/5,

the polynomials A_n + b A_{n-1} + c A_{n-2} have simple negative roots for every
n >= 3.

For n >= 4 put m=n-2, h=A_m, g=A_{m+1}, f=A_{m+2}, and R=g/h. The standard
Eulerian recurrence proves inductively that h and g have simple negative roots
and strictly interlace. For alpha>=0, q=g+alpha*h has simple negative roots and
strictly interlaces h (the degree of q is m and that of h is m-1).

Let r be a root of q. It is not a root of h, and R(r)=-alpha. Put L=h'/h.
The recurrence gives

    R=1+m*x+x*(1-x)*L,
    f/h=R*(R+x)+x*(1-x)*R'.

Because h has m-1 distinct real roots,

    -L'(r) = sum_j 1/(r-lambda_j)^2 >= L(r)^2/(m-1).

Substitute r*(1-r)*L(r)=-alpha-1-m*r into the preceding identities. The result is

    -f(r)/h(r)+b*alpha
      >= r^2 + alpha*r - alpha^2 + alpha*(b+1) + 1
         + (r+alpha+1)^2/(m-1)

      = [m/(m-1)] * [r+(alpha*(m+1)+2)/(2*m)]^2
         + 1 + alpha*(b+1) - 5*alpha^2/4
         + (alpha+2)^2/(4*m).

Both displayed formulas were checked by symbolic expansion in SymPy. For
alpha=2*(b+1)/5, the final line is strictly greater than
1+(b+1)^2/5, because m is finite and (alpha+2)^2/(4*m)>0.

Thus, for the asserted c range, P_n(r)/h(r)<0 at every root of q. At the ordered
roots r_1<...<r_m of the monic degree-m polynomial q, strict interlacing gives
sign(h(r_i))=sign(q'(r_i))=(-1)^(m-i). Consequently P_n has one root in each
interval between consecutive r_i, one below r_1, and one above r_m. Its degree
is m+1, so these are all its roots and are distinct. Positive coefficients
exclude nonnegative roots.

For n=3 the exact discriminant condition is c<=b^2/4+b+3. The difference between
that threshold and 1+(b+1)^2/5 is (b+6)^2/20>0, so the two roots are distinct
and negative throughout the proved subregion.

## 2. Earlier piecewise subregion from palindromicity (superseded)

Let k=sqrt(2)-1 and b_0=5*k-1. The argument can be strengthened to

    c <= H(b), where

    H(b)=1+(b+1)^2/5                         if 0<=b<=b_0,
    H(b)=1+k^2+(b+1-k)^2/4                 if b>=b_0.

The branches agree, with equal derivatives, at b_0. The second branch has the
same quadratic leading coefficient 1/4 as the proposed full criterion.

Here is the extra lemma. For any palindromic polynomial h with only negative
roots, degree m-1, define R=1+m*x+x*(1-x)*h'/h and

    E=-x*(1-x)*R' + (2-x)*R - 2.

Away from h's roots, E>=0 for x<=1-sqrt(2)=-k. To prove this, write x=-t and
each root of h as -a, a>0. Direct algebra gives

    E/t = sum_a (a+1)*(t^2+2*t-a)/(a-t)^2.

The roots occur in reciprocal pairs a,1/a, with possible unpaired a=1. The
contribution of a reciprocal pair is

    (a+1)^2 * [a*t^4-4*a*t^2-a+2*t*(a^2+1)]
      / [(a-t)^2*(a*t-1)^2].

Its numerator bracket equals

    a*(t-1)^2*(t^2+2*t-1) + 2*t*(a-1)^2,

which is nonnegative for t>=k. The unpaired a=1 term is

    2*(t^2+2*t-1)/(1-t)^2,

and is likewise nonnegative. Poles are excluded because r is never a root of h.

At a root r of q=g+alpha*h, the identity

    -f(r)/h(r)+b*alpha
       = E(r) + 2+(b+2)*alpha-alpha^2

therefore gives the lower bound 2+(b+2)*alpha-alpha^2 whenever r<=-k. This
lower bound is strictly larger than either lower bound used below.

For -k<r<0, the first Cauchy formula in Section 1 yields

    -f(r)/h(r)+b*alpha
       >= 1+alpha*(b+1)-5*alpha^2/4+(r+alpha/2)^2
          +(r+alpha+1)^2/(m-1).

If 0<=alpha<=2*k, dropping the squares gives
1+alpha*(b+1)-5*alpha^2/4. If alpha>=2*k, the infimum of the first square on
(-k,0) is (alpha/2-k)^2, giving

    1+k^2+alpha*(b+1-k)-alpha^2.

All bounds at the roots needed for P_n are strict: in (-k,0), the finite-m
correction (r+alpha+1)^2/(m-1) is positive; in r<=-k, the E bound exceeds the
piecewise lower bound by a strictly positive quantity. Optimizing in alpha
gives alpha=2*(b+1)/5 for b<=b_0 and alpha=(b+1-k)/2 for b>=b_0, yielding H.
The same sign argument completes the all-degree proof. The n=3 check can also
be done directly. On the second branch,

    [b^2/4+b+3] - H(b)
       = ((1+k)/2)*b + 2-k^2-(1-k)^2/4 > 0

for b>=0. Thus n=3 is strictly inside its true discriminant region.

## 3. Unproved route to the full target

For the full conjectural boundary write alpha=b/2+1>=1, so c=alpha^2+2.
At a q=g+alpha*h root, the desired sign condition is exactly E(r)>=0.
Equivalently,

    (g(r)+h(r))^2 - 3*h(r)^2 - f(r)*h(r) >= 0.

This need only be proved at points where g/h=-alpha<=-1. The palindromic lemma
already settles r<=1-sqrt(2), so the obstruction is the interval
(1-sqrt(2),0). The assertion does NOT follow from palindromicity and simple
negative roots alone. An exact obstruction is

    h=x^2+(21/10)*x+1, m=3, r=-3/10,
    R=1+3*x+x*(1-x)*h'/h,
    alpha=-R(r)=539/460>1,
    E(r)=-113037/211600<0.

The roots of h are (-21+-sqrt(41))/20, distinct, negative, and reciprocal.
This is not an Eulerian counterexample; it isolates the missing property.
Thus an Eulerian-specific inequality is required.

## 4. Other failed routes

* Interlacing P_n directly with A_{n-1} is too strong. For n=3, b=0, c=3,
  the sole A_2 root is -1 while P_3=(x+2)^2. Even c>2 fails this interlacer.
* The linear map on quadratics sending P_3 to P_n is not a universal
  real-rootedness preserver. For n=4, the image of (x+t)^2 is
  A_4+(2t-4)A_3+(t^2-2t+3)A_2, with discriminant
  4*(2t-3)*(t^4+12t^3+58t^2+100t-19). This is negative, for example, at t=1.
  This does not refute the target because b=2t-4<0 there.
* General Cauchy-Schwarz on h'/h alone yields the quadratic subregion above;
  it loses Eulerian-specific information. Its completed square has an
  asymptotic minimum 1+(b+1)^2/5, so it cannot prove the proposed bound without
  additional input.
