# Adversarial review of the full hybrid proof

Reviewer: independent `proof_sturm` agent. The final hybrid idea was supplied
by the transform agent/root; the reviewer reconstructed its sign count first
in Cayley coordinates and then independently in the original x coordinate.

**Outcome: PASS.** No unproved central lemma, incorrect quantifier, omitted
boundary, or circular interlacing inference was found in the proof described
below. This is a mathematical review, not Lean/formal verification.

## Statement audited

For all real b,c>=0, every polynomial

    P_n=A_n+b*A_{n-1}+c*A_{n-2}, n>=3,

has only real roots if and only if c<=b^2/4+b+3. The same pair b,c is used
for every n. The proof covers arbitrary real parameters, including equality.

## 1. Positive-residue lemma: checked induction

Define

    C_k(z)=(z+1)^(k-1)*A_k((z-1)/(z+1)),
    F_k(z)=(z^2-1)*C_{k-2}(z).

The recurrence gives C_{k+1}=((z^2-1)*C_k)' and F_k'=C_{k-1}.
All C_k roots are simple and lie in (-1,1), by the ordinary Eulerian
recurrence/interlacing proof. The F_k roots are also simple, adding only +-1.

The inductive form is

    C_k/F_k=rho_k+sum_j lambda_j/(z^2-a_j),
    rho_k>0, lambda_j>0, 0<a_j<=1.

For k=3 it is 6+4/(z^2-1). At a positive root xi of F_k' in (0,1),

    C_{k+1}(xi)/F_k(xi)
      =2*xi*[rho_k+sum_j lambda_j*(1-a_j)/(xi^2-a_j)^2]>0.

Also

    F_{k+1}'(xi)/F_k(xi)
      =(xi^2-1)*F_k''(xi)/F_k(xi)>0,

because F_k'(xi)=0 and F_k''(xi)/F_k(xi)=-sum_r 1/(xi-r)^2<0.
Therefore the residue at xi is positive. At endpoint 1 the residue is
C_k(1)/F_k'(1)=2>0. A zero at 0 cancels when the two polynomials are odd;
it is simple in both. Parity combines the residues at +-xi into a term with
lambda=2*xi*Res>0. The leading quotient is k(k+1)>0 at the next step.
These are all poles. Hence the partial-fraction form propagates.

For h=A_m, g=A_{m+1}, f=A_{m+2}, a root r of h in (-1,0) maps to a positive
root z of C_m. The positive residue of C_{m+2}/F_{m+2} there is
C_{m+2}(z)/C_{m+1}(z), because F_{m+2}'=C_{m+1}. It follows that

    f(r)/g(r)>0.

The ordinary adjacent interlacing ensures g(r) is nonzero. This proves
exactly the one-sided sign fact the full argument needs.

## 2. Negative-Q sign lemma: checked identity and strictness

Let R=g/h and

    E=-x*(1-x)*R'+(2-x)*R-2.

The recurrence gives f/h=R*(R+x)+x*(1-x)*R'. Write the roots of h as -a_j,
a_j>0. Because h is palindromic, roots occur in reciprocal pairs, with
possible unpaired -1. With t=-x,

    E/t=sum_j (a_j+1)*(t^2+2*t-a_j)/(a_j-t)^2.

A reciprocal pair a,1/a contributes

    (a+1)^2 * [a*(t-1)^2*(t^2+2*t-1)+2*t*(a-1)^2]
      /[(a-t)^2*(a*t-1)^2].

For t>1 this is strictly positive. An unpaired a=1 contributes
2*(t^2+2*t-1)/(1-t)^2>0. Since m>=2 makes h nonconstant, E(x)>0 for
x<-1 outside h's roots. The displayed identity was independently checked
symbolically in the retained `verify_sturm_identities.py` run.

Set alpha=b/2+1 and Q=g+alpha*h. At a Q root q, R(q)=-alpha, and direct
substitution gives the exact formula

    P_n(q)/h(q)=c-(alpha^2+2)-E(q).

Because alpha^2+2=b^2/4+b+3, this is strictly negative at every Q root
q<-1 in the proposed region. No assertion is needed about Q roots to the
right of -1. Q and h strictly interlace by the usual consecutive Eulerian
interlacing; all Q roots are simple and negative.

## 3. Hybrid testpoint count and signs

Assume n>=4 and b>0, and put m=n-2. Select all Q roots below -1 and all
h roots in (-1,0). When m is even, also select -1.

### m=2*l+1 odd

h has l roots on each side of -1. Q has l+1 roots below -1 and l above it.
To check its extra left root, note that R(-1)=0, R'>0 between h poles, and
the central Q root solves R=-alpha<0; therefore it lies below -1.

There are (l+1)+l=m selected points. At the last selected Q root, P has
sign (-1)^(l+1). At the first selected h root on the right, P has sign
(-1)^l: indeed P(r)=g(r)*(f(r)/g(r)+b), whose parenthesis is positive.
The signs alternate within each list because h interlaces Q and because
g(r)=r*(1-r)*h'(r) at h roots. Thus they alternate across the joining gap.

### m=2*l even

h has l-1 roots on each side of -1 and a simple root at -1. Q has l roots
on each side of -1 by strict interlacing. There are l+1+(l-1)=m selected
points, counting the additional point -1.

The signs at the final left Q point, at -1, and at the first right h point
are respectively

    (-1)^(l+1), (-1)^l, (-1)^(l-1).

Here P(-1)=b*g(-1), because f and h vanish there. This is nonzero because
b>0. When l=1 (n=4), there is no right h point; the last selected point
is -1 and has negative sign, as required.

### Exterior signs

In either parity, the first selected Q point lies to the left of every h
root. Its P sign is (-1)^m, opposite the sign (-1)^(m+1) of monic P as
x tends to -infinity. The final selected point has negative P sign, opposite
P(0)=1+b+c>0. Thus the m selected points together with the two exterior
ends produce m+1 disjoint intervals, each containing a real root. Since
deg P=m+1, these are all roots, and they are distinct and negative.

## 4. Boundaries and quantifiers

* The c boundary is included directly: E(q)>0 remains strict at every
  selected Q point even when c=alpha^2+2.
* For b=0 and any fixed 0<=c<=3, take positive b_j tending to zero. The
  same c remains admissible, and all P_n(x;b_j,c) are real-rooted. Their
  monic coefficient limit P_n(x;0,c) is real-rooted. Fixed degree and bounded
  coefficients bound all roots, so a convergent subsequence of the ordered
  real roots gives a real factorization of the limit. Repeated roots are
  permitted by the target.
* n=3 is handled directly by its quadratic discriminant, including the
  repeated root on the sharp boundary.
* The necessity uses that same n=3 discriminant. It does not substitute for
  any part of the all-degree sufficiency argument.
* No numerical screening or finite-degree Sturm certificate is used in
  this full proof. Earlier finite-degree H experiments and partial regions
  are now historical research artifacts.

## 5. Review conclusion

The central repair is valid: the argument uses Q testpoints only to the left
of -1, where its sign lemma is proved, and switches to h testpoints on the
right, where the independently proved positive-residue lemma applies. It
never assumes that all summands are compatible, and it never uses the
unproved global E implication from the earlier approach. The resulting
sign count proves the original full quantifiers.
