# Transformation approach: checked reductions and obstruction

This branch did not prove the full conjecture.

## Möbius differential reduction
Set y=(1+x)/(1-x), x=(y-1)/(y+1), and
B_n(y)=(1+y)^(n-1) A_n((y-1)/(y+1)), n>=1.
The recurrence gives B_(n+1)=((y^2-1)D+2y)B_n.
For F=B_(n-2), the transformed target is

L_(b,c)F=(y^2-1)^2 F'' +(y^2-1)((6+b)y+b)F'
 +[(6+2b+c)y^2+(2b+2c)y+c-2]F.

This operator is independent of n. However, it does not preserve
real-rootedness of arbitrary symmetric polynomials with roots in (-1,1).
For b=0,c=3,F=y^2-1/100, its output is
(2300 y^4+600 y^3-1509 y^2-6 y+199)/100,
which has exactly two real roots (SymPy exact count), not four.
Thus a generic interval-preserver argument does not work.

## Turán expression behind the candidate interlacer
Write m=n-2, f=A_m, g=A_(m+1), h=A_(m+2),
Q=g+alpha f with alpha=b/2+1.
The desired sign at roots of Q reduces to

H_m=g^2+2fg-2f^2-fh >=0.

Equivalently, with p=x(1-x),
H_m=p^2(f'^2-ff'')+x(1-x^2)ff'+(m-1)x f^2.
The full criterion would follow if H_m>=0 at every x<0 with
g/f<=-1 (excluding zeros of f). This is still unproved.

The inequality is not valid for arbitrary reciprocal, negative-rooted f
with the consecutive polynomials defined by the Eulerian recurrence.
For m=3 and f=x^2+(202/99)x+1, define g,h by the recurrence.
At the largest root r of Q=g+f, r is approximately -0.2921526813,
H_m(r) is approximately -0.1675109835.
The resulting h+3f has two nonreal roots. These floating-point values
are diagnostic only; the independent transformed quartic above has an
exact root-count certificate.

For the actual Eulerian f, exact experiments m=2,...,6 found that
K_m=H_m/x has only two distinct real roots, one negative near zero and
one positive. Proving the needed sign or root-location condition could
be useful, but these finite observations are not a proof.

## Source work
Read Athanasiadis, arXiv:2302.00754v5, directly at
https://arxiv.org/html/2302.00754v5.
The convention agrees. Theorem 1.1 concerns the nonnegative cone spanned
by x^(n-k)(1+x)^k, and Example 3.3 gives a>=b-c>=c>=0.
A search snippet for the Zhang–Kitaev stack-sortable paper mentioned an
unrestricted middle coefficient, but inspection of the primary paper
found no real-rootedness discussion. That snippet comes from a citing
paper (Ma, The Eulerian Combinations) identified separately by root; do
not attribute it to Zhang–Kitaev.

Other search lead, not invoked as a dependency:
Gao–Liu, arXiv:2610.04150, Hurwitz Stability of Generalized Turán Expressions
of Polynomial Sequences (2026). Abstract mentions weak Hurwitz stability
of strong Eulerian Turán expressions. HTML and PDF fetch failed in this
branch; no theorem from it was verified or applied.
