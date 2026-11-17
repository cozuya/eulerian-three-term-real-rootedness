# Candidate B: submitted full-bound reduction



Define, for each m>=1,

\[
\begin{aligned}
N_m(x)
&=-q(x)\bigl(G'(x)F(x)-G(x)F'(x)\bigr)
 +(2-x)G(x)F(x)-2F(x)^2\\
&=G(x)^2-F(x)H(x)+2F(x)G(x)-2F(x)^2.
\end{aligned}
\tag{5}
\]

A sufficient all-degree lemma for the original conjecture is

\[
\boxed{N_m(x)\ge0\quad\text{whenever }x<0,\ F(x)\ne0,
\ R(x)=G(x)/F(x)\le-1.}
\tag{6}
\]

To see sufficiency, put d=1+b/2, so d>=1 and the original bound becomes c<=d^2+2. Use the same separator Q_d=G+dF. At its roots,

\[
\frac{P_n}{F}=c-(d^2+2)-\frac{N_m}{F^2}\le0.
\tag{7}
\]

For c<d^2+2 this is strict, and the same sign argument proves real-rootedness. Equality follows by coefficientwise continuity of fixed-degree monic polynomials with all roots real: roots of a convergent monic sequence stay bounded, and a subsequence of their ordered real roots converges to a real factorization of the limit. Thus repeated roots at the original boundary cause no missing case. For m=1, N_1 is identically zero, matching the elementary quadratic condition.

No proof of (6) for arbitrary m was obtained. It is not permissible to call the original conjecture proved merely because this reduction is available.

### 5.1 Part of the lemma that is proved

The inequality in (6) holds without its R<=-1 restriction whenever x<=1-sqrt(2), purely from reciprocal negative roots. Write x=-t and the roots of F as -a, a>0. Expanding (5) by logarithmic derivatives gives

\[
\frac{N_m(-t)}{F(-t)^2}
=\sum_a\frac{t(a+1)(t^2+2t-a)}{(a-t)^2}.
\tag{8}
\]

Pair a and 1/a. Their contribution is

\[
\frac{t(a+1)^2a}{(a-t)^2(at-1)^2}
\left[t^4-4t^2+2(a+a^{-1})t-1\right].
\]

Since a+a^{-1}>=2, its bracket is at least

\[
t^4-4t^2+4t-1=(t-1)^2(t^2+2t-1),
\]

which is nonnegative for t>=sqrt(2)-1. An unpaired a=1 has nonnegative contribution in the same range. Poles are excluded throughout. Therefore the outstanding part of (6) is confined to 1-sqrt(2)<x<0.

### 5.2 Exact finite-degree certificates for the full proposed region

For each m=2,...,15, exact computation certified that:

1. N_m has degree 2m-1 and negative leading coefficient.
2. N_m is square-free, has a root at zero, and has exactly one strictly negative root alpha_m.
3. The largest root beta_m of Q_1=G+F is strictly less than alpha_m. Both roots have retained rational isolating intervals with a strict gap.

Since N_m is positive near -infinity and has no earlier negative root, it is positive for x<alpha_m. On the other hand, R(x)>-1 for beta_m<x<0, because beta_m is in the rightmost pole interval and R is strictly increasing there. Thus R<=-1 forces x<=beta_m<alpha_m, giving N_m>0 on the whole required set. Equation (7) now proves the full proposed region, with simple roots, at n=m+2=4,...,17. The n=3 case follows from its discriminant and may have a double root.

The certificates are in `eulerian_attempt/exact_reduction_checks.json`; the generation code is `eulerian_attempt/exact_reduction_checks.py`. A separate supplied checker is `counterexample_search/review_exact_reduction.py`.

These certify arbitrary real b,c at the listed degrees. They do not infer anything about the outstanding all-degree lemma.

