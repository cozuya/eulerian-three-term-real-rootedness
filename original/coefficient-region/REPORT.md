# A sharp uniform coefficient region for three consecutive Eulerian polynomials

**Outcome: PROVED.** The proposed criterion holds, including its boundary.

## 1. Exact result

Use the convention

\[
A_n(x)=\sum_{\pi\in S_n}x^{\operatorname{des}(\pi)},\qquad A_0=A_1=1,
\]

and the recurrence

\[
A_{n+1}(x)=(1+nx)A_n(x)+x(1-x)A_n'(x),\qquad n\ge1.
\]

**Theorem.** For every fixed pair of real numbers \(b,c\ge0\), the following are equivalent:

1. \(A_n(x)+bA_{n-1}(x)+cA_{n-2}(x)\) has only real roots for every integer \(n\ge3\).
2. \(c\le b^2/4+b+3\).

Repeated roots are permitted. The proof is uniform in the real parameters and in the degree. It does not rely on a finite computational screen.

### Necessity and the boundary

At \(n=3\),

\[
P_3(x)=x^2+(b+4)x+(1+b+c),
\]

whose discriminant is \(b^2+4b+12-4c\). Thus condition 1 implies condition 2. On the boundary,

\[
c=\frac{b^2}{4}+b+3,
\qquad
P_3(x)=\left(x+\frac b2+2\right)^2.
\]

The substantive part is sufficiency in every degree; that proof follows.

## 2. Eulerian preliminaries

The recurrence gives positive coefficients, constant coefficient 1, and a monic polynomial of degree \(j-1\) for every \(j\ge1\). More explicitly, if \(e_{j,k}=[x^k]A_j(x)\), then

\[
e_{j+1,k}=(k+1)e_{j,k}+(j-k+1)e_{j,k-1},
\]

with coefficients outside the degree range interpreted as zero. This also preserves the symmetry \(e_{j,k}=e_{j,j-1-k}\), starting from \(A_1=1\). Therefore

\[
A_j(x)=x^{j-1}A_j(1/x).
\tag{2.1}
\]

The same symmetry follows combinatorially by reversing a permutation.

The recurrence proves simple negative roots and consecutive strict interlacing by induction. The base case is \(A_2=1+x\). If the roots of the monic polynomial \(A_j\) are

\[
r_1<\cdots<r_{j-1}<0,
\]

then

\[
A_{j+1}(r_i)=r_i(1-r_i)A_j'(r_i).
\]

The multiplier \(r_i(1-r_i)\) is negative. These values alternate in sign; the signs at \(-\infty\) and at 0 provide the two outer sign changes. Consequently, \(A_{j+1}\) has one root in each of

\[
(-\infty,r_1),\ (r_1,r_2),\ldots,\ (r_{j-2},r_{j-1}),\ (r_{j-1},0).
\]

These \(j\) roots exhaust its degree and are simple. Thus all the asserted root and interlacing facts follow from the recurrence.

### Cayley coordinates

Set

\[
x=\frac{z-1}{z+1},\qquad
C_j(z)=(1+z)^{j-1}A_j\!\left(\frac{z-1}{z+1}\right),\qquad j\ge1.
\tag{2.2}
\]

The map sends \((-1,1)\) increasingly and bijectively onto \((-\infty,0)\). Therefore \(C_j\) has \(j-1\) simple roots in \((-1,1)\). Reciprocity gives

\[
C_j(-z)=(-1)^{j-1}C_j(z).
\tag{2.3}
\]

In particular, its roots are symmetric about zero. Its zero at zero occurs exactly when \(j\) is even, and is simple.

Evaluating the original recurrence at 1 gives \(A_j(1)=j!\). Hence \(C_j\) has degree \(j-1\), positive leading coefficient \(j!\), and endpoint values

\[
C_j(1)=2^{j-1},\qquad C_j(-1)=(-2)^{j-1}.
\tag{2.4}
\]

A direct substitution in the recurrence gives the particularly useful relation

\[
C_{j+1}(z)=\bigl((z^2-1)C_j(z)\bigr)'
=(z^2-1)C_j'(z)+2zC_j(z).
\tag{2.5}
\]

Write \(T=(z^2-1)D+2z\), so \(C_{j+1}=TC_j\).

## 3. Positive residues for a two-step Eulerian ratio

The following lemma supplies the Eulerian-specific information needed on the positive half of the Cayley interval. Its zero-order consequence is the two-step interlacing result also appearing in Ma's Corollary 1 [2]. A complete specialized proof is given here.

**Lemma 3.1.** For \(n\ge3\), define

\[
F_n(z)=(z^2-1)C_{n-2}(z).
\]

After canceling the common simple zero at zero when the parity is odd, the ratio has a partial-fraction expansion

\[
\frac{C_n(z)}{F_n(z)}
=\rho_n+\sum_j\frac{\lambda_j}{z^2-a_j},
\qquad
\rho_n>0,\quad\lambda_j>0,\quad0<a_j\le1.
\tag{3.1}
\]

The numbers \(a_j\) are exactly the squares of the positive roots of \(F_n\).

**Proof.** All roots of \(F_n\) are simple, lie in \([-1,1]\), and include both endpoints. Its degree and parity agree with those of \(C_n\). Equation (2.5) gives

\[
F_n'=C_{n-1},\qquad
F_{n+1}=(z^2-1)F_n',\qquad
C_{n+1}=(z^2-1)C_n'+2zC_n.
\tag{3.2}
\]

For \(n=3\),

\[
F_3=z^2-1,\qquad C_3=6z^2-2,
\qquad \frac{C_3}{F_3}=6+\frac4{z^2-1}.
\]

Suppose (3.1) holds at \(n\), and put \(R=C_n/F_n\). Let \(\xi\in(0,1)\) be a zero of \(F_n'\). The simple real roots of \(F_n\) imply \(F_n(\xi)\ne0\), and logarithmic differentiation at this critical point gives

\[
\frac{F_n''(\xi)}{F_n(\xi)}
=-\sum_{s:F_n(s)=0}\frac1{(\xi-s)^2}<0.
\tag{3.3}
\]

Thus

\[
\frac{F_{n+1}'(\xi)}{F_n(\xi)}
=(\xi^2-1)\frac{F_n''(\xi)}{F_n(\xi)}>0.
\tag{3.4}
\]

Because \(F_n'(\xi)=0\), the numerator recurrence and the inductive expansion yield

\[
\begin{aligned}
\frac{C_{n+1}(\xi)}{F_n(\xi)}
&=(\xi^2-1)R'(\xi)+2\xi R(\xi)\\
&=2\xi\left(\rho_n+
\sum_j\frac{\lambda_j(1-a_j)}{(\xi^2-a_j)^2}\right)>0.
\end{aligned}
\tag{3.5}
\]

The strict inequality follows from \(\rho_n>0\); all summands are nonnegative. Dividing (3.5) by (3.4) shows that the ordinary residue

\[
\frac{C_{n+1}(\xi)}{F_{n+1}'(\xi)}
\]

is positive. The coefficient of \((z^2-\xi^2)^{-1}\) is \(2\xi\) times that ordinary residue and is therefore positive as well.

The endpoint \(\xi=1\) is equally direct:

\[
C_{n+1}(1)=2C_n(1)>0,\qquad
F_{n+1}'(1)=2F_n'(1)>0.
\]

Here \(F_n'(1)>0\) because 1 is the largest simple root of a polynomial with positive leading coefficient. Hence the endpoint residue is positive.

The positive zeros of \(F_{n+1}\) are precisely this endpoint and the positive critical points already considered. Parity handles the corresponding negative poles. If zero is present, it is simple in both \(C_{n+1}\) and \(F_{n+1}\), so it cancels. This accounts for every pole. The ratio is even, and its numerator and denominator have the same degree with positive leading coefficients; consequently its polynomial part is a positive constant. The required expansion follows at \(n+1\), completing the induction. \(\square\)

**Corollary 3.2.** If \(r>0\) is a root of \(C_{n-2}\), then

\[
\frac{C_n(r)}{C_{n-1}(r)}>0.
\tag{3.6}
\]

Indeed, \(F_n'(r)=C_{n-1}(r)\), and the ordinary residue at \(r\) in (3.1) is positive. The denominator is nonzero because the roots of \(F_n\) are simple.

For completeness, (3.1), regarded as a rational function of \(t=z^2\), is strictly decreasing between its poles. Its numerator roots alternate with the poles, with the smallest squared numerator root positive by the already established real-rootedness of \(C_n\). This recovers the strict two-step root order on either side of zero, with the shared simple parity zero treated separately.

## 4. A logarithmic-derivative inequality on the negative half-interval

**Lemma 4.1.** Let \(f\) be a nonconstant polynomial with simple roots in \((-1,1)\), symmetric about zero. For \(-1<z<0\) away from its roots, set

\[
L(z)=\frac{f'(z)}{f(z)}=\sum_r\frac1{z-r},
\qquad
V(z)=\sum_r\frac1{(z-r)^2}.
\]

Then

\[
E(z):=(1-z^2)V(z)-2L(z)>0.
\tag{4.1}
\]

**Proof.** Write \(u=-z\in(0,1)\). A root at zero contributes

\[
\frac{1+2u-u^2}{u^2}>0.
\]

A pair of roots \(\pm\sqrt a\), with \(0<a<1\), contributes

\[
\frac{2N(u,a)}{(u^2-a)^2},
\]

where

\[
\begin{aligned}
N(u,a)
&=u^2(1+2u-u^2)+a(1-2u-u^2)\\
&=a(1-u)^3(1+u)
 +(1-a)u^2(1+2u-u^2)>0.
\end{aligned}
\tag{4.2}
\]

Every contribution is strictly positive. Summation proves the assertion. \(\square\)

This lemma is used only for negative \(z\). No two-sided extension is assumed.

## 5. The polynomial identity and the hybrid test points

Assume \(b,c\ge0\) and \(c\le b^2/4+b+3\). Fix \(n\ge4\), put \(m=n-2\), and write

\[
f=C_m,\qquad g=C_{m+1}=Tf,\qquad h=C_{m+2}=Tg,
\qquad \alpha=\frac b2+1.
\]

Thus \(\alpha\ge1\), \(b=2\alpha-2\), and the parameter bound is \(c\le\alpha^2+2\). The Cayley transform of the target polynomial is

\[
P(z)=h(z)+b(z+1)g(z)+c(z+1)^2f(z).
\tag{5.1}
\]

Its degree is \(m+1\), with positive leading coefficient. Also,

\[
\operatorname{sgn}P(-1)=(-1)^{m+1},\qquad P(1)>0.
\tag{5.2}
\]

Define the auxiliary polynomial

\[
q(z)=g(z)+\alpha(z+1)f(z).
\tag{5.3}
\]

It has \(m\) simple roots in \((-1,1)\), with one in every gap determined by the roots of \(f\), including the endpoint gaps. To see this directly, at a root \(r\) of \(f\),

\[
q(r)=(r^2-1)f'(r),
\]

while \(q(1)>0\) and \(q(-1)=-2f(-1)\). These signs force exactly the stated roots, exhausting its degree. In particular, \(f\) and \(q\) have no common root.

### The decisive identity

The exact polynomial identity

\[
\begin{aligned}
Pf={}&q^2+(z+1)^2(c-\alpha^2-2)f^2\\
&-(1-z^2)\left[(1-z^2)(f'^2-ff'')-2ff'\right]
\end{aligned}
\tag{5.4}
\]

follows by substitution and expansion. The expressions needed to check it are

\[
g=(z^2-1)f'+2zf
\]

and

\[
h=(z^2-1)^2f''+6z(z^2-1)f'+(6z^2-2)f.
\]

At a negative root \(s\) of \(q\), the first term on the right of (5.4) vanishes. The second is nonpositive. The bracket in the last term equals \(f(s)^2E(s)>0\) by Lemma 4.1; \(f\) is nonconstant because \(n\ge4\). Hence

\[
\frac{P(s)}{f(s)}<0,
\qquad
\operatorname{sgn}P(s)=-\operatorname{sgn}f(s).
\tag{5.5}
\]

This sign is strict even on the parameter boundary.

### Positive roots use a different family of test points

If \(r>0\) is a root of \(f\), Corollary 3.2 gives \(h(r)/g(r)>0\). Therefore

\[
P(r)=h(r)+b(r+1)g(r)
\]

has the sign of \(g(r)\), since \(b\ge0\). As \(g(r)=(r^2-1)f'(r)\),

\[
\operatorname{sgn}P(r)=-\operatorname{sgn}f'(r).
\tag{5.6}
\]

We combine the negative roots of \(q\) with the positive roots of \(f\). When \(f\) is odd, zero supplies one additional test point. This choice is what permits the full coefficient bound.

## 6. Complete root count, with both parities

### Case I: \(n\) odd

Write \(\deg f=2p\), so \(m=2p+1\); here \(p\ge1\). The polynomial \(f\) has \(p\) negative and \(p\) positive roots. The polynomial \(q\) has \(p+1\) negative and \(p\) positive roots.

For the latter count, all gaps away from the central gap follow immediately from interlacing. In the central gap, \(q(0)=\alpha f(0)\), whose sign agrees with \(q\) at the smallest positive root of \(f\) and is opposite to its sign at the largest negative root of \(f\). Thus the unique central root of \(q\) lies to the left of zero.

Use, in increasing order, all \(p+1\) negative roots of \(q\), followed by all \(p\) positive roots of \(f\). There are exactly \(2p+1=m=\deg P-1\) test points.

At the smallest negative \(q\)-root, \(f>0\), so \(P<0\), opposite to \(P(-1)>0\). The signs along the negative \(q\)-roots alternate by (5.5), since \(f\) interlaces \(q\). At the largest negative \(q\)-root, \(f\) has sign \((-1)^p\), so \(P\) has sign \((-1)^{p+1}\).

At the first positive \(f\)-root, (5.6) gives sign \((-1)^p\). Thus the signs alternate across the junction too. They continue alternating along the positive \(f\)-roots; at the last one, \(P<0\), opposite to \(P(1)>0\).

The endpoints and these \(m\) test points therefore give a sign change in each of \(m+1=\deg P\) disjoint intervals. Every interval contains a root. These roots exhaust the degree, proving that all roots of \(P\) are real, simple, and in \((-1,1)\).

### Case II: \(n\) even and \(b>0\)

Write \(\deg f=2p+1\), so \(m=2p+2\), with \(p\ge0\). The roots of \(f\) comprise \(p\) negative roots, a simple root at zero, and \(p\) positive roots. Interlacing gives \(p+1\) negative and \(p+1\) positive roots of \(q\).

Use all \(p+1\) negative \(q\)-roots, then zero, then the \(p\) positive \(f\)-roots. Again there are exactly \(2p+2=m=\deg P-1\) test points.

At the smallest negative \(q\)-root, \(f<0\), so \(P>0\), opposite to \(P(-1)<0\). The signs alternate along these roots by (5.5). At the last negative \(q\)-root, \(f\) has sign \((-1)^{p+1}\), so \(P\) has sign \((-1)^p\).

Since \(f,h\) are odd and \(g\) is even,

\[
P(0)=bg(0)=-bf'(0),
\]

whose sign is \((-1)^{p+1}\). This supplies the next sign change. If \(p\ge1\), the first positive \(f\)-root has sign \((-1)^p\) for \(P\), by (5.6); the signs then alternate to the last positive \(f\)-root, where \(P<0\), followed by \(P(1)>0\).

If \(p=0\), there are no positive \(f\)-roots: \(P(0)<0\) and \(P(1)>0\) directly give the final sign change.

As in Case I, there are \(\deg P\) disjoint sign-change intervals. All roots of \(P\) are therefore real, simple, and in \((-1,1)\).

### Case III: \(n\) even and \(b=0\)

Here \(0\le c\le3\). Keep \(c\) fixed and take positive \(b_j\to0\). Each pair satisfies

\[
c\le3<b_j^2/4+b_j+3,
\]

so Case II applies. The corresponding original polynomials in \(x\) are monic of the same degree \(n-1\), are real-rooted, and converge coefficientwise to the required polynomial.

For clarity, fixed-degree monic real-rootedness is closed: bounded coefficients give a uniform bound on all roots; a subsequence of the ordered real root lists converges in \(\mathbb R^{n-1}\); the product of the limiting linear factors is the coefficientwise limiting polynomial. Thus its roots remain real, with multiplicities retained.

### Completion

The Cayley map takes the roots obtained in Cases I and II back to real negative roots of the original polynomial. Case III supplies the remaining parameters, and the direct quadratic calculation covers \(n=3\), including its repeated boundary root. This proves sufficiency for arbitrary real \(b,c\ge0\) throughout the stated region. Together with necessity, it proves the theorem. \(\square\)

## 7. Relation to the published starting point

Athanasiadis defines the Eulerian transformation by \(\mathcal A^\circ(x^j)=xA_j(x)\) for \(j\ge1\). Theorem 1.1 applies to the nonnegative cone spanned by \(x^{n-k}(1+x)^k\). In the present setting,

\[
\begin{aligned}
x^n+bx^{n-1}+cx^{n-2}
={}&(1-b+c)x^n\\
&+(b-2c)x^{n-1}(1+x)
+cx^{n-2}(1+x)^2.
\end{aligned}
\]

Nonnegative coefficients in this representation give exactly

\[
1\ge b-c\ge c\ge0.
\]

Thus Theorem 1.1 gives the real-rootedness assertion in Example 3.3, together with its stronger symmetric-decomposition conclusion [1]. The present theorem concerns real-rootedness alone and covers the larger sharp region.

The targeted literature check also found Ma's preprint [2]. Its Corollary 1 gives the related two-step Eulerian root order; Theorem 5 proves real-rootedness of the three-term combination for \(0\le c\le1\) and every real \(b\). Neither inspected statement resolves the sharp criterion proved here. Lemma 3.1 supplies the needed specialized argument directly, so the proof above is self-contained.

## 8. Verification and limits of the claim

| Verification layer | Completed work | What it establishes |
|---|---|---|
| Analytical proof | The complete argument in Sections 2–6 | Sufficiency for all real admissible parameters and all degrees, plus necessity and the boundary |
| Independent adversarial review | Two separate reviewer agents checked the residue induction, polynomial identity, parity counts, endpoint signs, and limiting case | Both reviewers found the completed proof sound; this is independent agent review, not external peer review |
| Exact symbolic computation | Polynomial identity (5.4), paired-root identity (4.2), residue-induction identity, Cayley recurrence and setup checks | The central displayed algebraic identities were independently expanded and verified exactly |
| Exact finite computation | 279 exact sign cases, 22 boundary cases, and 145 earlier screening cases; inputs, code and retained outputs accompany this report | Finite corroboration, including boundary and sign-pattern checks; these counts describe completed verification batches, not a claim of that many distinct parameter pairs |
| Numerical exploration | Diagnostic searches and exploratory root approximations are retained separately | Used to test approaches and expose auxiliary obstructions; no floating-point result is a proof dependency |
| Formal verification | No Lean or other proof-assistant formalization was produced | No formal-verification claim is made |

The finite screens are not used to extrapolate to arbitrary degree. Repeated roots are handled analytically at \(n=3\) and by the fixed-degree closure argument where needed. No degree drop is hidden: every original target polynomial is monic of degree \(n-1\), and the transformed polynomials used for sign counting have positive leading coefficients.

The main failed route tried to use the shifted polynomial \(q\) as an interlacer on both halves of the Cayley interval. The needed strengthened inequality is not valid in the corresponding generic class on the positive half. An exact auxiliary obstruction and exploratory notes are retained. The successful proof uses positive roots of \(f\) on that half instead, justified by Lemma 3.1; it does not assume the failed claim.

### Novelty status

The mathematical outcome is **proved in this attempt**. A brief targeted search and direct examination of the starting paper and the related Ma preprint found no existing resolution of this exact sharp criterion. This was not an exhaustive novelty audit, and novelty is **not certified**.

## References

1. Christos A. Athanasiadis, *On the real-rootedness of the Eulerian transformation*, arXiv:2302.00754v5, 18 February 2025. In particular, the definition of \(\mathcal A^\circ\), Theorem 1.1, and Example 3.3. [Primary HTML source](https://arxiv.org/html/2302.00754v5).
2. Shi-Mei Ma, *The Eulerian Combinations*, author-uploaded preprint, August 2026. In particular, Corollary 1 (two-step Eulerian interlacing) and Theorem 5 (a free middle coefficient for \(0\le c\le1\)). [Author-uploaded full text](https://www.researchgate.net/publication/413485066_THE_EULERIAN_COMBINATIONS).
