# Proof

This is a readable account of the argument formalized in this repository. It follows the
informal proof in [original/coefficient-region/REPORT.md](original/coefficient-region/REPORT.md)
(§§1–6), with one change in the last case. Each section names the Lean file where the step is
proved.

## Statement

Let $A_0=1$ and $A_{n+1}=(1+nx)A_n+x(1-x)A_n'$, and for real $b,c$ and $n\ge3$ put

```math
P_n(x)=A_n(x)+b\,A_{n-1}(x)+c\,A_{n-2}(x).
```

**Theorem.** For real $b,c\ge0$, every $P_n$ with $n\ge3$ has only real roots if and only if
$c\le b^2/4+b+3$.

In Lean, $A_n$ is `EulerianRegion.A` and $P_n$ is `EulerianRegion.combination n b c`
([Definitions.lean](EulerianRegion/Definitions.lean)). The recurrence at $n=0$ gives $A_1=1$,
so the definition agrees with the usual convention $A_0=A_1=1$. The description of $A_n$ as
the descent polynomial of $S_n$ is not formalized; the recurrence is the definition.

## 1. Degree three: necessity and the boundary

[Sanity.lean](EulerianRegion/Sanity.lean). Since $A_1=1$, $A_2=1+x$, $A_3=1+4x+x^2$,

```math
P_3(x)=x^2+(b+4)x+1+b+c,
```

with discriminant $b^2+4b+12-4c$. So $P_3$ is real-rooted exactly when $c\le b^2/4+b+3$, for
all real $b,c$ (`combination_three_splits_iff`), and on the boundary
$P_3=(x+b/2+2)^2$ (`combination_three_boundary`). This gives necessity and the case $n=3$ of
sufficiency. The rest of the proof is sufficiency for $n\ge4$.

The recurrence also shows that $A_{j+1}$ is monic of degree $j$ with positive coefficients and
constant term $1$, so $P_n$ is monic of degree $n-1$ (`combination_monic`,
`combination_natDegree`).

## 2. Cayley coordinates

[Cayley.lean](EulerianRegion/Cayley.lean). Put $x=(z-1)/(z+1)$, which maps $(-1,1)$
increasingly onto $(-\infty,0)$, and

```math
C_j(z)=(1+z)^{j-1}A_j\Bigl(\frac{z-1}{z+1}\Bigr).
```

Substituting into the recurrence gives

```math
C_{j+1}=T\,C_j,\qquad T f=\bigl((z^2-1)f\bigr)'=(z^2-1)f'+2zf .
```

Lean defines $C_j$ by $C_1=1$, $C_{j+1}=TC_j$ (`Cay`), and proves that this agrees with the
Cayley transform of $A_j$ for every index (`Cay_succ_eq_homog`, `eval_Cay_succ`). From the
recurrence: $C_j$ has degree $j-1$ and leading coefficient $j!$, $C_j(1)=2^{j-1}$,
$C_j(-1)=(-2)^{j-1}$, and $C_j(-z)=(-1)^{j-1}C_j(z)$. A sign count at $-1$, the roots of $C_j$
and $1$ shows that $C_{j+1}$ has simple roots in $(-1,1)$ interlacing those of $C_j$
(`Cay_rootedIn`, `Cay_interlace`). The roots are symmetric about $0$, and $0$ is a root exactly
when $j$ is even.

Root counting throughout uses one tool ([RootCount.lean](EulerianRegion/RootCount.lean)):
if a polynomial with positive leading coefficient strictly alternates in sign on
$\deg+1$ increasing test points, then by the intermediate value theorem it has a root
between each consecutive pair, so it splits with simple roots (`SignPattern.splits`,
`SignPattern.nodup`).

## 3. Positive residues

[PartialFractions.lean](EulerianRegion/PartialFractions.lean),
[Residue.lean](EulerianRegion/Residue.lean).

**Lemma 3.1.** For $n\ge3$ let $F_n=(z^2-1)C_{n-2}$. Then, away from the poles,

```math
\frac{C_n(z)}{F_n(z)}=\rho_n+\sum_j\frac{\lambda_j}{z^2-a_j},\qquad
\rho_n>0,\quad \lambda_j>0,\quad 0<a_j\le1,
```

where the $a_j$ are the squares of the positive roots of $F_n$ (`positive_partial_fractions`).

The proof is by induction on $n$, starting from $C_3/F_3=6+4/(z^2-1)$. Partial fractions are
done with finite polynomial identities (Lagrange form), not complex residues. The residue at a
simple pole $s$ is $\kappa_s=C_n(s)/F_n'(s)$, and pairing $s$ with $-s$ turns
$\kappa_s/(z-s)-\kappa_s/(z+s)$ into $2s\kappa_s/(z^2-s^2)$. From $T$ one gets $F_n'=C_{n-1}$
and $F_{n+1}=(z^2-1)F_n'$, so the interior poles at level $n+1$ are the critical points
$\xi$ of $F_n$. At such a point:

- $F_n''(\xi)/F_n(\xi)=-\sum_s(\xi-s)^{-2}<0$, because $F_n$ has simple real roots;
- $C_{n+1}(\xi)/F_n(\xi)=2\xi\bigl(\rho_n+\sum_j\lambda_j(1-a_j)/(\xi^2-a_j)^2\bigr)$, by the
  induction hypothesis.

Together these give a positive residue at every positive interior pole. The endpoint pole
$z=1$ is direct, parity handles negative poles, and a pole at $0$ (present for one parity)
cancels. Since $F_n'=C_{n-1}$, the residue at $s$ is $C_n(s)/C_{n-1}(s)$, and Lean proves
the invariant $s\,C_n(s)\,C_{n-1}(s)>0$ for every pole $s\ne0$ of $F_n$ (`residue_pos`).

**Corollary 3.2.** If $r>0$ is a root of $f=C_{n-2}$, then $C_n(r)\,C_{n-1}(r)>0$
(`cor_3_2`).

## 4. A one-sided inequality on the negative half

[Central.lean](EulerianRegion/Central.lean).

**Lemma 4.1.** Let $f$ have simple roots in $(-1,1)$, symmetric about $0$, and at least one
root. For $-1<z<0$ with $f(z)\ne0$,

```math
(1-z^2)\sum_r\frac{1}{(z-r)^2}-2\sum_r\frac{1}{z-r}>0
```

(`lemma_4_1`). With $u=-z$, a pair of roots $\pm\sqrt a$ contributes
$2N(u,a)/(u^2-a)^2$, where

```math
N(u,a)=a(1-u)^3(1+u)+(1-a)u^2(1+2u-u^2)>0,
```

and a root at $0$ contributes $(1+2u-u^2)/u^2>0$. The inequality is used only for $z<0$.

## 5. The identity and the signs at the test points

[Central.lean](EulerianRegion/Central.lean), [Separator.lean](EulerianRegion/Separator.lean),
[Sufficiency.lean](EulerianRegion/Sufficiency.lean).

Fix $n\ge4$, put $m=n-2$, $f=C_m$, $g=C_{m+1}=Tf$, $h=C_{m+2}=Tg$ and $\alpha=b/2+1\ge1$, so
the parameter bound reads $c\le\alpha^2+2$. The Cayley transform of $P_n$ is

```math
\hat P(z)=h(z)+b(z+1)g(z)+c(z+1)^2f(z),
```

of degree $n-1$ with positive leading coefficient, $\hat P(1)>0$ and
$\hat P(-1)=(-2)^{n-1}$ (`Phat`, `Phat_degree`, `homog_combination`). The separator

```math
q=g+\alpha(z+1)f
```

satisfies $q(r)=(r^2-1)f'(r)$ at the roots of $f$, $q(1)>0$ and $q(-1)=-2f(-1)$. So $q$ has a
simple root in each gap of $f$, including the two end gaps, and no root in common with $f$
(`sep_signPattern`).

**The central identity** (`central_identity`, a polynomial identity for arbitrary $f$, proved
by `ring`):

```math
\hat P f=q^2+(z+1)^2(c-\alpha^2-2)f^2-(1-z^2)\bigl[(1-z^2)(f'^2-ff'')-2ff'\bigr].
```

At a negative root $s$ of $q$ the first term vanishes, the second is $\le0$, and the bracket
equals $f(s)^2$ times the positive quantity of Lemma 4.1. Hence
$\hat P(s)f(s)<0$, strictly, including on the boundary $c=\alpha^2+2$
(`sign_at_neg_separator_root`).

At a positive root $r$ of $f$, $\hat P(r)=h(r)+b(r+1)g(r)$. By Corollary 3.2 and $b\ge0$ this
has the sign of $g(r)=(r^2-1)f'(r)$, that is, $-\mathrm{sgn}f'(r)$.

## 6. The root count

[Separator.lean](EulerianRegion/Separator.lean),
[Sufficiency.lean](EulerianRegion/Sufficiency.lean),
[BoundaryZero.lean](EulerianRegion/BoundaryZero.lean).

The test points are $-1$, the negative roots of $q$, the nonnegative roots of $f$, and $1$
(`hybridSet`). For $n$ odd, $f$ has no root at $0$ and the root of $q$ in the central gap is
negative, because $q(0)=\alpha f(0)$. For $n$ even, $f(0)=0$ and $0$ is a test point. In both
cases there are exactly $\deg\hat P+1=n$ test points (`hybridSet_counts`).

- **$n$ odd, or $n$ even and $b>0$.** The signs of §5 alternate along the negative roots of
  $q$ (since $f$ interlaces $q$) and along the positive roots of $f$, and they also alternate
  across the junction, at $0$ (where $\hat P(0)=b\,g(0)$ for $n$ even) and at the endpoints.
  So $\hat P$ has a sign pattern on $\deg\hat P+1$ points and splits with simple roots in
  $(-1,1)$ (`Phat_signPattern`).
- **$n$ even and $b=0$** (so $0\le c\le3$). Now $\hat P(0)=0$ by parity and the previous count
  breaks. The informal proof takes a limit $b\to0^+$ instead. The Lean proof writes
  $\hat P=zR$, removes $0$ from the test points, and checks that $R$ alternates in sign on the
  remaining $n-1=\deg R+1$ points: at $t\ne0$, $R(t)=\hat P(t)/t$, and for $t<0$ the sign flip
  of $1/t$ is compensated by one fewer test point above $t$ (`Rzero_signPattern`). So $R$, and
  hence $\hat P$, splits. Only splitting is concluded here; $\hat P$ may have a double root at
  $z=0$. A similar limit-free count appears in the auditor's remark at the end of §6 of the
  independent audit ([original/audit/AUDIT.md](original/audit/AUDIT.md)).

**Back to $x$** (`splits_of_homog`). Since $\hat P$ has degree $n-1$ and
$\hat P(-1)\ne0$, its factorization over the roots $z_i\in(-1,1)$ gives

```math
P_n(x)=\frac{\mathrm{lc}\hat P}{2^{\,n-1}}\prod_i\bigl((1+z_i)x+(1-z_i)\bigr),
```

with multiplicities, so $P_n$ splits. This completes sufficiency for $n\ge4$
(`combination_splits_of_branch`, `combination_splits_b_zero_even`), and with §1 for all
$n\ge3$ (`combination_splits`, `eulerian_three_term_realRooted_iff` in
[MainTheorem.lean](EulerianRegion/MainTheorem.lean)).

## Relation to the informal proof

The Lean proof follows the informal argument step by step. It differs in three places:

- partial fractions and residues are finite polynomial identities, with the zero pole
  handled by the factor $s$ in the paired sums;
- the case $b=0$, $n$ even uses the factor-$z$ count above instead of a limit, so no
  continuity of roots is needed;
- it concludes only splitting. Simple roots, which the informal proof also gives for
  $n\ge4$ outside the case $b=0$, $n$ even, are not stated as theorems.

The independent audit in [original/audit/](original/audit/README.md) reconstructs every
decisive step of the informal proof before the formalization; the Lean files cite its
sections.
