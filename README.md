# Real-Rootedness of Three Consecutive Eulerian Polynomials

**By Chris Ozols, with AI-assisted proof development and formalization.**

> **Lean-checked proof; no novelty claim.** The sharp criterion proved here extends the
> sufficient region of Athanasiadis's Example 3.3. The searches made for this project did not
> find it stated or proved elsewhere, but they were brief, and one related preprint could not
> be retrieved for independent checking. I do not claim novelty, first discovery, or priority. This repository makes
> the argument and its Lean checks available to anyone investigating the question. See the
> [prior-art review](PRIOR_ART.md).

Let $A_n(x)$ be the Eulerian polynomials, $A_0=1$ and

```math
A_{n+1}(x)=(1+nx)A_n(x)+x(1-x)A_n'(x),
```

so $A_1=1$, $A_2=1+x$, $A_3=1+4x+x^2$ and $A_4=1+11x+11x^2+x^3$. This repository proves, in
**Lean 4.35.0 with Mathlib v4.35.0**, that for all fixed real $b,c\ge 0$, the polynomials

```math
P_n(x)=A_n(x)+b\,A_{n-1}(x)+c\,A_{n-2}(x)
```

have only real roots for every $n\ge 3$ **if and only if**

```math
c\le \frac{b^2}{4}+b+3 .
```

Repeated roots are allowed, and the boundary is included. Necessity comes from $n=3$ alone:
there the polynomial is $x^2+(b+4)x+1+b+c$, with discriminant $b^2+4b+12-4c$. Inside the
region every polynomial of the family is monic of degree $n-1$ with $n-1$ real roots counted
with multiplicity.

> **Trust model.** Every audited theorem depends only on Lean's standard axioms
> `propext`, `Classical.choice` and `Quot.sound`. There is no `native_decide`, no
> `sorry`, and no project-specific axiom, so the proofs are checked by the Lean kernel,
> including every Mathlib lemma they use. See [Trust model](#trust-model).

[Readable proof](PROOF.md) · [Main Lean theorem](EulerianRegion/MainTheorem.lean) ·
[Exact-statement check](Verification.lean) ·
[Verification report](VERIFICATION_REPORT.md) · [Provenance](PROVENANCE.md) ·
[Prior art](PRIOR_ART.md) · [Citation](CITATION.cff)

## The question and what is proved

C. A. Athanasiadis, *On the real-rootedness of the Eulerian transformation*
([arXiv:2302.00754v5](https://arxiv.org/abs/2302.00754v5), J. London Math. Soc.,
DOI [10.1112/jlms.70083](https://doi.org/10.1112/jlms.70083)), Example 3.3, shows that
$aA_n+bA_{n-1}+cA_{n-2}$ is real-rooted whenever $a\ge b-c\ge c\ge 0$. With $a=1$ this is the
triangle $1\ge b-c\ge c\ge 0$. This repository determines the exact set of nonnegative
$(b,c)$ for which the whole family $n\ge3$ is real-rooted: the region under the parabola
$c=b^2/4+b+3$, which contains that triangle.

| Statement | Status | Lean declaration |
| --- | --- | --- |
| For $b,c\ge0$: real-rooted for every $n\ge3$ $\iff$ $c\le b^2/4+b+3$ | Formalized | `EulerianRegion.eulerian_three_term_realRooted_iff` |
| Sufficiency for each $n\ge3$ inside the region | Formalized | `EulerianRegion.combination_splits` |
| Inside the region: monic, degree $n-1$, $n-1$ real roots with multiplicity | Formalized | `EulerianThreeTermVerification.real_rooted_strong` |
| At $n=3$, for all real $b,c$: real-rooted $\iff$ $c\le b^2/4+b+3$; on the boundary, $(x+b/2+2)^2$ | Formalized | `combination_three_splits_iff`, `combination_three_boundary` |
| All roots negative; simple roots for $n\ge4$ (outside $b=0$ with $n$ even) | Informal proof only ([original/](original/README.md)) | — |
| The exact real-rooted region for a single degree $n\ge4$ | Not addressed | — |

"Only real roots" is Mathlib's `Polynomial.Splits` over $\mathbb R$: the polynomial is a
product of a constant and monic linear factors. [Verification.lean](Verification.lean)
restates the results for **any** sequence satisfying the recurrence above, using only Mathlib
notions, and proves that such a sequence exists, so its hypothesis is not vacuous.

The criterion is uniform in $n$, not a description of each degree separately. For a single
$n\ge4$ the real-rooted region is larger; for example
$A_4+cA_2=(x+1)(x^2+10x+1+c)$ is real-rooted for all $c\le24$.

## Proof overview

1. **Cayley coordinates.** Put $x=(z-1)/(z+1)$ and $C_j(z)=(1+z)^{j-1}A_j(x)$. Then
   $C_{j+1}=\bigl((z^2-1)C_j\bigr)'$, each $C_j$ has $j-1$ simple roots in $(-1,1)$, and
   reciprocity of $A_j$ becomes the parity $C_j(-z)=(-1)^{j-1}C_j(z)$.
2. **Positive residues.** With $F_n=(z^2-1)C_{n-2}$, the ratio $C_n/F_n$ is a positive
   constant plus a sum of terms $\lambda_j/(z^2-a_j)$ with $\lambda_j>0$, by induction on
   $n$. This fixes the sign of the target at the positive roots of $f=C_{n-2}$.
3. **A logarithmic-derivative inequality.** On $(-1,0)$, for $f$ with simple roots symmetric
   about $0$, $(1-z^2)\sum_r(z-r)^{-2}-2\sum_r(z-r)^{-1}>0$. A polynomial identity then fixes
   the sign of the target at the negative roots of the separator
   $q=C_{n-1}+(b/2+1)(z+1)f$, for every $c\le b^2/4+b+3$.
4. **Counting sign changes.** The negative roots of $q$, the positive roots of $f$ (and $0$
   when $n$ is even) give exactly enough alternating signs to place every root of the
   transformed polynomial in $(-1,1)$. For $b=0$ and $n$ even the transformed polynomial
   vanishes at $0$; it is divided by $z$ and the same count is applied to the quotient.
5. **Back to $x$.** The roots map back through the Cayley transform, with multiplicities and
   without a degree drop.

[PROOF.md](PROOF.md) gives the full argument and the Lean file for each step.

## Trust model

`./verify.sh` prints the type and the axioms of 23 declarations: the restatements in
[Verification.lean](Verification.lean), the project's main theorems and the decisive
lemmas of each proof step. Each must depend on exactly `propext`, `Classical.choice` and
`Quot.sound`. Lean's `#print axioms` reports the full transitive closure, so this covers every
Mathlib lemma used; any `sorryAx`, `Lean.ofReduceBool` or added axiom would fail the audit.
[scripts/audit.py](scripts/audit.py) also rejects `sorry`, `admit`, axiom declarations,
`native_decide`, `unsafe`, `implemented_by`, `extern`, instances, notation, macros and
attributes other than `@[simp]` and `@[expose]` in this project's Lean files, and the build
must finish with no warnings. With `VERIFY_LEANCHECKER=1`, the proofs are also replayed by
the toolchain's `leanchecker`; the recorded run did this.

The project depends only on Mathlib. Its definitions are `EulerianRegion.A` (the recurrence
above) and `EulerianRegion.combination n b c = A n + C b * A (n-1) + C c * A (n-2)`;
[Verification.lean](Verification.lean) shows that neither is needed to state the result.

## Reproduce the verification

On Linux x86_64 with Bash, Git, Python 3, curl, tar, zstd and coreutils:

```sh
git clone https://github.com/cozuya/eulerian-three-term-real-rootedness.git
cd eulerian-three-term-real-rootedness
bash scripts/install-lean.sh
export PATH="$PWD/.tools/lean-4.35.0-linux/bin:$PATH"
bash scripts/fetch-deps.sh        # locked Mathlib, prebuilt Mathlib
./verify.sh                       # rebuild + statement/axiom audit
python3 scripts/check-package.py
```

`VERIFY_LEANCHECKER=1 ./verify.sh` adds the independent kernel replay. See
[REPRODUCE.md](REPRODUCE.md) for details, timings and resource needs.

| Component | Pinned version or revision |
| --- | --- |
| Lean | 4.35.0, `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` |
| Lake | `5.0.0-src+eb6cafb` |
| Mathlib | v4.35.0, `56a005855ea17e0b0958f73ec801ae140b0a1679` |

The committed [local evidence](evidence/verification.json) identifies its sources by hash.

## Provenance

Chris Ozols directed the work. The informal proof ([original/](original/README.md)) was
developed with AI assistants and independently audited by Anthropic's Claude. The Lean
formalization was written by Claude; its final verification step and report were completed
by OpenAI's Codex. This package was assembled by Claude. [PROVENANCE.md](PROVENANCE.md) gives
dates, sources and what each record does and does not establish.

Formal verification establishes the stated results relative to Lean and its kernel. It does
not establish historical priority. [PRIOR_ART.md](PRIOR_ART.md) records the literature checks
and their limits.

## Discovery and novelty-checking summary

**Search identifiers:** Eulerian polynomials; linear combinations of consecutive Eulerian
polynomials; $A_n+bA_{n-1}+cA_{n-2}$; real-rootedness; three-term Eulerian combination;
Athanasiadis Example 3.3; Eulerian transformation; Cayley transform; interlacing; Lean.

**Exact scope:** for real $b,c\ge0$, real-rootedness of $A_n+bA_{n-1}+cA_{n-2}$ for every
$n\ge3$ holds exactly when $c\le b^2/4+b+3$. Per-degree regions are not determined. The
[Lean statements](Verification.lean), [verification report](VERIFICATION_REPORT.md) and
[prior-art review](PRIOR_ART.md) enable a direct novelty check.

## License

Copyright 2026 Chris Ozols. The Lean proofs, scripts, and documentation in this
repository are licensed under the [Apache License, Version 2.0](LICENSE).
Third-party dependencies, including Mathlib, retain their respective licenses. The preserved
informal proof material in [original/](original/README.md) is included under the same
license.
