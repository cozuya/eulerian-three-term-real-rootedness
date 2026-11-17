# Prior art

## Starting point

C. A. Athanasiadis, *On the real-rootedness of the Eulerian transformation*,
[arXiv:2302.00754v5](https://arxiv.org/abs/2302.00754v5) (February 18, 2025), published in
J. London Math. Soc., DOI [10.1112/jlms.70083](https://doi.org/10.1112/jlms.70083).
Theorem 1.1 shows that the Eulerian transformation maps nonnegative combinations of
$x^{n-k}(1+x)^k$ to real-rooted polynomials. Example 3.3 applies it to three consecutive
Eulerian polynomials: $aA_n+bA_{n-1}+cA_{n-2}$ is real-rooted whenever
$a\ge b-c\ge c\ge0$. With $a=1$ this is the triangle $1\ge b-c\ge c\ge0$, which is
strictly smaller than the region $c\le b^2/4+b+3$ proved here. The paper uses the same
convention $A_0=A_1=1$, $A_2=1+x$, $A_3=1+4x+x^2$. The independent audit checked this convention
and the statement of Example 3.3 against the arXiv HTML version on November 14, 2026
([original/audit/AUDIT.md](original/audit/AUDIT.md), §7).

The informal report ([original/coefficient-region/REPORT.md](original/coefficient-region/REPORT.md),
§7) explains the triangle: $x^n+bx^{n-1}+cx^{n-2}$ lies in the cone of Theorem 1.1 exactly
when $1\ge b-c\ge c\ge0$. Theorem 1.1 also gives a symmetric-decomposition conclusion, which is
not addressed here.

## Origin of the criterion

The sharp criterion $c\le b^2/4+b+3$ was posed as a conjecture before the proof in this
repository, with Example 3.3 as the stated starting point. It was supported by exploratory
exact computations for $n\le20$; that exploratory record is not included here. The
necessary direction is elementary (the discriminant at $n=3$); the open question was
sufficiency in every degree.

## Related work

- **Ma, *The Eulerian Combinations*.** S.-M. Ma, author-posted preprint (August 2026),
  [ResearchGate](https://www.researchgate.net/publication/413485066_THE_EULERIAN_COMBINATIONS).
  According to the informal report, which states that its full text was read, Corollary 1
  gives a two-step interlacing of Eulerian polynomials, and Theorem 5 proves real-rootedness
  of the three-term combination for $0\le c\le1$ and every real $b$. Neither resolves the sharp
  criterion. The informal proof proves the two-step fact it needs (Lemma 3.1) directly.
  **This description was not independently confirmed:** the audit could not retrieve the
  preprint, and a search on November 16, 2026 did not locate it either.
- **Turán-type expressions.** L. L. Liu and X. Yan, *Zeros distribution of the reverse strong
  Turán expressions of polynomials sequences*, Adv. in Appl. Math., DOI
  [10.1016/j.aam.2022.102426](https://doi.org/10.1016/j.aam.2022.102426), and Gao–Liu,
  *Hurwitz stability of generalized Turán expressions of polynomial sequences*,
  [arXiv:2610.04150](https://arxiv.org/abs/2610.04150), were encountered during the informal
  search. No theorem from either is used, and neither was identified as covering this
  statement; only the abstract of the second was retrieved.

## Proof ingredients used

The proof uses standard tools: the Cayley substitution $x=(z-1)/(z+1)$, which turns the
reciprocity of $A_n$ into parity; partial fractions with positive residues; a
logarithmic-derivative inequality; and counting sign changes at test points with the
intermediate value theorem. The Lean proof uses only Mathlib, including its
`Polynomial.Splits`, roots and derivative APIs. No external result about Eulerian
polynomials is assumed; their root and interlacing properties are proved from the recurrence.

## Novelty statement

Three bounded checks were made: a targeted search during the informal proof on November 14,
2026 (queries on linear combinations of consecutive Eulerian polynomials, real-rootedness,
Turán expressions and the middle coefficient), the audit's source check the same day, and a
web search on November 16, 2026. None found the sharp criterion stated or proved. This is a
finding about the sources checked, **not a claim of novelty, first discovery or historical
priority**. The purpose of this repository is to provide a checkable proof for researchers
investigating this question.

What was already known or is not claimed here:

- the sufficient triangle $1\ge b-c\ge c\ge0$ (Athanasiadis, Example 3.3);
- real-rootedness for $0\le c\le1$ and every real $b$ (Ma, Theorem 5, as reported above);
- the real-rootedness and interlacing of the Eulerian polynomials themselves, and the
  methods listed above.

**Results provided in this repository:** a Lean-checked proof that, for real $b,c\ge0$,
$A_n+bA_{n-1}+cA_{n-2}$ is real-rooted for every $n\ge3$ if and only if $c\le b^2/4+b+3$; and an
informal proof (not formalized) that all roots are negative and that, for $n\ge4$ outside the
case $b=0$ with $n$ even, they are simple.

## Access limitations

- Ma's preprint was not retrieved by the audit or by the November 16 search; its content is
  known here only from the informal report.
- Only the abstract of Gao–Liu was retrieved.
- None of the searches was an exhaustive literature review, and no human expert was
  consulted.
