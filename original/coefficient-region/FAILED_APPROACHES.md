# Earlier approaches and their exact obstructions

The full conjecture is proved. These records explain why several initially
promising shortcuts were insufficient and how the final argument avoids them.

## 1. Applying a second-order operator to arbitrary reciprocal inputs

Let \(L_mf=(1+mx)f+x(1-x)f'\). The target can be written

\[
(L_{m+1}L_m+bL_m+c)A_m,\qquad m=n-2.
\]

This operator does not preserve real-rootedness for every reciprocal polynomial
with negative roots. For example, at \(m=3,b=0,c=3,f=(1+x)^2\), its output is

\[
x^4+18x^3+45x^2+24x+4,
\]

which has only two real roots. The exact Sturm certificate is preserved in
`research/search/generic_failures.json`. Examples with distinct reciprocal roots
are also retained. This is a counterexample to a proposed generic lemma,
not to the Eulerian conjecture.

## 2. Using one auxiliary interlacer on the entire negative x-axis

Write \(h=A_m,g=A_{m+1},R=g/h\), and consider

\[
E=-x(1-x)R'+(2-x)R-2.
\]

A tempting sufficient assertion was \(E\ge0\) wherever \(x<0\) and
\(R\le-1\). Exact finite experiments supported the Eulerian version, but no
all-degree proof of this stronger assertion was obtained. Its generic
reciprocal-polynomial version is false, including for simple roots. One exact
example is

\[
h=x^2+\frac{21}{10}x+1,\qquad x=-\frac3{10},
\qquad R=-\frac{539}{460},\qquad
E=-\frac{113037}{211600}.
\]

The final proof needs \(E>0\) only for \(x<-1\), where reciprocal-pair
positivity proves it. It switches to the roots of \(A_m\) on \((-1,0)\).
The unproved stronger assertion is therefore not a gap in the completed proof.

## 3. Generic positive residues were still insufficient for the stronger lemma

A symmetric input \(C(z)=z^2-3/20\) satisfies the relevant positive
squared-residue condition, yet the proposed inequality at every shifted
interlacer root fails. Its exact certificate is retained in
`research/transform/check_auxiliary_obstruction.json`. The final proof uses
residue positivity only for signs at positive roots of the lower polynomial.

## 4. Partial regions developed along the way

Successive analytical arguments established

\[
c\le1+\frac{(b+1)^2}{5},\qquad
c\le1+\frac{(b+1)^2}{4},
\]

and the strip \(0\le c\le3\). In fact, the strip construction proves
\(c\le n-1\) for each \(n\ge4\), with arbitrary \(b\ge0\).
The complete proofs and audits are retained in the research directories.
They are superseded by the full theorem.

## 5. Finite certificates and numerical diagnostics

The exploratory polynomial \(H=(g+h)^2-3h^2-hA_{m+2}\) was studied by exact
root counts and rational evaluations. Exact finite auxiliary certificates
through \(m=27\) were completed. They would have supported parameter-uniform
low-degree lemmas, but the final proof does not depend on them.

Floating-point searches of generic transformed inputs and large-parameter
asymptotic expansions were used only to choose approaches and test proposed
lemmas. All claims in the final theorem follow from the analytical proof.
