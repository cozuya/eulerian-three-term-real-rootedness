# Counterexample search and auxiliary diagnostics

This file preserves the earlier counterexample-search subtask. No counterexample
to the requested criterion was found. A later full analytical proof was
independently reviewed and accepted; see `hybrid_adversarial_review.md` and
`verify_hybrid_proof.py/.json/.log`. The failed approaches below remain useful
historical diagnostics and do not describe a gap in the final proof.

## Exact polynomial checks actually completed

`exact_screen.py` uses Python 3.12.14 and SymPy 1.14.0, constructs Eulerian polynomials by the stated recurrence, square-free factors each test polynomial, and sums each square-free factor's exact number of real roots with its multiplicity.

145 checks completed, all with real-root count equal to degree. The records are in `exact_screen.json` and the chronological output is in `exact_screen.log`.

For each n in {3,4,5,10,20,21,25,30,40}, the completed grid is

* b in {1/10000,1/7,3,20,1000,2^n,3^n,10^12};
* c=t(b^2/4+b+3), t in {99/100,1}.

One further test completed: n=50, b=1/10000, t=99/100.

The process was interrupted while doing its next check because the all-degree proof was the priority. The rest of the script's scheduled n=50 and n=64 cases **were not completed**. Reproduction can run the script as written, but will do more cases than the retained output.

## Auxiliary proposed by the main researcher

Put h=A_m, g=A_{m+1}, R=g/h, and

    E=-x(1-x)R'(x)+(2-x)R(x)-2.

The proposed unproved implication is

    x<0, h(x) != 0, R(x)<=-1  =>  E(x)>=0.

Multiplying by h^2 gives the polynomial

    H=-x(1-x)(g'h-gh')+(2-x)gh-2h^2.

The Eulerian recurrence also yields the exact identity

    H=g^2-h*A_{m+2}+2gh-2h^2.

`test_aux.py` uses integer coefficient arrays and exact integer evaluation at rational x, so its sign decisions are exact. For m=1,...,100 it tested 2,568 distinct negative rational x values per m: a logarithmic grid, dense small rational grids, and powers of 2 out to 2^101 and their reciprocals. Of 256,800 tested points, 144,280 satisfied the antecedent. No failure was found. These are finite point evaluations, **not interval certificates or an all-degree proof**. Exact inputs and outputs are reconstructible from the script and `aux_screen.json`.

`aux_counts.py` performed exact Sturm counts for m=2,...,27: in every case H/x had exactly one negative real root. Isolating intervals were also computed through m=12. The retained output is in `aux_counts.json` and `aux_counts.log`. The process was interrupted after m=27; its scheduled m=28,...,30 cases were not completed.

## Analytic reduction of the auxiliary

The following part is proved and does not use Eulerian-specific root spacing. Let h be any monic palindromic real-rooted polynomial of degree d, with all roots negative, and set

    R=1+(d+1)x+x(1-x)h'/h.

Then, at nonroots of h,

    E=d*x+x(1-x)(1+x)h'/h+x^2(1-x)^2 * sum_i 1/(x-r_i)^2.

Because h is palindromic, its roots pair as -lambda,-1/lambda, with possible unpaired roots -1. Put t=-x>0 and u=lambda+1/lambda>=2. The contribution of one reciprocal pair to E is exactly

    t(u+2)(t^4-4t^2+2tu-1)/(t^2-ut+1)^2.

The numerator factor satisfies

    t^4-4t^2+2tu-1
       >= t^4-4t^2+4t-1
        = (t-1)^2(t^2+2t-1).

An unpaired root -1 contributes

    2t(t^2+2t-1)/(1-t)^2,

one half of the paired expression at u=2. Consequently E>=0 whenever t>=sqrt(2)-1, equivalently x<=1-sqrt(2), and h(x)!=0.

Therefore the unproved auxiliary only needs Eulerian-specific control for

    1-sqrt(2)<x<0.

The omitted interval cannot be settled using only palindromicity and real-rootedness. For h=(1+x)^10 and x=-1/10, the above R and E are

    R=-119/90 < -1,
    E=-158/81 < 0.

Thus a generic palindromic-real-rooted version of the implication is false.

## Other exact diagnostics

`discriminants.py` gives exact small-degree discriminants. At c=b^2/4+b+3, the n=4 discriminant factors as

    (b+1)(b^4+40b^3+616b^2+4064b+8400)/4,

strictly positive for b>=0. The n=5 boundary discriminant is 9/16 times

    b^9+91b^8+3720b^7+81888b^6+1072768b^5
    +9176416b^4+54806400b^3+230777856b^2
    +532829952b+443520768,

also strictly positive for b>=0. This certifies absence of repeated roots along those two boundary curves, but by itself is not a proof of real-rootedness for all parameters.

For fixed n>=4 and b tending to infinity on the conjectured boundary, expansion of the high-degree coefficients gives the two diverging roots formally as

    x=-b/2 +/- sqrt((2^(n-3)-1)b)+O(1).

This is a useful asymptotic diagnostic, not used as a theorem in the main result.

## Failed generic-operator route

Writing L_m f=(1+mx)f+x(1-x)f', one has

    P_{m+2}=(L_{m+1}L_m+b L_m+c)A_m.

It is tempting to assert this operator preserves all palindromic negative-rooted f at the conjectured coefficient bound. That assertion is false. For m=3, f=(1+x)^2, b=0, c=3, the output is

    x^4+18x^3+45x^2+24x+4,

which has only two real roots by exact SymPy root count. Thus the Eulerian input's extra structure matters.

## Brief source check

The primary Athanasiadis source was opened and its convention and Theorem 1.1 checked:

* https://arxiv.org/html/2302.00754v5

A short search around Eulerian Turan inequalities also found:

* Lily Li Liu and Xue Yan, *Zeros distribution of the reverse strong Turan expressions of polynomials sequences*, Advances in Applied Mathematics 142 (2023), 102426. DOI: https://doi.org/10.1016/j.aam.2022.102426 . The accessible article text discusses Hurwitz stability of reverse Turan expressions; no direct implication of the requested criterion was established.
* Huihua Gao and Xin-Bei Liu, *Hurwitz Stability of Generalized Turan Expressions of Polynomial Sequences*, arXiv:2610.04150 (2026), https://arxiv.org/abs/2610.04150 . The abstract was retrieved, but attempted HTML/PDF retrieval failed. No theorem from this paper was invoked or assumed.

This is not an exhaustive novelty audit.

## Reproduction

    python exact_screen.py --limit 145
    python test_aux.py
    python aux_counts.py --max-m 27
    python discriminants.py
    python generic_failures.py
    python finite_auxiliary_certificate.py
    python verify_hybrid_proof.py

The first and third scripts default to scheduled cases beyond those completed in this attempt, as explicitly listed above. The displayed flags reproduce the actually completed case lists. They write result files next to the scripts and print each completed record with flush enabled.

The finite auxiliary script subsequently completed 26 exact semialgebraic
certificates, m=2,...,27. These retain full polynomial coefficients, primitive
Sturm chain endpoint sign vectors, and rational separating points. They are
not dependencies of the final analytical proof. The hybrid verification script
completed 279 exact testpoint-sign cases and 22 b=0 or repeated-boundary
root-count cases; every check passed.
