# AUDIT — two arguments on `A_n + b A_{n-1} + c A_{n-2}`

Packet audited: `eulerian-cross-vendor-review.zip`
SHA-256 `546fb0ce23613ee2a02ac87a56d74400e6ea91aecdd93094d005d846d5897a2e`; all 16 files match the packet's `MANIFEST.json`.
Audit date 2026-11-14. Auditor: Claude (Anthropic), working alone, no contact with authors, nothing published or modified outside this archive.

Notation follows the packet: `A_n(x) = sum over S_n of x^des`, `A_0 = A_1 = 1`, `P_n = A_n + b A_{n-1} + c A_{n-2}` with real `b, c >= 0`, `n >= 3`.

---

## 1. Verdicts

| Submission | Claim audited | Verdict |
|---|---|---|
| **Candidate A** | `P_n` real-rooted for every `n >= 3`  ⇔  `c <= b^2/4 + b + 3` | **VALID** |
| **Candidate B** | `c <= 1 + (b+1)^2/4`  ⇒  `P_n` has `n-1` distinct negative roots, every `n >= 3` | **VALID** |
| Candidate B, full-bound route | reduction of the full criterion to inequality (6) | The reduction is correct. Inequality (6) is unproved for general `m`, as B itself states. As a proof of the full criterion this route is **INCOMPLETE**; B does not claim otherwise. |

No substantive defect was found in either submission. Nothing was repaired. Minor presentation notes are in 3.8 and 4.5.

The submissions are mathematically compatible. A and B's full-bound route use the same separator and the same completed-square identity; they differ in one step (section 5).

A verdict of VALID here means: every inference on which the all-degree conclusion depends was re-derived independently of the submission's text and found correct, and exact computation on finite ranges found no contradiction. It is not a machine-checked formal proof.

---

## 2. Method

1. Read in the prescribed order: `00_problem.md`, A's argument, B's argument, B's reduction, B's obstruction. Re-derived every decisive step **before** opening any supplied script.
2. Wrote an independent exact toolkit (`checks/eul.py`): rational polynomials (python-flint), my own signed-remainder sequences, Sturm counts of distinct roots, multiplicity-aware counts, Sturm–Tarski sign queries, bisection root isolation and merged root ordering. The toolkit is self-tested against polynomials with known roots and against sympy (`00_selftest`).
3. Wrote checks `01`–`08` against the submissions' claims, including attempts to break them.
4. Inspected the seven supplied scripts, then ran them on a scratch copy.
5. Light source check of the one external reference that could be reached.

"Exact" below means rational arithmetic with certified sign decisions; no floating point enters any certified statement. Float output is labelled diagnostic. Finite checks cannot establish the all-degree theorem; they are used to test the proof's lemmas and to try to refute it.

---

## 3. Candidate A — reconstruction of the decisive steps

### 3.0 Logical structure

```
§2  recurrence ⇒ shape, simple negative roots, consecutive interlacing; Cayley facts
      │
      ├─► Lemma 3.1 (induction on n, base n=3) ─► Cor. 3.2:  h/g > 0 at positive roots of f
      │
      ├─► structure of q = g + α(z+1)f          (uses §2 only)
      │
Lemma 4.1 (elementary, one-sided)  +  identity (5.4) (pure algebra)
      │                                   └─► (5.5): sign of P at negative roots of q
      │
Cor. 3.2 + b ≥ 0 ─► (5.6): sign of P at positive roots of f
      │
      └─► sign count: Case I (n odd), Case II (n even, b>0) ─► Case III (n even, b=0, limit) ; n=3 direct
```

No arrow points backwards. In particular Lemma 3.1 is proved before, and independently of, the theorem.

### 3.1 Eulerian preliminaries (brief item A)

Comparing coefficients of `x^k` in the recurrence gives

```
e_{j+1,k} = (k+1) e_{j,k} + (j-k+1) e_{j,k-1}.
```

Consequences, each a one-line induction: degree `j-1`; leading coefficient `e_{j+1,j} = e_{j,j-1} = 1`; constant term 1; all coefficients positive; palindromic, since substituting `k -> j-k` and using `e_{j,i} = e_{j,j-1-i}` returns the same right-hand side. `A_j(1) = j!` from the recurrence at `x = 1`.

Roots. Let `r_1 < ... < r_{j-1} < 0` be the simple roots of the monic `A_j` (`j >= 2`). Then `A_{j+1}(r_i) = r_i(1-r_i) A_j'(r_i)`, the multiplier is negative and `sgn A_j'(r_i) = (-1)^{j-1-i}`, so `sgn A_{j+1}(r_i) = (-1)^{j-i}`. The two outer comparisons the submission leaves implicit: at `i = j-1` the sign is `-1` against `A_{j+1}(0) = 1`; at `i = 1` it is `(-1)^{j-1}` against `(-1)^j` at `-∞`. That gives one root of `A_{j+1}` in each of the `j` gaps `(-∞,r_1), (r_1,r_2), ..., (r_{j-1},0)`, exhausting the degree. Correct.

Cayley coordinates. `x = (z-1)/(z+1)` is an increasing bijection `(-1,1) -> (-∞,0)`, with `z = 0 ↔ x = -1` and `z -> -z ↔ x -> 1/x`.

```
C_j(z) = (1+z)^{j-1} A_j(x) = Σ_k e_{j,k} (z-1)^k (z+1)^{j-1-k}
```

so the leading coefficient is `Σ_k e_{j,k} = j!`, `C_j(1) = 2^{j-1}`, `C_j(-1) = (-2)^{j-1}`. Since `C_j(-1) != 0` and `deg C_j = j-1`, the roots of `C_j` are exactly the images of the roots of `A_j`: `j-1` simple roots in `(-1,1)`. Palindromicity gives `C_j(-z) = (-1)^{j-1} C_j(z)`. A symmetric set of `j-1` simple roots contains 0 iff `j-1` is odd, so the zero at 0 occurs exactly for even `j` and is simple.

Recurrence (2.5). With `dx/dz = 2/(z+1)^2`, `1+jx = ((j+1)z-(j-1))/(z+1)`, `x(1-x) = 2(z-1)/(z+1)^2`:

```
(z^2-1) C_j' + 2z C_j = (1+z)^{j-1} [(j+1)z-(j-1)] A_j + 2(z-1)(1+z)^{j-2} A_j'  = (1+z)^j A_{j+1}(x).
```

So `C_{j+1} = T C_j`, `T = (z^2-1)D + 2z`. Correct. (`C_2 = 2z`, `C_3 = 6z^2-2`, `C_4 = 24z^3-16z`.)

Exact confirmation: `01_eulerian_basics` — three independent constructions of `A_n` agree (enumeration of `S_n` for `n <= 8`; closed form and recurrence for `n <= 60`); shape, squarefreeness, `n-1` negative roots for `n <= 60`; the exact gap pattern of consecutive interlacing for `j <= 39`; both constructions of `C_j`, degree, `j!`, parity, endpoint values, zero at 0, roots in `(-1,1)` for `j <= 60`.

### 3.2 Lemma 3.1, positive residues (brief item B)

Claim. With `F_n = (z^2-1) C_{n-2}` (`n >= 3`),

```
C_n / F_n = ρ_n + Σ_j λ_j / (z^2 - a_j),     ρ_n > 0,  λ_j > 0,  0 < a_j <= 1,          (3.1)
```

the `a_j` being the squares of the positive roots of `F_n`.

Set-up facts, all from (2.5): `F_n' = C_{n-1}`, `F_{n+1} = (z^2-1) F_n'`, `C_{n+1} = ((z^2-1) C_n)'`. `F_n` and `C_n` have the same degree `n-1` and the same parity, so the ratio is even with constant polynomial part `ρ_n = n!/(n-2)! = n(n-1)`. Roots of `F_n`: `±1` and the roots of `C_{n-2}`, all simple.

Residue ↔ coefficient. For an even rational function with a simple pole at `ξ > 0` of residue `κ`, the residue at `-ξ` is `-κ`, and `κ/(z-ξ) - κ/(z+ξ) = 2ξκ/(z^2-ξ^2)`. Hence `λ = 2ξκ`, and `λ_j > 0` iff the ordinary residue at the positive pole is positive. The submission states this conversion correctly.

Zero. When `n` is even both `C_n` and `F_n` are odd with a simple zero at 0 (section 3.1 above), so the ratio is regular at 0. When `n` is odd neither vanishes at 0. Cancellation is legitimate.

Base `n = 3`: `F_3 = z^2-1`, `C_3 = 6z^2-2`, `C_3/F_3 = 6 + 4/(z^2-1)`. Correct; the induction then runs `n -> n+1` for `n >= 3`, using (2.5) with index `n-2 >= 1`.

Induction step, reconstructed. Assume (3.1) at `n`, write `R = C_n/F_n` and `Φ = (z^2-1) R`. Then `(z^2-1) C_n = Φ F_n` and

```
C_{n+1} = (Φ F_n)' = Φ' F_n + Φ F_n'.
```

Why the critical points are the relevant points: the interior poles at level `n+1` are the roots of `F_{n+1}/(z^2-1) = F_n' = C_{n-1}`. Let `ξ ∈ (0,1)` be one. `F_n` has simple roots, so `F_n(ξ) != 0`, hence `ξ^2 != a_j` and `R` is regular at `ξ`.

*Numerator.* `F_n'(ξ) = 0` gives `C_{n+1}(ξ) = Φ'(ξ) F_n(ξ)`. From (3.1), `Φ = (z^2-1)ρ_n + Σ λ_j [1 + (a_j-1)/(z^2-a_j)]`, so

```
Φ'(z) = 2z [ ρ_n + Σ_j λ_j (1-a_j) / (z^2-a_j)^2 ].
```

For `ξ > 0` this is strictly positive: `ρ_n > 0` and every summand is `>= 0` because `λ_j > 0`, `a_j <= 1`. This is (3.5), and it is where `a_j <= 1` and `ξ > 0` are used.

*Denominator.* `F_{n+1}' = 2z F_n' + (z^2-1) F_n''`, so `F_{n+1}'(ξ) = (ξ^2-1) F_n''(ξ)`. In general `(F_n'/F_n)' = -Σ_s (z-s)^{-2}` over the roots `s` of `F_n`; at a critical point the left side is `F_n''(ξ)/F_n(ξ)`, and since every `s` is real, `F_n''(ξ)/F_n(ξ) = -Σ_s (ξ-s)^{-2} < 0`. Hence `F_{n+1}'(ξ)/F_n(ξ) = (1-ξ^2) Σ_s (ξ-s)^{-2} > 0`. This is (3.3)–(3.4); it also shows `ξ` is a simple root of `F_{n+1}`.

*Residue.*

```
C_{n+1}(ξ) / F_{n+1}'(ξ) = Φ'(ξ) / [ (1-ξ^2) Σ_s (ξ-s)^{-2} ] > 0.
```

*Endpoint.* `C_{n+1}(1) = 2^n` and `F_{n+1}'(1) = 2 F_n'(1) = 2 C_{n-1}(1) = 2^{n-1}`; the residue at 1 equals 2.

*Accounting.* The positive roots of `F_{n+1} = (z^2-1) C_{n-1}` are exactly 1 and the positive roots of `C_{n-1}`. Negative poles follow by evenness. A zero at 0, when present, is simple in both and cancels. Equal degrees and positive leading coefficients give polynomial part `(n+1)n > 0`. Nothing is omitted. The step uses only §2 and the level-`n` expansion; nothing is circular.

Corollary 3.2. For a root `r > 0` of `C_{n-2}`, the residue of `C_n/F_n` at `r` is `C_n(r)/F_n'(r) = C_n(r)/C_{n-1}(r) = λ/(2r) > 0`, strictly, and `C_{n-1}(r) != 0`. With `f = C_m`, `g = C_{m+1}`, `h = C_{m+2}` this is `h(r)/g(r) > 0` at every positive root of `f`. The required strictness follows.

Hand check of one nontrivial step (`n = 5 -> 6`): `R_5 = 20 + 4/(t-1) + (8/3)/(t-1/3)` in `t = z^2`; `ξ^2 = 2/3`; (3.5) predicts `C_6(ξ)/F_5(ξ) = 2ξ[20 + (8/3)(2/3)/(1/9)] = 72ξ`; directly `C_6(ξ) = -48ξ`, `F_5(ξ) = -2/3`. Agrees; the new coefficient is `λ = 6`, and indeed `R_6 = 30 + 4/(t-1) + 6/(t-2/3)`.

Exact confirmation: `02_residue_lemma`, `n = 3..46` — the equivalent root pattern in `t` (zeros and poles alternate `N,D,...,N,D`, last pole `t = 1`; with `ρ > 0` and simple poles this is equivalent to all `λ_j > 0`, by the sign count `sgn N(a_i) = sgn D'(a_i)·sgn(lc N/lc D)`); Corollary 3.2 by Sturm–Tarski; and each sign used inside the step ((3.3), (3.4), (3.5), residue) at every positive critical point. `08_large_degree`: Corollary 3.2 exactly at `n = 60, 80, 100, 130, 160, 200`.

### 3.3 Lemma 4.1, one-sided inequality (brief item C)

For `f` with roots in `(-1,1)` symmetric about 0 and `z ∈ (-1,0)` not a root, with `u = -z ∈ (0,1)`:

* a root at 0 contributes `(1-z^2)/z^2 - 2/z = (1+2u-u^2)/u^2 > 0`, since `1+2u-u^2 = 2-(1-u)^2`;
* a pair `±√a` contributes

```
2(1-z^2)(z^2+a)/(z^2-a)^2 - 4z/(z^2-a) = 2 N(u,a)/(u^2-a)^2,
N(u,a) = u^2(1+2u-u^2) + a(1-2u-u^2) = a(1-u)^3(1+u) + (1-a) u^2 (1+2u-u^2) > 0   for 0<a<1, 0<u<1.
```

Both formulas re-derived from scratch; correct. Every root contributes strictly positively and `f` nonconstant supplies at least one root, so `E(z) > 0` strictly. Poles are excluded by hypothesis.

Where it is applied: only at negative roots `s` of `q`. There `s ∈ (-1,0)`, `f(s) != 0` by strict interlacing, and `f = C_m` with `m >= 2` is nonconstant with simple symmetric roots in `(-1,1)`. Every hypothesis holds at every point of use.

The lemma is genuinely one-sided. For `f = z`, `E(1/2) = -1`. For the Eulerian `f = C_m` the polynomial `f^2 E` has no root in `(-1,0)` and exactly one root in `(0,1)`, beyond which it is negative (`03_logderiv_lemma`, exact, `m = 2..40`; the same check ran 3999 random exact trials of the lemma itself). Candidate A does not use the lemma for `z > 0`.

### 3.4 The identity (5.4) and the separator (brief item D)

Write `w = z^2-1`. `g = w f' + 2z f`; applying `T` again, `h = w^2 f'' + 6zw f' + (6z^2-2) f`. With `b = 2α-2`:

```
P f           :  ff'' · w^2  |  ff' · w[6z + b(z+1)]        |  f^2 · [6z^2-2 + 2bz(z+1) + c(z+1)^2]
q^2 + ... - … :  ff'' · w^2  |  ff' · w[4z + 2α(z+1) - 2]   |  f^2 · [4z^2 + 4αz(z+1) + (c-2)(z+1)^2]
```

(the `f'^2` terms cancel on the right). The `ff'` brackets differ by `-2z-2+2(z+1) = 0`; the `f^2` brackets by `6z^2-2-4z(z+1)-4z^2+2(z+1)^2 = 0`. So (5.4) holds identically, for any `f`. The bracket in its last term is `f^2 E`. `α^2+2 = b^2/4+b+3`.

`P = h + b(z+1)g + c(z+1)^2 f` is `(1+z)^{n-1} P_n(x)`. Leading coefficient `(m+2)! + b(m+1)! + c m! > 0`, so `deg P = m+1 = n-1`: no degree drop. `P(1) = 2^{m+1}(1+b+c) > 0`, `P(-1) = h(-1) = (-2)^{m+1}`. Since `P(-1) != 0` and `P_n(1) > 0`, roots of `P` in `(-1,1)` and negative roots of `P_n` correspond with multiplicity.

Separator `q = g + α(z+1) f`: degree `m`, leading coefficient `(m+1)! + α m! > 0`. At the roots `r_1 < ... < r_{m-1}` of `f`: `q(r_i) = (r_i^2-1) f'(r_i)`, of sign `(-1)^{m-i}`. `q(1) = 2^m(1+α) > 0` against `q(r_{m-1}) < 0`; `q(-1) = -2 f(-1) = (-2)^m` against `sgn q(r_1) = (-1)^{m+1}`. One root in each of the `m` gaps including both end gaps; degree exhausted; roots simple; no common root with `f`. This is a direct sign count; it does not invoke "sums of real-rooted polynomials are real-rooted".

At a negative root `s` of `q`, (5.4) gives

```
P(s) f(s) = (s+1)^2 (c - α^2 - 2) f(s)^2 - (1-s^2) f(s)^2 E(s) < 0,
```

first term `<= 0` by the hypothesis on `c`, second strictly negative by Lemma 4.1. Strict also on the boundary. This is (5.5).

At a positive root `r` of `f`: `P(r) = h(r) + b(r+1) g(r)`, `h(r)` and `g(r)` have the same strict sign (Cor. 3.2), `b(r+1) >= 0`, so `sgn P(r) = sgn g(r) = -sgn f'(r)`. This is (5.6). It does not involve `c`.

Exact confirmation: `04_central_identity` (identity for an arbitrary function `f`, with `h` obtained by applying `T` twice; Cayley dictionary for `n <= 40`). `05_root_count`: structure of `q` for 330 pairs `(m,b)`, `m = 2..34`, `b` from 0 to `10^12`; (5.5) in 1320 cases and (5.6) in 1280 cases by Sturm–Tarski, with `c` at 0, 1/3, `1-10^{-9}` and 1 times the bound.

### 3.5 The root count (brief item E)

`p = floor((m-1)/2)`. Negative roots of `q`: `s_1 < ... < s_{p+1}`.

**Case I, `n` odd** (`m = 2p+1`, `p >= 1`, `f` even of degree `2p`). `f` has roots `r_1<...<r_p<0<r_{p+1}<...<r_{2p}`. Central gap: `q(0) = α f(0)` because `f'(0) = 0`; `f` keeps the sign of `f(0)` on `(r_p, r_{p+1})`, so `sgn f'(r_p) = sgn f(0) = -sgn f'(r_{p+1})`, hence `sgn q(r_p) = -sgn q(0)` and `sgn q(r_{p+1}) = sgn q(0)`. The central root of `q` is negative: `p+1` negative, `p` positive roots. Test points in order: `s_1,...,s_{p+1}, r_{p+1},...,r_{2p}` — `m` points.

```
point   -1    s_i (i=1..p+1)    r_{p+j} (j=1..p)       1
sgn P    +      (-1)^i           (-1)^{p+1+j}           +
```

`sgn f(s_i) = (-1)^{i-1}` from `f(-1) > 0`; `r_{p+j}` is the `(p-j+1)`-th root from the top, so `sgn f' = (-1)^{p-j}`. The `k`-th test point carries sign `(-1)^k`, `k = 1..m`, flanked by `+` at `k = 0` and `k = m+1` (even). The junction `s_{p+1} -> r_{p+1}` is `(-1)^{p+1} -> (-1)^{p+2}`: alternation continues across it.

**Case II, `n` even, `b > 0`** (`m = 2p+2`, `p >= 0`, `f` odd of degree `2p+1`). Roots of `f`: `r_1<...<r_p<0=r_{p+1}<...<r_{2p+1}`. `q` has `p+1` roots on each side. Test points: `s_1,...,s_{p+1}, 0, r_{p+2},...,r_{2p+1}` — `m` points. `P(0) = b g(0) = -b f'(0)` because `f, h` are odd, and `sgn f'(0) = (-1)^p`.

```
point   -1    s_i (i=1..p+1)    0             r_{p+1+j} (j=1..p)     1
sgn P    -      (-1)^{i+1}      (-1)^{p+1}       (-1)^{p+j+1}        +
```

The `k`-th test point carries `(-1)^{k+1}`, flanked by `-` at `k = 0` and `+` at `k = m+1 = 2p+3`. For `p = 0` (`n = 4`, `f = 2z`) the points are `s_1, 0` with signs `+, -` between `P(-1) < 0` and `P(1) > 0`.

In both cases the `m+2` ordered points `-1 < t_1 < ... < t_m < 1` carry strictly alternating nonzero signs, so each of the `m+1` disjoint open intervals between consecutive points contains a root. `m+1 = deg P`, so there is exactly one simple root in each and none elsewhere. No root is counted twice: the intervals are disjoint and the test points are not roots.

Exact confirmation: `05_root_count` — the full merged order `P-root, T, P-root, ..., T, P-root` on `(-1,1)` in 146 cases (`m = 2..22`, on the boundary and at `c = 0`), including `b = 0` in Case I.

### 3.6 Boundaries and remaining cases

* **`n = 3`.** `P_3 = x^2 + (b+4)x + 1+b+c`, discriminant `b^2+4b+12-4c`. Real-rooted iff `c <= b^2/4+b+3`; on the boundary `P_3 = (x+b/2+2)^2`. This is the whole of necessity.
* **`c = b^2/4+b+3`, `n >= 4`.** (5.5) stays strict because `E > 0`. Roots remain simple in Cases I and II.
* **`b = 0`, `n` odd.** Case I applies verbatim; (5.6) only needs `b >= 0`.
* **`b = 0`, `n` even (Case III).** Here `P(0) = 0`, so 0 cannot serve as a test point. A takes `b_j -> 0+` with `c` fixed; `0 <= c <= 3 < b_j^2/4+b_j+3`, so each `(b_j, c)` is admissible and Case II applies. The `P_n(·; b_j, c)` are monic of the fixed degree `n-1` and converge coefficientwise; a limit of monic real-rooted polynomials of fixed degree is real-rooted (roots bounded, pass to a convergent subsequence of ordered root vectors). Correct. Simplicity is not claimed in this case and not needed for the theorem.
* **Degree drops.** None: all polynomials involved are monic of degree `n-1` in `x`.
* **Real parameters.** Every step is for arbitrary real `b, c >= 0`; nothing is sampled.

### 3.7 Does the argument prove too much?

Sections 4–6 of A use only: `f` has positive leading coefficient and simple roots in `(-1,1)` symmetric about 0. The Eulerian sequence enters solely through Corollary 3.2. B's obstruction shows the conclusion is false for a non-Eulerian reciprocal input, so for A to be sound the Eulerian-specific step must be the one that fails there. `07_cross_checks` verifies this exactly:

* B's obstruction in Cayley form has seed `(2z)^{10}`, `f = 2^{10} z^9 (12z^2-10)`: not simple-rooted, so A's hypotheses fail at once.
* Perturbing the seed to `Π(z^2-(i/50)^2)`, `i = 1..5`, gives a simple-rooted `f` for which `P` (with `b = 4`, `c = 11`) still has only 11 real roots. There A's generic steps hold (structure of `q`, (5.5)), while the analogue of Corollary 3.2 fails (sign sum `-1` instead of `5`) and the level below already has negative residues. The break is in the Eulerian-specific input — the positivity that Lemma 3.1 propagates from its base case — and nowhere else.
* Over 594 random non-Eulerian seeds, half of them clustered near 0: 102 gave a non-real-rooted `P`, and in none of those did the Corollary 3.2 analogue hold; whenever it held (85 seeds) `P` was real-rooted.
* The induction step of Lemma 3.1 is generic: on 54 random seeds whose level-0 residues were all positive, the next level was positive every time.

So A's proof neither assumes nor implies the false generic statement.

### 3.8 Issues

Substantive: none.

Minor, none affecting validity:

1. §2 does not display the two outer sign comparisons in the interlacing induction (supplied in 3.1 above).
2. §3 does not say separately that the new poles are simple; (3.4) gives `F_{n+1}'(ξ) != 0`.
3. Lemma 4.1 assumes simple roots; the proof does not need it.
4. Case III proves real-rootedness only; see the auditor's remark in section 6 for simplicity.
5. Reference [2] (Ma) could not be retrieved. It is not used in the logic; Lemma 3.1 is proved in full.
6. `verify_hybrid_proof.py` line 21 checks the positivity decomposition only at `a = 1`; the general identity is in `check_proof_identities.py`. Supporting code only.

---

## 4. Candidate B — reconstruction

### 4.1 Quotient identities

`F = A_m`, `G = A_{m+1}`, `H = A_{m+2}`, `R = G/F`, `q(x) = x(1-x)`, roots `a_j < 0` of `F`.

* `R = 1 + mx + q F'/F`. Since `x + q/(x-a) = x(1-a)/(x-a)`, summing over the `m-1` roots gives `R = 1 + x + Σ_j (1-a_j)x/(x-a_j)`.
* `d/dx [x/(x-a)] = -a/(x-a)^2`, so `R' = 1 - Σ_j a_j(1-a_j)/(x-a_j)^2 >= 1` at every real non-pole, because `a_j(1-a_j) < 0`. Strict for `m >= 2`; identically 1 for `m = 1`.
* `F`, `G` palindromic of degrees `m-1`, `m` give `R(1/x) = R(x)/x`; differentiating, `R'(1/x) = R(x) - x R'(x)`.
* `G' = R'F + RF'` and `qF'/F = R-1-mx` in `H = (1+(m+1)x)G + qG'` give `H/F = R^2 + xR + qR'`.

All correct.

### 4.2 Separator and sign

`d = (b+1)/2`, `Q = G + dF`. Each pole of `R` has residue `a_j(1-a_j) < 0` and `R' > 0`, so `R` runs from `-∞` to `+∞` on each interval between consecutive poles, from `-∞` (at `-∞`) to `+∞` on the leftmost interval, and from `-∞` to `+∞` on the rightmost, where `R(0) = 1 > -d` places the crossing left of 0. Hence `Q` has `m` distinct negative roots, strictly interlaced by `F`, with no common root. For `m = 1`, `Q = x+1+d`.

At a root `r` of `Q`: `R(r) = -d`, and `q(r)R'(r) = (1-r)·rR'(r) = (1-r)(R(r)-R'(1/r)) = (1-r)(-d-R'(1/r))`. Then

```
P/F (r) = d^2 - rd + qR' - bd + c = d^2 - (b+1)d + c - (1-r) R'(1/r).
```

`1/r` is not a pole (`F` reciprocal, `F(r) != 0`, `r != 0`), `1/r` is real, so `R'(1/r) >= 1`, and `1-r > 0`:

```
P/F (r) <= d^2 - (b+1)d + c - (1-r) = c - 1 - (b+1)^2/4 + r <= r < 0.
```

Strict at equality `c = 1+(b+1)^2/4`, for every real `b >= 0`. Correct.

### 4.3 Root count

`P` monic of degree `m+1`, `P(0) = 1+b+c > 0`, `sgn F(r_i) = (-1)^{m-i}`, so `sgn P(r_i) = (-1)^{m-i+1}`. Sign changes on `(r_m, 0)`, on each `(r_i, r_{i+1})`, and on `(-∞, r_1)` (`(-1)^m` at `r_1` against `(-1)^{m+1}` at `-∞`): `m+1` disjoint intervals, the degree. All roots distinct and negative. `n = 3` (`m = 1`) is covered: `P(r) = c-d^2-2-d <= -1-d < 0` at `r = -1-d`; consistently the discriminant of `P_3` on B's boundary is `2b+7 > 0`.

**B's partial theorem holds for all stated real parameters and all `n >= 3`, including equality.**

Exact confirmation: `06_candidate_B` — generic identities symbolically; on Eulerian triples `m = 1..40`: the quotient identity, palindromicity, `R'(1/x) = R - xR'` as a polynomial identity, `R' > 1` everywhere for `m >= 2` (Sturm), `m` distinct negative roots of `Q` (320 cases; full interlacing pattern for `m <= 20`), `P/F < 0` and the sharper `P/F <= r` at every root of `Q` (960 Sturm–Tarski cases, with exact equality `P/F = r` detected at `m = 1` on the boundary), and `n-1` distinct negative roots for `n = 3..90` (1312 cases).

### 4.4 The full-bound reduction and the finite certificates

With `d = 1 + b/2`:

```
F·P = (G + dF)^2 + (c - d^2 - 2) F^2 - N_m,       N_m = G^2 - FH + 2FG - 2F^2.          (7)
```

Verified generically (it is `G^2 + 2dGF + (c-2)F^2` on both sides). So `N_m >= 0` at the roots of `Q_d` for all `d >= 1` suffices for the full criterion; that is B's (6). The reduction, the treatment of equality by a limit, and `N_1 = 0` are correct.

(8) and the pairing identity are correct, so `N_m >= 0` for `x <= 1-√2` from negative reciprocal roots alone. The interval `(1-√2, 0)` is left open by B for general `m`.

Certificates, recomputed without B's intervals: for `m = 2..15`, `N_m` has degree `2m-1`, negative leading coefficient, is squarefree, vanishes at 0, has exactly one negative root `α_m`, and the largest root `β_m` of `G+F` satisfies `β_m < α_m`. B's stored coefficients and intervals agree with mine. The same pattern persists for every `m <= 40` (my extension). Through (7), which is parameter-free in its hypothesis, this certifies the full region with simple roots for **all real** admissible `(b,c)` at `4 <= n <= 42`, independently of A's Lemma 3.1.

Status of (6) for general `m`: unproved in the packet; not refuted; true for `m <= 40`.

### 4.5 Issues

Substantive: none in the partial theorem. The full-bound route is incomplete and is labelled so by B.

Minor:

1. The remark that the proof extends to any reciprocal `F` with distinct negative roots is right, with `P` monic and `P(0) = 1+b+c` replaced by multiples of the leading coefficient of `F`.
2. `check_identities.py` refers in its docstring to `partial_theorem.md`, a file not in the packet.

### 4.6 The obstruction

Recomputed: with `h = (x+1)^{10}`, `H + 4G + 11F = (x+1)^7 S(x)` with the stated sextic; `S` is squarefree with exactly 4 real roots (my Sturm count), so 11 of 13 roots are real. `(4, 11)` lies on the proposed boundary and outside B's own region (`29/4`). `F = (x+1)^9 (x^2+22x+1)` is not an Eulerian polynomial and has a 9-fold root. It refutes the generic one-step claim only. At B's own boundary `c = 29/4` the same triple is real-rooted.

---

## 5. Comparison

**Same skeleton.** A's `q = g + α(z+1) f` is the Cayley transform of B's `Q_d` with `d = α = 1 + b/2` (exact, `n <= 40`). A's (5.4) is B's (7) multiplied by `(1+z)^{2m}`:

```
(1+z)^{2m} N_m(x) = (1-z^2) [ (1-z^2)(f'^2 - f f'') - 2 f f' ],      i.e.   N_m / F^2 = -x · E(z).
```

Verified for an arbitrary function `f` and for the Eulerian triples. So "`N_m >= 0` at a root of `Q_d`" and "`E >= 0` at a root of `q`" are the same statement.

**Where the scopes diverge.** Both need the sign of `P` at `m` points.

* B's partial theorem uses all `m` roots of `Q_{(b+1)/2}` and bounds the unknown term by `R' >= 1`, which uses only negativity of the roots. That costs `b/2 + 7/4` in `c`.
* B's full-bound route uses all `m` roots of `Q_{1+b/2}` and needs `N_m >= 0` at every one of them. That is elementary for `x <= 1-√2` and unproved on `(1-√2, 0)`.
* A uses the roots of the same separator **only where `x < -1`** (`z < 0`), where `N_m > 0` is elementary (Lemma 4.1 is the `x < -1` part of B's 5.1). For the remaining points A does not use the separator at all: it takes the roots of `A_{n-2}` in `(-1,0)` (positive roots of `f`), where `P = A_n + b A_{n-1}` and the sign is fixed by two-step interlacing (Cor. 3.2) and `b >= 0`, with no condition on `c`. Symmetry about `x = -1` makes the two families fit: `p+1` separator roots, `p` roots of `f`, plus `x = -1` itself when `n` is even.

The single mathematical step accounting for the difference in scope is therefore Lemma 3.1 together with the change of test points on `-1 < x < 0`.

**Answers to the brief's questions.**

* B's inequality (6) is sufficient for B's route, not necessary for the theorem.
* A does not depend on (6), does not prove it, and legitimately avoids it: the points where (6) is unproved are not among A's test points.
* B's obstruction invalidates nothing A assumes: A needs simple roots (proved in §2) and Cor. 3.2 (proved from the Eulerian base case); the obstruction has neither (3.7).
* The submissions are compatible: B's region is contained in A's (difference `b/2+7/4 > 0`), and B's conclusion (distinct negative roots) agrees with A's on the overlap.

A is not accepted because it contains B's result, and not doubted because B stopped earlier. A is accepted because each of its steps was re-derived; B's stop is explained by a step B lacked.

---

## 6. Theorem supported by this audit

Let `b, c >= 0` be real and `P_n = A_n + b A_{n-1} + c A_{n-2}`.

1. `P_n` has only real roots for every `n >= 3` **if and only if** `c <= b^2/4 + b + 3`. (Candidate A.)
2. In that region every root is negative (positive coefficients), and:
   * `n = 3`: two distinct roots if `c < b^2/4+b+3`; the double root `-(b/2+2)` if `c = b^2/4+b+3`.
   * `n >= 4` with `n` odd or `b > 0`: `n-1` distinct roots, also on the boundary. (A, Cases I–II.)
   * `n >= 4` even and `b = 0` (`0 <= c <= 3`): real-rooted (A, Case III); distinct for `c <= 5/4` (B). See the remark below for `5/4 < c <= 3`.
3. `c <= 1 + (b+1)^2/4` implies `n-1` distinct negative roots for every `n >= 3`. (Candidate B; an independent elementary proof of a subcase of 1–2.)
4. The criterion is uniform, not per-degree: necessity comes only from `n = 3`. For a fixed `n >= 4` the boundary roots are simple, so they stay real under a small increase of `c`, and the real-rooted set of that single degree is strictly larger (e.g. `P_4(x;0,c) = (x+1)(x^2+10x+1+c)` is real-rooted exactly for `c <= 24`; diagnostic thresholds for `n <= 12` are in `outputs/05_root_count.txt`).

Not established by either submission: inequality (6) for all `m`; the exact region for an individual degree `n >= 4`. Novelty and priority were not assessed.

**Auditor's remark (not part of either submission).** In the case `n` even, `b = 0`, `0 <= c <= 3` the roots are in fact simple, and no limit is needed. Use A's own test points without the point 0: (5.5) and (5.6) hold with `b = 0`, giving `2p+1` sign-change intervals; on the remaining interval `(s_{p+1}, r_{p+2})` (or `(s_1, 1)` when `p = 0`) the end signs agree, so it contains an even number of roots, at least two because `P(0) = 0`. The total is at least `2p+3 = deg P`, hence exactly that. The only possible multiple root is `z = 0` (`x = -1`), double iff `P'(0) = h'(0) + c f'(0) = 0`, i.e. `c = -C_n'(0)/C_{n-2}'(0) = T_{n+1}/T_{n-1}` (ratio of tangent numbers: 8, 17, 496/17, ...). Status: the counting argument is a short proof; the closed form and `T_{n+1}/T_{n-1} >= 8` were verified exactly for even `n <= 90` and follow in general from the classical zeta-value formula for tangent numbers, which I did not re-derive here. Squarefreeness was confirmed exactly for `c ∈ {0, 1/2, 5/4, 2, 3}`, even `n <= 90`, and for all real parameters at `n <= 42` via 4.4.

---

## 7. Computations and source checks actually performed

All runs completed with exit code 0 and status PASS. Python 3.13.18, sympy 1.14.0, python-flint 0.9.0, mpmath 1.3.0. Outputs are in `outputs/`.

| Script | What it certifies (exact unless noted) | Range | Time |
|---|---|---|---|
| `00_selftest` | toolkit vs known roots (300), Tarski (296), sympy (200), merged order (100) | — | 1 s |
| `01_eulerian_basics` | constructions, shape, roots, interlacing pattern, Cayley facts | `n <= 60` (pattern `j <= 39`) | 5 s |
| `02_residue_lemma` | Lemma 3.1 pattern, Cor. 3.2, signs in the induction step; λ values (diagnostic, 60-digit) | `n = 3..46` (diag. `<= 40`) | 5 s |
| `03_logderiv_lemma` | Lemma 4.1 algebra; 3999 random exact trials; Eulerian bracket on `(-1,0)` and `(0,1)` | `m = 2..40` | 2 s |
| `04_central_identity` | (5.4) for arbitrary `f`; `h`; `N_m` ↔ bracket; Cayley dictionary | `n = 3..40` | 1 s |
| `05_root_count` | `q` structure (330), (5.5) (1320), (5.6) (1280), `P(0)` (680), full order (146), Sturm in `x` (2624), `n = 3`, Case III, per-degree thresholds (diagnostic) | `m <= 34`, pattern `m <= 22`, Sturm `n <= 90` | 4.4 min |
| `06_candidate_B` | B's identities, separator, signs, root counts; certificates recomputed and extended; obstruction | triples `m <= 40`, Sturm `n <= 90`, certificates `m = 2..40` | 3.4 min |
| `07_cross_checks` | proves-too-much test; genericity of the induction step; A/B test points | 594 + 54 seeds, `m = 2..40` | 2 s |
| `08_large_degree` | Cor. 3.2, boundary root counts (`b = 0, 1, 100`), (5.5) | `n = 60, 80, 100, 130, 160, 200` | 0.4 + 4 + 9 min |

A second complete run of checks `00`–`07` and `08` (`n = 60, 80, 100`) from the packaged directory via `run_all.sh` reproduced every summary exactly, timings aside. The `n = 130, 160, 200` runs were executed once.

Supplied scripts, inspected then run on a scratch copy (all exit 0):

| Script | Result | What it actually tests |
|---|---|---|
| A `verify_conventions.py` | pass | `S_n` enumeration `n <= 7`; `P_3` discriminant and boundary square |
| A `check_proof_identities.py` | pass | (5.4), `N` decomposition, pair formula, one-term (3.5), Cayley recurrence `n <= 12`; **not** residue positivity |
| A `verify_hybrid_proof.py` | pass (279 + 22 cases) | sign pattern at the hybrid test points, `m = 2..12`, 8–9 values of `b`, `c` at 0, 1/2, 1 times the bound |
| B `check_identities.py` | pass | B's identities `m <= 10`; 40 root counts on B's boundary |
| B `exact_reduction_checks.py` | pass; regenerated JSON identical to the supplied one except the Python version field | certificates `m = 2..15`, `n = 4` discriminant |
| B `review_exact_reduction.py` | pass | re-audit of the stored certificates |
| B `one_step_counterexample.py` | pass; JSON identical | the obstruction |

Source checks:

* Athanasiadis, arXiv:2302.00754v5 (HTML fetched): same convention (`A_0 = A_1 = 1`, `A_2 = 1+x`, `A_3 = 1+4x+x^2`); Example 3.3 states real-rootedness of `aA_n + bA_{n-1} + cA_{n-2}` whenever `a >= b-c >= c >= 0`, which at `a = 1` is the packet's baseline `1 >= b-c >= c >= 0`. Both candidates' regions contain it.
* Ma, "The Eulerian Combinations" (ResearchGate): not retrievable. Its Corollary 1 and Theorem 5 were **not** checked. No verdict relies on them.

---

## 8. Verification limits

* The proofs were read and re-derived by an AI model, supported by exact finite computation. Nothing was formalised in a proof assistant, and no human mathematician has reviewed this audit.
* Parameter coverage in the computations is by rational samples, except the certificate route of 4.4 (all real parameters, `4 <= n <= 42`) and `n = 3`, `n = 4` (symbolic). The all-degree, all-real-parameter statement rests on the reconstruction in section 3.
* The tangent-number inequality in the auditor's remark is quoted, not re-proved.
* One external reference was unreachable (above).
* Novelty and priority are out of scope.

---

## 9. Reproduction

```
python3 -m venv venv
./venv/bin/python -m pip install sympy==1.14.0 mpmath==1.3.0 python-flint==0.9.0
./run_all.sh /path/to/extracted/eulerian-cross-vendor-review      # packet path optional
./venv/bin/python -I checks/08_large_degree.py 130 160             # ~4 min
./venv/bin/python -I checks/08_large_degree.py 200                 # ~9 min
```

Supplied scripts (run on a copy, since several write next to themselves):

```
cp -r /path/to/extracted/eulerian-cross-vendor-review scratch/
for s in candidate_A/checks/verify_conventions.py candidate_A/checks/check_proof_identities.py \
         candidate_A/checks/verify_hybrid_proof.py candidate_B/proof_route/check_identities.py \
         candidate_B/eulerian_attempt/exact_reduction_checks.py \
         candidate_B/counterexample_search/review_exact_reduction.py \
         candidate_B/counterexample_search/one_step_counterexample.py; do
  ./venv/bin/python -I scratch/eulerian-cross-vendor-review/$s
done
```

`-I` runs Python in isolated mode so that nothing in the packet directory can shadow a library import.
