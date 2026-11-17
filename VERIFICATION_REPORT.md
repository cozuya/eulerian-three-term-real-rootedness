# Verification and statement correspondence

The reproducible entry point is `./verify.sh`. Its complete output is retained in
[evidence/verification.log](evidence/verification.log), with machine-readable metadata in
[evidence/verification.json](evidence/verification.json), the build output in
[evidence/build.log](evidence/build.log), and the exact theorem types and axiom reports in
[evidence/kernel-check.log](evidence/kernel-check.log).

## What the theorems say

The main theorem, in [EulerianRegion/MainTheorem.lean](EulerianRegion/MainTheorem.lean), as
printed by Lean:

```text
EulerianRegion.eulerian_three_term_realRooted_iff : ∀ (b c : ℝ), 0 ≤ b → 0 ≤ c →
  ((∀ (n : ℕ), 3 ≤ n → (EulerianRegion.combination n b c).Splits) ↔ c ≤ b ^ 2 / 4 + b + 3)
```

The names it uses:

- `EulerianRegion.A : ℕ → ℝ[X]` is defined by `A 0 = 1` and
  `A (n + 1) = (1 + C n * X) * A n + X * (1 - X) * derivative (A n)`
  ([Definitions.lean](EulerianRegion/Definitions.lean)). The project proves `A 1 = 1`,
  `A 2 = 1 + X`, `A 3 = 1 + 4X + X²` and `A 4 = 1 + 11X + 11X² + X³`.
- `EulerianRegion.combination n b c = A n + C b * A (n - 1) + C c * A (n - 2)`. It is used
  only for `n ≥ 3`, where the natural-number subtractions are exact.
- `Polynomial.Splits` is Mathlib's: the polynomial is a product of a constant and monic linear
  factors over `ℝ`, with multiplicities. For a nonzero polynomial this is equivalent to
  `p.roots.card = p.natDegree` (Mathlib's `splits_iff_card_roots`).
- The parameters `b, c` are arbitrary real numbers with `0 ≤ b`, `0 ≤ c`; the quantifier over
  `n ≥ 3` is inside the left side; the inequality is `≤`, so the boundary is included.

The project defines no replacement for any Mathlib notion, and the source audit rejects
notation, macros, instances and attributes that could alter them. The same statement is also
recorded as the proposition `EulerianRegion.PrimaryClaim`
([Statement.lean](EulerianRegion/Statement.lean)), proved as `primaryClaim_holds`; nothing
assumes it.

[Verification.lean](Verification.lean) imports the proof and restates the results without the
project's definitions. It assumes a sequence `P : ℕ → ℝ[X]` with
`P 0 = 1 ∧ ∀ n, P (n+1) = (1 + C n * X) * P n + X * (1 - X) * derivative (P n)`
(`IsEulerian P`) and proves:

| Declaration | Statement |
| --- | --- |
| `EulerianThreeTermVerification.real_rooted_iff` | for real `b, c ≥ 0`: `P n + C b * P (n-1) + C c * P (n-2)` splits for every `n ≥ 3` iff `c ≤ b^2/4 + b + 3` |
| `EulerianThreeTermVerification.real_rooted_strong` | if moreover `c ≤ b^2/4 + b + 3` and `n ≥ 3`, that polynomial is monic, splits, and has `natDegree = n - 1` and `roots.card = n - 1` |
| `EulerianThreeTermVerification.degree_three_iff` | for **all** real `b, c`: `P 3 + C b * P 2 + C c * P 1` splits iff `c ≤ b^2/4 + b + 3` |
| `EulerianThreeTermVerification.degree_three_boundary` | `P 3 + C b * P 2 + C (b^2/4 + b + 3) * P 1 = (X + C (b/2 + 2))^2` |
| `EulerianThreeTermVerification.boundary_example` | for `(b, c) = (1, 17/4)`, on the boundary, every `n ≥ 3` splits |
| `EulerianThreeTermVerification.outside_example` | for `(b, c) = (1, 5)`, not every `n ≥ 3` splits |
| `EulerianThreeTermVerification.sequence_exists` | some `P` satisfies `IsEulerian`, with `P 1 = 1`, `P 2 = 1 + X`, `P 3 = 1 + 4X + X²`, `P 4 = 1 + 11X + 11X² + X³` |

The last shows that the hypothesis is satisfiable, so the other statements are not vacuous.
There are no other hypotheses.

## Trust model

`./verify.sh` audits the printed axioms of 23 declarations: the 7 restatements above, the
main theorem in both forms, `primaryClaim_holds`, and the decisive lemmas of each proof step
(`combination_splits`, `combination_three_splits_iff`, `combination_splits_of_branch`,
`combination_splits_b_zero_even`, `Cay_succ_eq_homog`, `residue_pos`,
`positive_partial_fractions`, `cor_3_2`, `lemma_4_1`, `central_identity`,
`Phat_signPattern`, `Rzero_signPattern`, `splits_of_homog`).

| Axioms | Declarations |
| --- | --- |
| `propext`, `Classical.choice`, `Quot.sound` only | all 23 |

`#print axioms` reports the transitive closure, including every Mathlib lemma used, so the
audit would detect `sorryAx`, `native_decide` (`Lean.ofReduceBool`, `Lean.trustCompiler`)
or any added axiom anywhere in the dependency chain. The theorems are therefore checked by
the Lean kernel alone, without trusting the Lean compiler.

The source scan rejects, outside comments, `sorry`, `admit`, `axiom` declarations,
`native_decide`, `unsafe`, `implemented_by`, `extern`, `csimp`, `opaque`, kernel-checking
options, instances, notation, macros and attributes other than `@[simp]` and `@[expose]` in
this project's 14 Lean files. `@[simp]` only adds lemmas to the simplifier, and `@[expose]`
only controls which definition bodies the module system exports; neither can change what the
kernel accepts. The scan does not cover Mathlib's sources; the axiom audit covers what the
theorems actually use.

The recorded run also replayed the proofs with `leanchecker`, the standalone checker shipped
with the pinned toolchain: once for all 13 project modules, and once with `--fresh` for the
full import closure of `EulerianRegion.MainTheorem`, including Mathlib, into a new kernel
environment. `leanchecker` uses the same kernel implementation as Lean itself, so the replay
guards against environment or elaboration problems, not against a kernel bug.

## Measured results

The recorded local run took place from 2026-11-17 00:04:29 to 00:07:48 UTC (3 min 19 s), with
`VERIFY_LEANCHECKER=1`. The machine was a WSL2 Linux host with 24 hardware threads and 23 GB
of RAM. Mathlib came from its prebuilt cache; every module of this project was compiled from
source.

| Step | Result |
| --- | --- |
| Pins, every locked dependency, source scan, inventory, 123 source hashes | PASS |
| `rm -rf .lake/build`, then `lake build EulerianRegion` | 1,930 jobs, exit 0, 18 s wall time; all 13 project modules compiled; no warnings |
| `lake env lean --trust=0 Verification.lean` | exit 0, no warnings or errors |
| Axiom audit | all 23 declarations exactly as expected |
| `leanchecker --verbose EulerianRegion` | all 13 project modules replayed, exit 0, 12 s |
| `leanchecker --verbose --fresh EulerianRegion.MainTheorem` | full import closure replayed into a fresh environment, exit 0, 167 s |
| Whole script | exit 0; 3 min 19 s wall time; 197 s user CPU; largest single-process resident size 2.7 GB |

The same Lean sources were also built, audited and replayed with `leanchecker` in the private
development repository, including a rerun at its exact final commit, with the same pins and
the same axiom reports.

## Commands

After installing the pinned compiler and fetching the locked dependencies, as described in
[REPRODUCE.md](REPRODUCE.md):

```sh
VERIFY_LEANCHECKER=1 ./verify.sh
python3 scripts/check-package.py
```

## Limits of what is verified

- Only the statements above are formalized. Simple roots, negative roots and the exact
  real-rooted region for a single degree are not. The informal proof of simplicity is in
  [original/](original/README.md).
- `A` is defined by the recurrence. Its description as the descent generating polynomial of
  the symmetric group is standard but not formalized; the correspondence rests on the
  recurrence and the checked small cases.
- Verification establishes the stated theorem. It does not establish historical priority;
  see [PRIOR_ART.md](PRIOR_ART.md).
