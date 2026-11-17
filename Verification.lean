import EulerianRegion

/-!
# Independent restatement of the verified results

The statements below use only Mathlib notions. Instead of the project's definitions, they
quantify over any sequence `P : ℕ → ℝ[X]` with `P 0 = 1` and
`P (n+1) = (1 + n x) P n + x(1-x) (P n)'`, the Eulerian polynomials.

`sequence_exists` shows that such a `P` exists and starts `1, 1, 1 + x, 1 + 4x + x²`, so the
hypothesis is not vacuous. Each statement is proved directly from the project's theorems.
`verify.sh` checks the printed types and transitive axioms below.
-/

open Polynomial

set_option autoImplicit false

namespace EulerianThreeTermVerification

/-- The Eulerian recurrence. -/
def IsEulerian (P : ℕ → ℝ[X]) : Prop :=
  P 0 = 1 ∧ ∀ n : ℕ, P (n + 1) = (1 + C (n : ℝ) * X) * P n + X * (1 - X) * derivative (P n)

theorem eq_A {P : ℕ → ℝ[X]} (hP : IsEulerian P) : P = EulerianRegion.A := by
  funext n
  induction n with
  | zero => exact hP.1
  | succ n ih => rw [hP.2, ih, EulerianRegion.A_succ]

/-- Such a sequence exists, and it starts `1, 1, 1 + x, 1 + 4x + x², 1 + 11x + 11x² + x³`. -/
theorem sequence_exists :
    ∃ P : ℕ → ℝ[X], IsEulerian P ∧ P 1 = 1 ∧ P 2 = 1 + X ∧ P 3 = 1 + C 4 * X + X ^ 2 ∧
      P 4 = 1 + C 11 * X + C 11 * X ^ 2 + X ^ 3 :=
  ⟨EulerianRegion.A, ⟨EulerianRegion.A_zero, EulerianRegion.A_succ⟩, EulerianRegion.A_one,
    EulerianRegion.A_two, EulerianRegion.A_three, EulerianRegion.A_four⟩

/-- **Main theorem.** For fixed real `b, c ≥ 0`, `P n + b P (n-1) + c P (n-2)` splits over `ℝ`
for every `n ≥ 3` if and only if `c ≤ b²/4 + b + 3`. -/
theorem real_rooted_iff {P : ℕ → ℝ[X]} (hP : IsEulerian P) (b c : ℝ) (hb : 0 ≤ b)
    (hc : 0 ≤ c) :
    (∀ n : ℕ, 3 ≤ n → (P n + C b * P (n - 1) + C c * P (n - 2)).Splits) ↔
      c ≤ b ^ 2 / 4 + b + 3 := by
  rw [eq_A hP]
  exact EulerianRegion.eulerian_three_term_realRooted_iff' b c hb hc

/-- Strong form inside the region: for every `n ≥ 3` the polynomial is monic of degree
`n - 1`, splits, and has `n - 1` real roots counted with multiplicity. -/
theorem real_rooted_strong {P : ℕ → ℝ[X]} (hP : IsEulerian P) {b c : ℝ} (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hbc : c ≤ b ^ 2 / 4 + b + 3) {n : ℕ} (hn : 3 ≤ n) :
    let p := P n + C b * P (n - 1) + C c * P (n - 2)
    p.Monic ∧ p.Splits ∧ p.natDegree = n - 1 ∧ p.roots.card = n - 1 := by
  rw [eq_A hP]
  intro p
  have hp : p = EulerianRegion.combination n b c := rfl
  have hs := EulerianRegion.combination_splits hb hc hbc hn
  have hd := EulerianRegion.combination_natDegree hn b c
  rw [hp]
  refine ⟨EulerianRegion.combination_monic hn b c, hs, hd, ?_⟩
  rw [← hd]
  exact splits_iff_card_roots.mp hs

/-- Necessity comes from `n = 3` alone: for all real `b, c` (no sign condition),
`P 3 + b P 2 + c P 1` splits over `ℝ` if and only if `c ≤ b²/4 + b + 3`. -/
theorem degree_three_iff {P : ℕ → ℝ[X]} (hP : IsEulerian P) (b c : ℝ) :
    (P 3 + C b * P 2 + C c * P 1).Splits ↔ c ≤ b ^ 2 / 4 + b + 3 := by
  rw [eq_A hP]
  exact EulerianRegion.combination_three_splits_iff b c

/-- On the boundary `c = b²/4 + b + 3`, the degree-3 polynomial is the square
`(x + b/2 + 2)²`. -/
theorem degree_three_boundary {P : ℕ → ℝ[X]} (hP : IsEulerian P) (b : ℝ) :
    P 3 + C b * P 2 + C (b ^ 2 / 4 + b + 3) * P 1 = (X + C (b / 2 + 2)) ^ 2 := by
  rw [eq_A hP]
  exact EulerianRegion.combination_three_boundary b

/-- A boundary point: `(b, c) = (1, 17/4)` gives a real-rooted polynomial in every degree. -/
theorem boundary_example {P : ℕ → ℝ[X]} (hP : IsEulerian P) :
    ∀ n : ℕ, 3 ≤ n → (P n + C 1 * P (n - 1) + C (17 / 4) * P (n - 2)).Splits :=
  (real_rooted_iff hP 1 (17 / 4) (by norm_num) (by norm_num)).mpr (by norm_num)

/-- Just outside: for `(b, c) = (1, 5)` some polynomial in the family is not real-rooted. -/
theorem outside_example {P : ℕ → ℝ[X]} (hP : IsEulerian P) :
    ¬ ∀ n : ℕ, 3 ≤ n → (P n + C 1 * P (n - 1) + C 5 * P (n - 2)).Splits := by
  rw [real_rooted_iff hP 1 5 (by norm_num) (by norm_num)]
  norm_num

end EulerianThreeTermVerification

#check @EulerianThreeTermVerification.real_rooted_iff
#check @EulerianThreeTermVerification.real_rooted_strong
#check @EulerianThreeTermVerification.degree_three_iff
#check @EulerianThreeTermVerification.degree_three_boundary
#check @EulerianThreeTermVerification.boundary_example
#check @EulerianThreeTermVerification.outside_example
#check @EulerianThreeTermVerification.sequence_exists
#check @EulerianRegion.eulerian_three_term_realRooted_iff
#print EulerianRegion.A
#print EulerianRegion.combination
#print EulerianRegion.PrimaryClaim

#print axioms EulerianThreeTermVerification.real_rooted_iff
#print axioms EulerianThreeTermVerification.real_rooted_strong
#print axioms EulerianThreeTermVerification.degree_three_iff
#print axioms EulerianThreeTermVerification.degree_three_boundary
#print axioms EulerianThreeTermVerification.boundary_example
#print axioms EulerianThreeTermVerification.outside_example
#print axioms EulerianThreeTermVerification.sequence_exists
#print axioms EulerianRegion.eulerian_three_term_realRooted_iff
#print axioms EulerianRegion.eulerian_three_term_realRooted_iff'
#print axioms EulerianRegion.primaryClaim_holds
#print axioms EulerianRegion.combination_splits
#print axioms EulerianRegion.combination_three_splits_iff
#print axioms EulerianRegion.combination_splits_of_branch
#print axioms EulerianRegion.combination_splits_b_zero_even
#print axioms EulerianRegion.Cay_succ_eq_homog
#print axioms EulerianRegion.residue_pos
#print axioms EulerianRegion.positive_partial_fractions
#print axioms EulerianRegion.cor_3_2
#print axioms EulerianRegion.lemma_4_1
#print axioms EulerianRegion.central_identity
#print axioms EulerianRegion.Phat_signPattern
#print axioms EulerianRegion.Rzero_signPattern
#print axioms EulerianRegion.splits_of_homog
