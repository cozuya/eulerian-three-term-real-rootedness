module

public import EulerianRegion.BoundaryZero

/-!
# The main theorem

For fixed real `b, c ≥ 0`:

`(∀ n : ℕ, 3 ≤ n → (combination n b c).Splits) ↔ c ≤ b ^ 2 / 4 + b + 3`

(`eulerian_three_term_realRooted_iff`), i.e. `PrimaryClaim` holds (`primaryClaim_holds`).

* Necessity: `n = 3` only (`combination_three_splits_iff`, discriminant `b² + 4b + 12 - 4c`).
* Sufficiency (`combination_splits`): `n = 3` by the discriminant; `n ≥ 4` by Cases I–II
  (`combination_splits_of_branch`, `b > 0` or `n` odd) and Case III
  (`combination_splits_b_zero_even`, `b = 0` and `n` even).

`eulerian_three_term_realRooted_iff'` states the same with `combination` unfolded.  The `example`s
are regressions: boundary points `(0, 3)` and `(2, 6)`, the even-`b = 0` top case, and the negative
control `(0, 4)`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace EulerianRegion

/-- **Sufficiency** for every `n ≥ 3`: if `0 ≤ b`, `0 ≤ c` and `c ≤ b²/4 + b + 3`, then
`P_n = A_n + b A_{n-1} + c A_{n-2}` splits over `ℝ`.  `n = 3`: the discriminant; `n ≥ 4`: Cases I–II
(`combination_splits_of_branch`) when `b > 0` or `n` is odd, and Case III
(`combination_splits_b_zero_even`) when `b = 0` and `n` is even. -/
theorem combination_splits {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hbc : c ≤ b ^ 2 / 4 + b + 3)
    {n : ℕ} (hn : 3 ≤ n) : (combination n b c).Splits := by
  rcases Nat.lt_or_ge n 4 with h3 | h4
  · obtain rfl : n = 3 := by omega
    exact (combination_three_splits_iff b c).mpr hbc
  · rcases lt_or_eq_of_le hb with hbpos | hb0
    · exact combination_splits_of_branch hb hc hbc h4 (Or.inl hbpos)
    · subst hb0
      rcases Nat.even_or_odd n with he | ho
      · exact combination_splits_b_zero_even hc (by linarith) h4 he
      · exact combination_splits_of_branch le_rfl hc hbc h4 (Or.inr ho)

/-- **Main theorem.**  For fixed real `b, c ≥ 0`, the polynomials
`P_n(x; b, c) = A_n(x) + b A_{n-1}(x) + c A_{n-2}(x)` split over `ℝ` for every `n ≥ 3` if and only if
`c ≤ b²/4 + b + 3`.  Necessity comes from `n = 3` alone. -/
theorem eulerian_three_term_realRooted_iff (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (∀ n : ℕ, 3 ≤ n → (combination n b c).Splits) ↔ c ≤ b ^ 2 / 4 + b + 3 := by
  constructor
  · intro h
    exact (combination_three_splits_iff b c).mp (h 3 le_rfl)
  · intro hbc n hn
    exact combination_splits hb hc hbc hn

/-- The frozen `PrimaryClaim` holds. -/
theorem primaryClaim_holds : PrimaryClaim :=
  fun b c hb hc => eulerian_three_term_realRooted_iff b c hb hc

/-- The main theorem with `combination` unfolded (original notation). -/
theorem eulerian_three_term_realRooted_iff' (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (∀ n : ℕ, 3 ≤ n → (A n + C b * A (n - 1) + C c * A (n - 2)).Splits) ↔
      c ≤ b ^ 2 / 4 + b + 3 :=
  eulerian_three_term_realRooted_iff b c hb hc

/-! ### Regressions -/

/-- Boundary of the region, all degrees: `(b, c) = (0, 3)`. -/
example : ∀ n : ℕ, 3 ≤ n → (combination n 0 3).Splits :=
  (eulerian_three_term_realRooted_iff 0 3 le_rfl (by norm_num)).mpr (by norm_num)

/-- Boundary of the region, all degrees: `(b, c) = (2, 1 + 2 + 3) = (2, 6)`. -/
example : ∀ n : ℕ, 3 ≤ n → (combination n 2 6).Splits :=
  (eulerian_three_term_realRooted_iff 2 6 (by norm_num) (by norm_num)).mpr (by norm_num)

/-- Negative control: `(b, c) = (0, 4)` is outside the region, and some `P_n` does not split. -/
example : ¬ ∀ n : ℕ, 3 ≤ n → (combination n 0 4).Splits := by
  rw [eulerian_three_term_realRooted_iff 0 4 le_rfl (by norm_num)]; norm_num

/-- Even degree, `b = 0`, top of the range: `P_4(·; 0, 3)` splits. -/
example : (combination 4 0 3).Splits := combination_splits le_rfl (by norm_num) (by norm_num) (by norm_num)

end EulerianRegion
