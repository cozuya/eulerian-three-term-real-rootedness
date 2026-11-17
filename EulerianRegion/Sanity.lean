module

public import EulerianRegion.Statement
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Statement sanity checks

Kernel-checked facts about the frozen definitions:

* the small Eulerian polynomials `A 1, …, A 4`;
* the coefficient recurrence, and `A (j + 1)` monic of degree `j`;
* `P_n = combination n b c` monic of degree `n - 1` for `n ≥ 3`;
* `P_3 = x² + (b + 4) x + (1 + b + c)` and the boundary square `(x + b/2 + 2)²`;
* the degree-3 equivalence `P_3` splits `↔ c ≤ b²/4 + b + 3` (all real `b, c`), which is the
  necessity direction of the primary claim;
* a negative control `(b, c) = (0, 4)` and a boundary example `(b, c) = (0, 3)`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace EulerianRegion

theorem A_one : A 1 = 1 := by
  simp [A_succ]

theorem A_two : A 2 = 1 + X := by
  rw [A_succ, A_one]; simp

theorem A_three : A 3 = 1 + C 4 * X + X ^ 2 := by
  rw [A_succ, A_two]
  simp only [derivative_add, derivative_one, derivative_X, zero_add, Nat.cast_ofNat]
  rw [show (C (4 : ℝ)) = 4 by simp [map_ofNat], show (C (2 : ℝ)) = 2 by simp [map_ofNat]]
  ring

theorem A_four : A 4 = 1 + C 11 * X + C 11 * X ^ 2 + X ^ 3 := by
  rw [A_succ, A_three]
  simp only [derivative_add, derivative_one, derivative_mul, derivative_C, derivative_X,
    derivative_X_pow, zero_add, zero_mul, mul_one, Nat.cast_ofNat]
  rw [show (C (11 : ℝ)) = 11 by simp [map_ofNat], show (C (4 : ℝ)) = 4 by simp [map_ofNat],
    show (C (3 : ℝ)) = 3 by simp [map_ofNat]]
  simp only [map_ofNat]
  ring

/-- Coefficient recurrence `e_{j+1,k+1} = (k+2) e_{j,k+1} + (j-k) e_{j,k}`. -/
theorem coeff_A_succ_succ (j k : ℕ) :
    (A (j + 1)).coeff (k + 1) =
      ((k : ℝ) + 2) * (A j).coeff (k + 1) + ((j : ℝ) - k) * (A j).coeff k := by
  rw [A_succ]
  have h1 : ((1 + C (j : ℝ) * X) * A j).coeff (k + 1) =
      (A j).coeff (k + 1) + (j : ℝ) * (A j).coeff k := by
    rw [add_mul, one_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul]
  have h2 : (X * (1 - X) * derivative (A j)).coeff (k + 1) =
      ((k : ℝ) + 1) * (A j).coeff (k + 1) - (k : ℝ) * (A j).coeff k := by
    rw [mul_sub, mul_one, sub_mul, coeff_sub, coeff_X_mul,
      show X * X * derivative (A j) = X * (X * derivative (A j)) by ring, coeff_X_mul,
      coeff_derivative]
    cases k with
    | zero => simp
    | succ k =>
      rw [coeff_X_mul, coeff_derivative]
      push_cast
      ring
  rw [coeff_add, h1, h2]
  ring

theorem coeff_A_succ_zero (j : ℕ) : (A (j + 1)).coeff 0 = (A j).coeff 0 := by
  rw [A_succ]
  simp [coeff_add, mul_assoc, add_mul]

/-- `A (j + 1)` has degree at most `j` and its coefficient of `x^j` is `1`. -/
theorem A_succ_degree_and_lead (j : ℕ) :
    (∀ k, j < k → (A (j + 1)).coeff k = 0) ∧ (A (j + 1)).coeff j = 1 := by
  induction j with
  | zero => simp [A_one, coeff_one]; intro k hk; omega
  | succ j ih =>
    obtain ⟨hz, hl⟩ := ih
    refine ⟨fun k hk => ?_, ?_⟩
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [coeff_A_succ_succ, hz (k + 1) (by omega), hz k (by omega)]
      ring
    · rw [coeff_A_succ_succ, hz (j + 1) (by omega), hl]
      push_cast
      ring

theorem natDegree_A_succ (j : ℕ) : (A (j + 1)).natDegree = j := by
  obtain ⟨hz, hl⟩ := A_succ_degree_and_lead j
  apply le_antisymm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    exact hz k (by exact_mod_cast hk)
  · apply le_natDegree_of_ne_zero
    rw [hl]; exact one_ne_zero

theorem monic_A_succ (j : ℕ) : (A (j + 1)).Monic := by
  rw [Monic, leadingCoeff, natDegree_A_succ]
  exact (A_succ_degree_and_lead j).2

theorem A_ne_zero (n : ℕ) : A n ≠ 0 := by
  cases n with
  | zero => simp
  | succ n => exact (monic_A_succ n).ne_zero

theorem degree_C_mul_le' (a : ℝ) (p : ℝ[X]) : (C a * p).degree ≤ p.degree := by
  rw [← smul_eq_C_mul]; exact degree_smul_le a p

/-- For `n ≥ 3`, `P_n` is monic. -/
theorem combination_monic {n : ℕ} (hn : 3 ≤ n) (b c : ℝ) : (combination n b c).Monic := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  unfold combination
  have hA : (A (k + 3)).Monic := monic_A_succ (k + 2)
  have hdeg3 : (A (k + 3)).degree = ((k + 2 : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree (A_ne_zero _), natDegree_A_succ]
  have hlt1 : (C b * A (k + 3 - 1)).degree < (A (k + 3)).degree := by
    rw [hdeg3, show k + 3 - 1 = (k + 1) + 1 by omega]
    refine lt_of_le_of_lt (degree_C_mul_le' _ _) ?_
    rw [degree_eq_natDegree (A_ne_zero _), natDegree_A_succ]
    exact_mod_cast (by omega : k + 1 < k + 2)
  have hlt2 : (C c * A (k + 3 - 2)).degree < (A (k + 3)).degree := by
    rw [hdeg3, show k + 3 - 2 = k + 1 by omega]
    refine lt_of_le_of_lt (degree_C_mul_le' _ _) ?_
    rw [degree_eq_natDegree (A_ne_zero _), natDegree_A_succ]
    exact_mod_cast (by omega : k < k + 2)
  have h1 : (A (k + 3) + C b * A (k + 3 - 1)).Monic := hA.add_of_left hlt1
  refine h1.add_of_left ?_
  rwa [degree_add_eq_left_of_degree_lt hlt1]

/-- For `n ≥ 3`, `P_n` has degree `n - 1`. -/
theorem combination_natDegree {n : ℕ} (hn : 3 ≤ n) (b c : ℝ) :
    (combination n b c).natDegree = n - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  unfold combination
  have hdeg : ∀ j, (A (j + 1)).degree = (j : WithBot ℕ) := fun j => by
    rw [degree_eq_natDegree (A_ne_zero _), natDegree_A_succ]
  have hlt1 : (C b * A (k + 3 - 1)).degree < (A (k + 3)).degree := by
    rw [show k + 3 - 1 = (k + 1) + 1 by omega, show k + 3 = (k + 2) + 1 by omega, hdeg]
    refine lt_of_le_of_lt (degree_C_mul_le' _ _) ?_
    rw [hdeg]; exact_mod_cast (by omega : k + 1 < k + 2)
  have hlt2 : (C c * A (k + 3 - 2)).degree < (A (k + 3) + C b * A (k + 3 - 1)).degree := by
    rw [degree_add_eq_left_of_degree_lt hlt1, show k + 3 - 2 = k + 1 by omega,
      show k + 3 = (k + 2) + 1 by omega, hdeg]
    refine lt_of_le_of_lt (degree_C_mul_le' _ _) ?_
    rw [hdeg]; exact_mod_cast (by omega : k < k + 2)
  rw [natDegree_add_eq_left_of_degree_lt hlt2, natDegree_add_eq_left_of_degree_lt hlt1,
    show k + 3 = (k + 2) + 1 by omega, natDegree_A_succ]
  omega

/-- `P_3 = x² + (b + 4) x + (1 + b + c)`. -/
theorem combination_three (b c : ℝ) :
    combination 3 b c = X ^ 2 + C (b + 4) * X + C (1 + b + c) := by
  unfold combination
  simp only [show 3 - 1 = 2 by rfl, show 3 - 2 = 1 by rfl, A_three, A_two, A_one, map_add,
    map_one]
  ring

/-- On the boundary `c = b²/4 + b + 3`, `P_3 = (x + b/2 + 2)²`. -/
theorem combination_three_boundary (b : ℝ) :
    combination 3 b (b ^ 2 / 4 + b + 3) = (X + C (b / 2 + 2)) ^ 2 := by
  rw [combination_three]
  have h : (C (1 + b + (b ^ 2 / 4 + b + 3)) : ℝ[X]) = C (b / 2 + 2) ^ 2 := by
    rw [← map_pow]; congr 1; ring
  rw [h, show (C (b + 4) : ℝ[X]) = 2 * C (b / 2 + 2) by
    rw [show (2 : ℝ[X]) = C 2 by simp [map_ofNat], ← map_mul]; congr 1; ring]
  ring

/-- A real monic quadratic `x² + p x + q` splits over `ℝ` iff `4 q ≤ p²`. -/
theorem splits_quadratic_iff (p q : ℝ) :
    (X ^ 2 + C p * X + C q : ℝ[X]).Splits ↔ 4 * q ≤ p ^ 2 := by
  have hdeg : (X ^ 2 + C p * X + C q : ℝ[X]).natDegree = 2 := by compute_degree!
  have heval : ∀ x : ℝ, (X ^ 2 + C p * X + C q : ℝ[X]).eval x = 1 * (x * x) + p * x + q := by
    intro x; simp; ring
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero (by
      rw [degree_eq_natDegree (by intro h; simp [h] at hdeg), hdeg]; decide)
    rw [heval] at hx
    have := discrim_eq_sq_of_quadratic_eq_zero hx
    unfold discrim at this
    nlinarith [sq_nonneg (2 * 1 * x + p)]
  · intro h
    have hd : 0 ≤ discrim 1 p q := by unfold discrim; linarith
    obtain ⟨s, hs⟩ : ∃ s, discrim 1 p q = s * s :=
      ⟨Real.sqrt (discrim 1 p q), (Real.mul_self_sqrt hd).symm⟩
    have hroot : 1 * ((-p + s) / (2 * 1) * ((-p + s) / (2 * 1))) + p * ((-p + s) / (2 * 1)) + q
        = 0 := by
      exact (quadratic_eq_zero_iff one_ne_zero hs _).mpr (Or.inl rfl)
    refine Splits.of_natDegree_eq_two hdeg (x := (-p + s) / (2 * 1)) ?_
    rw [heval]; exact hroot

/-- The degree-three case of the primary claim, for arbitrary real `b, c`:
`P_3` splits over `ℝ` iff `c ≤ b²/4 + b + 3` (discriminant `b² + 4b + 12 - 4c`). -/
theorem combination_three_splits_iff (b c : ℝ) :
    (combination 3 b c).Splits ↔ c ≤ b ^ 2 / 4 + b + 3 := by
  rw [combination_three, splits_quadratic_iff]
  constructor <;> intro h <;> nlinarith

/-- Negative control: `P_3(·; 0, 4) = x² + 4x + 5` does not split over `ℝ`. -/
theorem combination_three_zero_four_not_splits : ¬ (combination 3 0 4).Splits := by
  rw [combination_three_splits_iff]; norm_num

/-- Boundary example: `P_3(·; 0, 3) = (x + 2)²` splits over `ℝ`. -/
theorem combination_three_zero_three :
    combination 3 0 3 = (X + C 2) ^ 2 ∧ (combination 3 0 3).Splits := by
  have h := combination_three_boundary 0
  norm_num at h
  refine ⟨h, ?_⟩
  rw [h]
  exact (Splits.X_add_C 2).pow 2

end EulerianRegion
