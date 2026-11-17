module

public import EulerianRegion.Sufficiency

/-!
# The boundary case `b = 0`, `n` even (A §6 Case III)

Candidate A handles `b = 0`, `n` even by a fixed-degree limit `b_j → 0⁺`, and the assignment's §4.5
and batch B09 describe that limit route.  The assignment's §1 ("Explicit scope exclusions") says:
"Follow A's fixed-degree limit route unless a fully proved alternative is demonstrably simpler."  This
file uses such an alternative, which departs from §4.5/B09: it needs no limit, topology, or
root-continuity theory, only the sign-count machinery already used for Cases I–II:

* For `b = 0` and `n = k + 3` even (`k` odd), `f = C_{k+1}` and `h = C_{k+3}` are odd, so
  `P̂(0) = h(0) + c f(0) = 0` (`Phat_zero_eval_zero`) and `P̂ = z · R` with `R = P̂ / z`
  (`X_mul_Rzero`, `Rzero_degree`: degree `k + 1`, positive leading coefficient).
* On the Case II test points with `0` removed (`(hybridSet 0 k).erase 0`, `k + 2` points), `R`
  has strictly alternating signs (`Rzero_signPattern`): at a test point `t ≠ 0`, `R(t) = P̂(t)/t`, and
  removing `0` lowers the count of test points above every negative point by one, which exactly
  compensates the sign flip of `1/t` for `t < 0`.  The signs of `P̂` used are A (5.5) and (5.6) with
  `b = 0` (`Phat_sign_neg_sep`, `Phat_sign_nonneg_f` with `r > 0`), valid for `0 ≤ c ≤ 3`.
* Hence `R` splits, `P̂ = z R` splits, and `splits_of_homog` transports this to `P_n`
  (`combination_splits_b_zero_even`).

Only splitting (with multiplicity) is concluded: `P̂` may have a double root at `z = 0`
(`x = -1`).  No simplicity claim and no tangent-number bound are used.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace EulerianRegion


theorem above_erase_val {L : Finset ℝ} {a : ℝ} (ha : a ∈ L) (t : ℝ) :
    above (L.erase a).val t + (if t < a then 1 else 0) = above L.val t := by
  conv_rhs => rw [← Finset.insert_erase ha]
  rw [above_insert_val (Finset.notMem_erase a L)]

/-- `R = P̂ / z` for `b = 0` and odd `k` (`n = k + 3` even). -/
def Rzero (c : ℝ) (k : ℕ) : ℝ[X] := cof (Phat 0 c k) 0

theorem Phat_zero_eval_zero (c : ℝ) {k : ℕ} (hk : Odd k) : (Phat 0 c k).eval 0 = 0 := by
  rw [eval_Phat, Cay_eval_zero_of_odd hk,
    show k + 3 = (k + 2) + 1 by ring,
    Cay_eval_zero_of_odd (by obtain ⟨j, hj⟩ := hk; exact ⟨j + 1, by omega⟩)]
  ring

theorem X_mul_Rzero (c : ℝ) {k : ℕ} (hk : Odd k) : X * Rzero c k = Phat 0 c k := by
  have := cof_mul (D := Phat 0 c k) (s := 0) (Phat_zero_eval_zero c hk)
  simpa [Rzero] using this

theorem eval_Rzero (c : ℝ) {k : ℕ} (hk : Odd k) {t : ℝ} (ht : t ≠ 0) :
    (Rzero c k).eval t = (Phat 0 c k).eval t / t := by
  rw [Rzero, eval_cof (Phat_zero_eval_zero c hk) ht, sub_zero]

theorem Rzero_degree {c : ℝ} (hc : 0 ≤ c) {k : ℕ} (hk : Odd k) :
    (Rzero c k).natDegree = k + 1 ∧ 0 < (Rzero c k).leadingCoeff := by
  obtain ⟨hd, hl⟩ := Phat_degree le_rfl hc k
  have hX := X_mul_Rzero c hk
  have hR0 : Rzero c k ≠ 0 := by
    intro h; rw [h, mul_zero] at hX
    have := congrArg leadingCoeff hX; rw [leadingCoeff_zero] at this; linarith
  constructor
  · have := congrArg natDegree hX
    rw [natDegree_mul X_ne_zero hR0, natDegree_X, hd] at this
    omega
  · have := congrArg leadingCoeff hX
    rw [leadingCoeff_mul, leadingCoeff_X, one_mul] at this
    rw [this]; exact hl

/-- Case III sign pattern on `hybridSet 0 k \ {0}`. -/
theorem Rzero_signPattern {c : ℝ} (hc : 0 ≤ c) (hc3 : c ≤ 3) {k : ℕ} (hk : Odd k) :
    SignPattern (Rzero c k) ((hybridSet 0 k).erase 0) := by
  have hk1 : 1 ≤ k := by obtain ⟨j, hj⟩ := hk; omega
  obtain ⟨hcard, hm1, h1, hneg, hnn⟩ := hybridSet_counts (le_refl (0 : ℝ)) k
  have hf0 : (Cay (k + 1)).eval 0 = 0 := Cay_eval_zero_of_odd hk
  have h0f : (0 : ℝ) ∈ (Cay (k + 1)).roots := (mem_roots (Cay_ne_zero k)).mpr hf0
  have h0L : (0 : ℝ) ∈ hybridSet 0 k := mem_hybridSet.mpr (Or.inr (Or.inr (Or.inr ⟨h0f, le_rfl⟩)))
  obtain ⟨hRd, hRl⟩ := Rzero_degree hc hk
  have hbc : c ≤ (0 : ℝ) ^ 2 / 4 + 0 + 3 := by linarith
  refine ⟨hRl, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem h0L, hcard, hRd]
    omega
  · intro t ht
    obtain ⟨ht0, htL⟩ := Finset.mem_erase.mp ht
    have hab := above_erase_val h0L t
    rw [eval_Rzero c hk ht0]
    rcases mem_hybridSet.mp htL with rfl | rfl | ⟨hsq, hs0⟩ | ⟨hrf, hr0⟩
    · rw [ite_eq_left (by norm_num), hm1] at hab
      rw [show above ((hybridSet 0 k).erase 0).val (-1) = k + 1 by omega, eval_neg_one_Phat,
        div_neg, div_one]
      have hsq : ((-1 : ℝ) ^ (k + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have h2 : (-2 : ℝ) ^ (k + 2) = -((-1) ^ (k + 1) * 2 ^ (k + 2)) := by
        rw [show (-2 : ℝ) = (-1) * 2 by norm_num, mul_pow]; ring
      rw [h2]
      nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) (k + 2)]
    · rw [ite_eq_right (by norm_num), h1, add_zero] at hab
      rw [hab, pow_zero, one_mul, div_one]
      exact eval_one_Phat le_rfl hc k
    · rw [ite_eq_left hs0, hneg t hsq hs0] at hab
      have hcnt : above ((hybridSet 0 k).erase 0).val t = above (Cay (k + 1)).roots t := by omega
      rw [hcnt]
      have hs := Phat_sign_neg_sep (c := c) le_rfl hbc hk1 hsq hs0
      rw [pow_succ] at hs
      have : (-1 : ℝ) ^ above (Cay (k + 1)).roots t * (Phat 0 c k).eval t < 0 := by nlinarith
      rw [mul_div_assoc']
      exact div_pos_of_neg_of_neg this hs0
    · have hrpos : 0 < t := lt_of_le_of_ne hr0 (Ne.symm ht0)
      rw [ite_eq_right (not_lt.mpr hr0), add_zero, hnn t hrf hr0] at hab
      rw [hab, mul_div_assoc']
      exact div_pos (Phat_sign_nonneg_f (c := c) le_rfl hrf hr0 (Or.inl hrpos)) hrpos

/-- **Sufficiency for `b = 0`, `n ≥ 4` even** (A §6 Case III, by the factor-`z` route). -/
theorem combination_splits_b_zero_even {c : ℝ} (hc : 0 ≤ c) (hc3 : c ≤ 3) {n : ℕ} (hn : 4 ≤ n)
    (heven : Even n) : (combination n 0 c).Splits := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hk : Odd k := by
    obtain ⟨j, hj⟩ := heven
    exact ⟨j - 2, by omega⟩
  have hR := (Rzero_signPattern hc hc3 hk).splits
  have hP : (Phat 0 c k).Splits := by
    rw [← X_mul_Rzero c hk]
    exact (Splits.X : (X : ℝ[X]).Splits).mul hR
  have hdeg := (Phat_degree le_rfl hc k).1
  rw [← homog_combination] at hP hdeg
  apply splits_of_homog (d := k + 2) (by rw [combination_natDegree (by omega)]; omega) hP hdeg
  rw [homog_combination, eval_neg_one_Phat]
  exact pow_ne_zero _ (by norm_num)

end EulerianRegion
