module

public import EulerianRegion.Cayley

/-!
# Finite partial fractions and critical-point identities

Machinery for A Lemma 3.1 (audit §3.2), stated for a denominator `D` that splits over `ℝ` with simple
roots and positive leading coefficient, and a numerator `N` with `natDegree N ≤ natDegree D`.
No analytic residue theory is used: the "residues" are the finite real numbers `κ_s = N(s)/D'(s)`.

* `pf_identity` (polynomial identity, Lagrange form):
  `N = c·D + Σ_{s root} κ_s · D/(X - s)`, `c = [x^d]N / lc D` (`d = natDegree D`).
* `pf_eval`: `N(z) = D(z) (c + Σ κ_s/(z - s))` for `D(z) ≠ 0` (no evaluation at a pole).
* At a critical point `ξ` of `D` with `D(ξ) ≠ 0`: `pf_derivative_at_critical`
  (`N'(ξ) = -D(ξ) Σ κ_s/(ξ - s)²`) and `T_at_critical`
  (`(T N)(ξ) = D(ξ) (2ξc + Σ κ_s (1 + (1 - s²)/(ξ - s)²))`).
* Pairing `s ↔ -s` for symmetric poles with odd residues: `sum_critical_symm`
  (`Σ κ_s (1 + (1-s²)/(ξ-s)²) = ξ Σ 2 s κ_s (1-s²)/(ξ²-s²)²`), the conversion
  `residue_pair` (`κ/(z-s) - κ/(z+s) = 2sκ/(z²-s²)`), and the paired expansion
  `sum_residue_paired` (`Σ_s κ_s/(z-s) = Σ_{s>0} 2 s κ_s/(z² - s²)`; a pole at `0` drops out of the
  paired sum because its paired term carries the factor `s`).  `residue_zero_of_eval_zero` only
  records the trivial fact that `κ_0 = N(0)/D'(0) = 0` when `N(0) = 0`.
* A (3.3): `critical_second_derivative_div` (`D''(ξ)/D(ξ) = -Σ (ξ - s)⁻²`) and
  `critical_second_derivative_mul_neg` (`D''(ξ) D(ξ) < 0`).
-/

@[expose] public section

open Polynomial

noncomputable section

namespace EulerianRegion

/-! ### Finite partial fractions for a denominator with simple real roots -/

/-- The cofactor `D / (X - s)`; it is a polynomial when `s` is a root. -/
abbrev cof (D : ℝ[X]) (s : ℝ) : ℝ[X] := D /ₘ (X - C s)

theorem cof_mul {D : ℝ[X]} {s : ℝ} (hs : D.IsRoot s) : (X - C s) * cof D s = D :=
  mul_divByMonic_eq_iff_isRoot.mpr hs

theorem eval_cof_self {D : ℝ[X]} {s : ℝ} (hs : D.IsRoot s) :
    (cof D s).eval s = (derivative D).eval s := by
  conv_rhs => rw [← cof_mul hs]
  simp [derivative_mul]

theorem eval_cof_of_ne {D : ℝ[X]} {s t : ℝ} (hs : D.IsRoot s) (ht : D.IsRoot t) (hst : s ≠ t) :
    (cof D s).eval t = 0 := by
  have h := congrArg (eval t) (cof_mul hs)
  rw [eval_mul, ht.eq_zero] at h
  simp only [eval_sub, eval_X, eval_C] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hst.symm)

theorem eval_cof {D : ℝ[X]} {s z : ℝ} (hs : D.IsRoot s) (hz : z ≠ s) :
    (cof D s).eval z = D.eval z / (z - s) := by
  have h := congrArg (eval z) (cof_mul hs)
  simp only [eval_mul, eval_sub, eval_X, eval_C] at h
  rw [← h]; field_simp [sub_ne_zero.mpr hz]

/-- At a critical point `ξ` of `D` that is not a root, the derivative of the cofactor. -/
theorem eval_derivative_cof {D : ℝ[X]} {s ξ : ℝ} (hs : D.IsRoot s) (hξs : ξ ≠ s)
    (hcrit : (derivative D).eval ξ = 0) :
    (derivative (cof D s)).eval ξ = -D.eval ξ / (ξ - s) ^ 2 := by
  have h := congrArg (fun p => (derivative p).eval ξ) (cof_mul hs)
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    eval_add, eval_mul, eval_sub, eval_X, eval_C, hcrit] at h
  rw [eval_cof hs hξs] at h
  have hne : ξ - s ≠ 0 := sub_ne_zero.mpr hξs
  have h2 : (ξ - s) * (D.eval ξ / (ξ - s)) = D.eval ξ := mul_div_cancel₀ _ hne
  rw [eq_div_iff (pow_ne_zero 2 hne)]
  linear_combination (ξ - s) * h - h2

/-- **Finite partial fractions.**  If `D` splits with simple roots and positive leading coefficient
and `natDegree N ≤ natDegree D`, then
`N = c D + Σ_{s} κ_s · D/(X - s)` with `c = [x^d]N / lc D` and `κ_s = N(s)/D'(s)`. -/
theorem pf_identity {D N : ℝ[X]} (hD : D.Splits) (hlc : 0 < D.leadingCoeff) (hnd : D.roots.Nodup)
    (hN : N.natDegree ≤ D.natDegree) :
    N = C (N.coeff D.natDegree / D.leadingCoeff) * D +
      ∑ s ∈ D.roots.toFinset, C (N.eval s / (derivative D).eval s) * cof D s := by
  classical
  have hD0 : D ≠ 0 := fun h => by simp [h] at hlc
  set d := D.natDegree with hd
  set E := N - (C (N.coeff d / D.leadingCoeff) * D +
      ∑ s ∈ D.roots.toFinset, C (N.eval s / (derivative D).eval s) * cof D s) with hE
  have hroot : ∀ s ∈ D.roots.toFinset, D.IsRoot s := fun s hs =>
    (mem_roots hD0).mp (Multiset.mem_toFinset.mp hs)
  have hderiv : ∀ s ∈ D.roots.toFinset, (derivative D).eval s ≠ 0 := fun s hs => by
    have := sign_derivative hD hlc hnd (Multiset.mem_toFinset.mp hs)
    intro h; rw [h, mul_zero] at this; exact lt_irrefl _ this
  -- E vanishes at every root of D
  have hEval : ∀ t ∈ D.roots.toFinset, E.eval t = 0 := by
    intro t ht
    rw [hE, eval_sub, eval_add, eval_mul, eval_C, (hroot t ht).eq_zero, mul_zero, zero_add,
      eval_finsetSum, Finset.sum_eq_single t]
    · rw [eval_mul, eval_C, eval_cof_self (hroot t ht), div_mul_cancel₀ _ (hderiv t ht), sub_self]
    · intro s hs hst
      rw [eval_mul, eval_cof_of_ne (hroot s hs) (hroot t ht) hst, mul_zero]
    · intro h; exact absurd ht h
  -- coefficients of E at and above d vanish
  have hEcoeff : ∀ m, d ≤ m → E.coeff m = 0 := by
    intro m hm
    have hsum : (∑ s ∈ D.roots.toFinset, C (N.eval s / (derivative D).eval s) * cof D s).coeff m
        = 0 := by
      rw [finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro s hs
      have hd0 : d ≠ 0 := by
        intro h0
        have : D.roots = 0 := by
          rw [eq_C_of_natDegree_eq_zero (show D.natDegree = 0 from h0), roots_C]
        rw [this] at hs; simp at hs
      rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by
        rw [natDegree_divByMonic _ (monic_X_sub_C s), natDegree_X_sub_C]; omega), mul_zero]
    rw [hE, coeff_sub, coeff_add, hsum, add_zero, coeff_C_mul]
    rcases lt_or_eq_of_le hm with hlt | rfl
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hN hlt),
        coeff_eq_zero_of_natDegree_lt hlt, mul_zero, sub_zero]
    · rw [← leadingCoeff, div_mul_cancel₀ _ (ne_of_gt hlc), sub_self]
  have hcard : D.roots.toFinset.card = d := by
    rw [Multiset.card_toFinset, Multiset.dedup_eq_self.mpr hnd]
    exact splits_iff_card_roots.mp hD
  by_cases hE0 : E = 0
  · rw [hE, sub_eq_zero] at hE0; exact hE0
  · exfalso
    have hdeg : E.natDegree < d := by
      by_contra hcon
      push Not at hcon
      exact hE0 (leadingCoeff_eq_zero.mp (hEcoeff _ hcon))
    have := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' E D.roots.toFinset hEval
      (by rw [hcard]; exact hdeg)
    exact hE0 this

/-- Pointwise partial fractions away from the poles. -/
theorem pf_eval {D N : ℝ[X]} (hD : D.Splits) (hlc : 0 < D.leadingCoeff) (hnd : D.roots.Nodup)
    (hN : N.natDegree ≤ D.natDegree) {z : ℝ} (hz : D.eval z ≠ 0) :
    N.eval z = D.eval z * (N.coeff D.natDegree / D.leadingCoeff +
      ∑ s ∈ D.roots.toFinset, (N.eval s / (derivative D).eval s) / (z - s)) := by
  have hD0 : D ≠ 0 := fun h => by simp [h] at hlc
  conv_lhs => rw [pf_identity hD hlc hnd hN]
  rw [eval_add, eval_mul, eval_C, eval_finsetSum, mul_add, Finset.mul_sum, mul_comm (D.eval z)]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have hsr : D.IsRoot s := (mem_roots hD0).mp (Multiset.mem_toFinset.mp hs)
  have hzs : z ≠ s := fun h => hz (h ▸ hsr.eq_zero)
  rw [eval_mul, eval_C, eval_cof hsr hzs]
  ring

/-- Derivative of the numerator at a critical point of the denominator. -/
theorem pf_derivative_at_critical {D N : ℝ[X]} (hD : D.Splits) (hlc : 0 < D.leadingCoeff)
    (hnd : D.roots.Nodup) (hN : N.natDegree ≤ D.natDegree) {ξ : ℝ} (hξ : D.eval ξ ≠ 0)
    (hcrit : (derivative D).eval ξ = 0) :
    (derivative N).eval ξ = -D.eval ξ *
      ∑ s ∈ D.roots.toFinset, (N.eval s / (derivative D).eval s) / (ξ - s) ^ 2 := by
  have hD0 : D ≠ 0 := fun h => by simp [h] at hlc
  conv_lhs => rw [pf_identity hD hlc hnd hN]
  rw [derivative_add, derivative_C_mul, derivative_sum, eval_add, eval_mul, eval_C, hcrit,
    mul_zero, zero_add, eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hsr : D.IsRoot s := (mem_roots hD0).mp (Multiset.mem_toFinset.mp hs)
  have hξs : ξ ≠ s := fun h => hξ (h ▸ hsr.eq_zero)
  rw [derivative_C_mul, eval_mul, eval_C, eval_derivative_cof hsr hξs hcrit]
  ring

/-- Applying `T` to the numerator at a critical point of the denominator. -/
theorem T_at_critical {D N : ℝ[X]} (hD : D.Splits) (hlc : 0 < D.leadingCoeff)
    (hnd : D.roots.Nodup) (hN : N.natDegree ≤ D.natDegree) {ξ : ℝ} (hξ : D.eval ξ ≠ 0)
    (hcrit : (derivative D).eval ξ = 0) :
    (T N).eval ξ = D.eval ξ * (2 * ξ * (N.coeff D.natDegree / D.leadingCoeff) +
      ∑ s ∈ D.roots.toFinset,
        (N.eval s / (derivative D).eval s) * (1 + (1 - s ^ 2) / (ξ - s) ^ 2)) := by
  have hD0 : D ≠ 0 := fun h => by simp [h] at hlc
  have hterm : ∀ s ∈ D.roots.toFinset,
      (N.eval s / (derivative D).eval s) * (1 + (1 - s ^ 2) / (ξ - s) ^ 2) =
        2 * ξ * ((N.eval s / (derivative D).eval s) / (ξ - s)) -
          (ξ ^ 2 - 1) * ((N.eval s / (derivative D).eval s) / (ξ - s) ^ 2) := by
    intro s hs
    have hsr : D.IsRoot s := (mem_roots hD0).mp (Multiset.mem_toFinset.mp hs)
    have hne : ξ - s ≠ 0 := sub_ne_zero.mpr (fun h => hξ (h ▸ hsr.eq_zero))
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    eval_T, pf_derivative_at_critical hD hlc hnd hN hξ hcrit, pf_eval hD hlc hnd hN hξ]
  ring

/-! ### Pairing `s ↔ -s` -/

theorem sum_neg_eq {S : Finset ℝ} (hS : ∀ s ∈ S, -s ∈ S) (φ : ℝ → ℝ) :
    ∑ s ∈ S, φ (-s) = ∑ s ∈ S, φ s :=
  Finset.sum_nbij' (fun s => -s) (fun s => -s) (fun s hs => hS s hs) (fun s hs => hS s hs)
    (fun s _ => neg_neg s) (fun s _ => neg_neg s) (fun _ _ => rfl)

/-- Residue/coefficient conversion: `κ/(z - s) - κ/(z + s) = 2 s κ / (z² - s²)`. -/
theorem residue_pair (κ s z : ℝ) (h1 : z ≠ s) (h2 : z ≠ -s) :
    κ / (z - s) - κ / (z + s) = 2 * s * κ / (z ^ 2 - s ^ 2) := by
  have hne1 : z - s ≠ 0 := sub_ne_zero.mpr h1
  have hne2 : z + s ≠ 0 := fun h => h2 (by linarith)
  have hne : z ^ 2 - s ^ 2 ≠ 0 := by
    rw [show z ^ 2 - s ^ 2 = (z - s) * (z + s) by ring]; exact mul_ne_zero hne1 hne2
  field_simp
  ring

/-- Symmetrized critical-point sum: if the poles are symmetric and the residues odd
(`κ(-s) = -κ(s)`), then `Σ κ_s (1 + (1 - s²)/(ξ - s)²) = ξ Σ 2 s κ_s (1 - s²)/(ξ² - s²)²`. -/
theorem sum_critical_symm {S : Finset ℝ} (hS : ∀ s ∈ S, -s ∈ S) {κ : ℝ → ℝ}
    (hκ : ∀ s ∈ S, κ (-s) = -κ s) {ξ : ℝ} (hξ : ∀ s ∈ S, ξ ≠ s) :
    ∑ s ∈ S, κ s * (1 + (1 - s ^ 2) / (ξ - s) ^ 2) =
      ξ * ∑ s ∈ S, 2 * s * κ s * (1 - s ^ 2) / (ξ ^ 2 - s ^ 2) ^ 2 := by
  set φ : ℝ → ℝ := fun s => κ s * (1 + (1 - s ^ 2) / (ξ - s) ^ 2) with hφ
  have h2 : 2 * ∑ s ∈ S, φ s = ∑ s ∈ S, (φ s + φ (-s)) := by
    rw [Finset.sum_add_distrib, sum_neg_eq hS φ]; ring
  have hpair : ∀ s ∈ S, φ s + φ (-s) = 2 * (ξ * (2 * s * κ s * (1 - s ^ 2) / (ξ ^ 2 - s ^ 2) ^ 2)) := by
    intro s hs
    have hne1 : ξ - s ≠ 0 := sub_ne_zero.mpr (hξ s hs)
    have hne2 : ξ + s ≠ 0 := fun h => hξ (-s) (hS s hs) (by linarith)
    have hne : ξ ^ 2 - s ^ 2 ≠ 0 := by
      rw [show ξ ^ 2 - s ^ 2 = (ξ - s) * (ξ + s) by ring]; exact mul_ne_zero hne1 hne2
    simp only [hφ, hκ s hs, sub_neg_eq_add, neg_sq]
    field_simp
    ring
  have : 2 * ∑ s ∈ S, φ s = 2 * (ξ * ∑ s ∈ S, 2 * s * κ s * (1 - s ^ 2) / (ξ ^ 2 - s ^ 2) ^ 2) := by
    rw [h2, Finset.sum_congr rfl hpair, ← Finset.mul_sum, ← Finset.mul_sum]
  linarith

/-- The paired form of the partial fractions: with symmetric poles and odd residues,
`Σ_s κ_s/(z - s) = Σ_{s > 0} 2 s κ_s / (z² - s²)` (a zero pole contributes nothing). -/
theorem sum_residue_paired {S : Finset ℝ} (hS : ∀ s ∈ S, -s ∈ S) {κ : ℝ → ℝ}
    (hκ : ∀ s ∈ S, κ (-s) = -κ s) {z : ℝ} (hz : ∀ s ∈ S, z ≠ s) :
    ∑ s ∈ S, κ s / (z - s) = ∑ s ∈ S.filter (fun s => 0 < s), 2 * s * κ s / (z ^ 2 - s ^ 2) := by
  classical
  set g : ℝ → ℝ := fun s => s * κ s / (z ^ 2 - s ^ 2) with hg
  -- step 1: Σ κ/(z-s) = Σ g
  have hstep1 : ∑ s ∈ S, κ s / (z - s) = ∑ s ∈ S, g s := by
    have h2 : 2 * ∑ s ∈ S, κ s / (z - s) = ∑ s ∈ S, (κ s / (z - s) + κ (-s) / (z - -s)) := by
      rw [Finset.sum_add_distrib, sum_neg_eq hS (fun s => κ s / (z - s))]; ring
    have hp : ∀ s ∈ S, κ s / (z - s) + κ (-s) / (z - -s) = 2 * g s := by
      intro s hs
      rw [hκ s hs, sub_neg_eq_add, neg_div, ← sub_eq_add_neg,
        residue_pair _ _ _ (hz s hs) (hz (-s) (hS s hs))]
      simp only [hg]; ring
    rw [Finset.sum_congr rfl hp, ← Finset.mul_sum] at h2
    linarith
  -- step 2: split by sign; `g` is even on `S` and `g 0 = 0`
  have hgeven : ∀ s ∈ S, g (-s) = g s := by
    intro s hs; simp only [hg]; rw [hκ s hs, neg_sq]; ring
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun s => 0 < s) g
  have hsplit2 := Finset.sum_filter_add_sum_filter_not (S.filter (fun s => ¬ 0 < s))
    (fun s => s < 0) g
  have hneg : ∑ s ∈ (S.filter (fun s => ¬ 0 < s)).filter (fun s => s < 0), g s =
      ∑ s ∈ S.filter (fun s => 0 < s), g s := by
    apply Finset.sum_nbij' (fun s => -s) (fun s => -s)
    · intro s hs
      simp only [Finset.mem_filter] at hs ⊢
      exact ⟨hS s hs.1.1, by linarith [hs.2]⟩
    · intro s hs
      simp only [Finset.mem_filter] at hs ⊢
      exact ⟨⟨hS s hs.1, by linarith [hs.2]⟩, by linarith [hs.2]⟩
    · intro s _; exact neg_neg s
    · intro s _; exact neg_neg s
    · intro s hs
      simp only [Finset.mem_filter] at hs
      rw [← hgeven s hs.1.1]
  have hzero : ∑ s ∈ (S.filter (fun s => ¬ 0 < s)).filter (fun s => ¬ s < 0), g s = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    simp only [Finset.mem_filter] at hs
    have : s = 0 := by linarith [not_lt.mp hs.1.2, not_lt.mp hs.2]
    simp [hg, this]
  rw [hstep1, ← hsplit, ← hsplit2, hneg, hzero, add_zero]
  rw [show ∑ s ∈ S.filter (fun s => 0 < s), 2 * s * κ s / (z ^ 2 - s ^ 2) =
      2 * ∑ s ∈ S.filter (fun s => 0 < s), g s by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; simp only [hg]; ring]
  ring

/-! ### Critical points (A (3.3)); the trivial residue at a common zero -/

/-- At a critical point `ξ` (not a root) of a split polynomial,
`D''(ξ)/D(ξ) = -Σ_s (ξ - s)⁻²`. -/
theorem critical_second_derivative_div {D : ℝ[X]} (hD : D.Splits) {ξ : ℝ} (hξ : D.eval ξ ≠ 0)
    (hcrit : (derivative D).eval ξ = 0) :
    (derivative (derivative D)).eval ξ / D.eval ξ = -(D.roots.map (fun s => 1 / (ξ - s) ^ 2)).sum := by
  have h := eval_derivative_sq_sub_of_splits hD hξ
  rw [hcrit] at h
  rw [div_eq_iff hξ]
  have h2 : D.eval ξ * ((derivative (derivative D)).eval ξ +
      (D.roots.map (fun s => 1 / (ξ - s) ^ 2)).sum * D.eval ξ) = 0 := by
    linear_combination -h
  linear_combination (mul_eq_zero.mp h2).resolve_left hξ

/-- The sign in A (3.3): `D''(ξ) D(ξ) < 0` at a critical point of a split polynomial with at least
one root. -/
theorem critical_second_derivative_mul_neg {D : ℝ[X]} (hD : D.Splits) (hne : D.roots ≠ 0) {ξ : ℝ}
    (hξ : D.eval ξ ≠ 0) (hcrit : (derivative D).eval ξ = 0) :
    (derivative (derivative D)).eval ξ * D.eval ξ < 0 := by
  have hD0 : D ≠ 0 := fun h => hξ (by simp [h])
  have h := eval_derivative_sq_sub_of_splits hD hξ
  rw [hcrit] at h
  have hV : 0 < (D.roots.map (fun s => 1 / (ξ - s) ^ 2)).sum := by
    have := Multiset.sum_lt_sum_of_nonempty (s := D.roots) (f := fun _ => (0 : ℝ))
      (g := fun s => 1 / (ξ - s) ^ 2) (by simpa using hne) (fun s hs => by
        have : ξ - s ≠ 0 := sub_ne_zero.mpr (fun h' => hξ (h' ▸ (mem_roots hD0).mp hs))
        positivity)
    simpa using this
  have hD2 : 0 < (D.eval ξ) ^ 2 := by positivity
  nlinarith [mul_pos hD2 hV]

/-- If the numerator vanishes at `0`, the residue `κ_0 = N(0)/D'(0)` is `0` (trivial). -/
theorem residue_zero_of_eval_zero {D N : ℝ[X]} (hN : N.eval 0 = 0) :
    N.eval 0 / (derivative D).eval 0 = 0 := by
  rw [hN, zero_div]

end EulerianRegion
