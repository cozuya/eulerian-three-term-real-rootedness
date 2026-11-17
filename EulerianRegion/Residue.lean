module

public import EulerianRegion.PartialFractions

/-!
# Positive residues for the two-step Eulerian ratio (A Lemma 3.1, Corollary 3.2)

Source: Candidate A §3, audit §3.2.  Indices: `F m = (X² - 1) C_{m+1}` is the source's
`F_n = (z² - 1) C_{n-2}` with `n = m + 3`; the numerator is `C_{m+3} = C_n`, and `F_m' = C_{m+2}`
(`derivative_F`, A (3.2)).

* `F_splits`, `F_nodup`, `F_root_mem`, `F_root_neg`, `F_natDegree`, `F_leadingCoeff`: the poles are
  `±1` and the roots of `C_{m+1}`, all simple, symmetric, in `[-1, 1]`; equal degrees.
* `resid m s = C_{m+3}(s)/C_{m+2}(s)` is the ordinary residue at the simple pole `s`; it is odd in `s`
  (`resid_neg`, parity).
* `residue_pos` (**the induction**, invariant form): for every pole `s ≠ 0`,
  `s · C_{m+3}(s) · C_{m+2}(s) > 0`.  Base `m = 0`: `C_3/F_0 = 6 + 4/(z² - 1)` (only the endpoint
  poles).  Step: endpoint poles `±1` directly (`endpoint_pos`); an interior pole `ξ` of `F_{m+1}` is a
  critical point of `F_m`, and `C_{m+4}(ξ) = F_m(ξ) · ξ · B` with `B ≥ 2ρ > 0` (A (3.5), from
  `T_at_critical` and the pairing `sum_critical_symm`, using the invariant at level `m` for every
  term), while `C_{m+3}(ξ) = (ξ² - 1) F_m''(ξ)` and `F_m''(ξ) F_m(ξ) < 0` (A (3.3)–(3.4)).  The zero
  pole (present when `F_m` is odd) is excluded from the invariant and contributes `0` to every
  pairing sum because its terms carry the factor `s`; this is the cancellation at zero.
* `positive_partial_fractions` (**A (3.1)**): `C_{m+3}/F_m = ρ + Σ_{s > 0} λ_s/(z² - s²)` away from
  the poles, with `ρ > 0` (`rho_pos`), `λ_s = 2 s κ_s > 0`, `0 < s ≤ 1` (`lambda_pos`).
* `cor_3_2` (**Corollary 3.2**): at every positive root `r` of `f = C_{m+1}`,
  `h(r) g(r) > 0` with `g = C_{m+2}`, `h = C_{m+3}`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace EulerianRegion

/-! ### Positive residues for the two-step Eulerian ratio (A Lemma 3.1, Corollary 3.2) -/

/-- `F m = (X² - 1) C_{m+1}`; in the source's indexing this is `F_n = (z² - 1) C_{n-2}` with
`n = m + 3`. -/
def F (m : ℕ) : ℝ[X] := (X ^ 2 - 1) * Cay (m + 1)

theorem derivative_F (m : ℕ) : derivative (F m) = Cay (m + 2) := by
  rw [F, Cay_succ_succ]; rfl

/-- A (3.2): `F_{n+1} = (z² - 1) F_n'`. -/
theorem F_succ (m : ℕ) : F (m + 1) = (X ^ 2 - 1) * derivative (F m) := by
  rw [derivative_F, F]

theorem X_sq_sub_one_eq : (X ^ 2 - 1 : ℝ[X]) = (X - C 1) * (X - C (-1)) := by
  simp; ring

theorem roots_X_sq_sub_one : (X ^ 2 - 1 : ℝ[X]).roots = {1, -1} := by
  rw [X_sq_sub_one_eq, roots_mul (by
    rw [← X_sq_sub_one_eq]; intro h
    have := congrArg (eval 0) h; simp at this), roots_X_sub_C, roots_X_sub_C]
  rfl

theorem F_ne_zero (m : ℕ) : F m ≠ 0 := by
  rw [F, X_sq_sub_one_eq]
  exact mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero 1) (X_sub_C_ne_zero (-1))) (Cay_ne_zero m)

theorem roots_F (m : ℕ) : (F m).roots = 1 ::ₘ (-1) ::ₘ (Cay (m + 1)).roots := by
  have h := F_ne_zero m
  rw [F] at h ⊢
  rw [roots_mul h, roots_X_sq_sub_one]
  simp only [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add]

theorem mem_roots_F {m : ℕ} {s : ℝ} :
    s ∈ (F m).roots ↔ s = 1 ∨ s = -1 ∨ s ∈ (Cay (m + 1)).roots := by
  rw [roots_F]; simp

theorem F_splits (m : ℕ) : (F m).Splits := by
  rw [F, X_sq_sub_one_eq]
  exact ((Splits.X_sub_C 1).mul (Splits.X_sub_C (-1))).mul (Cay_rootedIn m).splits

theorem F_nodup (m : ℕ) : (F m).roots.Nodup := by
  rw [roots_F]
  have h := Cay_rootedIn m
  refine Multiset.nodup_cons.mpr ⟨?_, Multiset.nodup_cons.mpr ⟨?_, h.nodup⟩⟩
  · simp only [Multiset.mem_cons, not_or]
    exact ⟨by norm_num, fun h1 => lt_irrefl _ (h.mem 1 h1).2⟩
  · exact fun h1 => lt_irrefl _ (h.mem (-1) h1).1

theorem monic_X_sq_sub_one : (X ^ 2 - 1 : ℝ[X]).Monic := by
  simpa using monic_X_pow_sub_C (1 : ℝ) two_ne_zero

theorem F_natDegree (m : ℕ) : (F m).natDegree = m + 2 := by
  have h2 : (X ^ 2 - 1 : ℝ[X]).natDegree = 2 := by compute_degree!
  rw [F, natDegree_mul monic_X_sq_sub_one.ne_zero (Cay_ne_zero m), h2, natDegree_Cay]
  ring

theorem F_leadingCoeff (m : ℕ) : (F m).leadingCoeff = ((m + 1).factorial : ℝ) := by
  rw [F, leadingCoeff_mul, leadingCoeff_Cay, monic_X_sq_sub_one.leadingCoeff, one_mul]

theorem F_lc_pos (m : ℕ) : 0 < (F m).leadingCoeff := by
  rw [F_leadingCoeff]; exact_mod_cast Nat.factorial_pos _

theorem F_root_mem {m : ℕ} {s : ℝ} (hs : s ∈ (F m).roots) : -1 ≤ s ∧ s ≤ 1 := by
  rcases mem_roots_F.mp hs with rfl | rfl | h
  · norm_num
  · norm_num
  · exact ⟨((Cay_rootedIn m).mem s h).1.le, ((Cay_rootedIn m).mem s h).2.le⟩

theorem F_root_neg {m : ℕ} {s : ℝ} (hs : s ∈ (F m).roots) : -s ∈ (F m).roots := by
  rcases mem_roots_F.mp hs with rfl | rfl | h
  · exact mem_roots_F.mpr (Or.inr (Or.inl rfl))
  · exact mem_roots_F.mpr (Or.inl (by norm_num))
  · exact mem_roots_F.mpr (Or.inr (Or.inr (Cay_root_neg m h)))

theorem natDegree_Cay_add_three_eq_F (m : ℕ) : (Cay (m + 3)).natDegree = (F m).natDegree := by
  rw [F_natDegree, show m + 3 = (m + 2) + 1 by ring, natDegree_Cay]

/-- The ordinary residue of `C_{m+3}/F_m` at a simple pole `s`: `C_{m+3}(s)/F_m'(s)`. -/
def resid (m : ℕ) (s : ℝ) : ℝ := (Cay (m + 3)).eval s / (Cay (m + 2)).eval s

theorem resid_neg (m : ℕ) (s : ℝ) : resid m (-s) = -resid m s := by
  unfold resid
  rw [show m + 3 = (m + 2) + 1 by ring, show m + 2 = (m + 1) + 1 by ring, eval_neg_Cay,
    eval_neg_Cay, pow_succ]
  rcases neg_one_pow_eq_or ℝ (m + 1) with h | h <;> rw [h] <;> ring

/-- The constant part of the expansion: `ρ = lc C_{m+3} / lc F_m = (m+3)(m+2) > 0`. -/
theorem rho_pos (m : ℕ) : 0 < (Cay (m + 3)).coeff (F m).natDegree / (F m).leadingCoeff := by
  rw [← natDegree_Cay_add_three_eq_F, ← leadingCoeff, show m + 3 = (m + 2) + 1 by ring,
    leadingCoeff_Cay]
  exact div_pos (by exact_mod_cast Nat.factorial_pos _) (F_lc_pos m)

/-- The endpoint poles `±1`. -/
theorem endpoint_pos (m : ℕ) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    0 < s * (Cay (m + 3)).eval s * (Cay (m + 2)).eval s := by
  rw [show m + 3 = (m + 2) + 1 by ring, show m + 2 = (m + 1) + 1 by ring]
  rcases hs with rfl | rfl
  · rw [eval_one_Cay, eval_one_Cay]; positivity
  · rw [eval_neg_one_Cay, eval_neg_one_Cay, mul_assoc, ← pow_add,
      show m + 1 + 1 + (m + 1) = 2 * m + 3 by ring, Odd.neg_pow ⟨m + 1, by ring⟩, neg_one_mul,
      neg_neg]
    positivity

/-- **Positive residues (A Lemma 3.1, invariant form).**  For every pole `s ≠ 0` of
`C_{m+3}/F_m`, `s · C_{m+3}(s) · C_{m+2}(s) > 0`; equivalently the ordinary residue
`C_{m+3}(s)/F_m'(s)` has the sign of `s`. -/
theorem residue_pos (m : ℕ) :
    ∀ s ∈ (F m).roots, s ≠ 0 → 0 < s * (Cay (m + 3)).eval s * (Cay (m + 2)).eval s := by
  induction m with
  | zero =>
    intro s hs _
    rcases mem_roots_F.mp hs with h | h | h
    · exact endpoint_pos 0 (Or.inl h)
    · exact endpoint_pos 0 (Or.inr h)
    · simp at h
  | succ m ih =>
    intro ξ hξ hξ0
    rcases mem_roots_F.mp hξ with h | h | hξc
    · exact endpoint_pos (m + 1) (Or.inl h)
    · exact endpoint_pos (m + 1) (Or.inr h)
    -- an interior pole: a critical point of `F m`
    have hξc' : ξ ∈ (Cay (m + 2)).roots := hξc
    have hcrit : (derivative (F m)).eval ξ = 0 := by
      rw [derivative_F]; exact ((mem_roots (Cay_ne_zero _)).mp hξc').eq_zero
    have hξm := (Cay_rootedIn (m + 1)).mem ξ hξc'
    have hDξ : (F m).eval ξ ≠ 0 := by
      intro h0
      have hroot : ξ ∈ (F m).roots := (mem_roots (F_ne_zero m)).mpr h0
      rcases mem_roots_F.mp hroot with h1 | h1 | h1
      · linarith [hξm.2]
      · linarith [hξm.1]
      · exact (Cay_interlace m h1).2 ((mem_roots (Cay_ne_zero _)).mp hξc').eq_zero
    have hNdeg : (Cay (m + 3)).natDegree ≤ (F m).natDegree := (natDegree_Cay_add_three_eq_F m).le
    -- (3.5): `C_{m+4}(ξ) = F_m(ξ) · ξ · B` with `B ≥ 2ρ > 0`
    have hsymm : ∀ s ∈ (F m).roots.toFinset, -s ∈ (F m).roots.toFinset := fun s hs =>
      Multiset.mem_toFinset.mpr (F_root_neg (Multiset.mem_toFinset.mp hs))
    have hne : ∀ s ∈ (F m).roots.toFinset, ξ ≠ s := fun s hs h =>
      hDξ (h ▸ ((mem_roots (F_ne_zero m)).mp (Multiset.mem_toFinset.mp hs)))
    have hT := T_at_critical (F_splits m) (F_lc_pos m) (F_nodup m) hNdeg hDξ hcrit
    rw [derivative_F] at hT
    have hresid : ∀ s, (Cay (m + 3)).eval s / (Cay (m + 2)).eval s = resid m s := fun _ => rfl
    simp only [hresid] at hT
    rw [sum_critical_symm hsymm (fun s _ => resid_neg m s) hne] at hT
    set B := 2 * ((Cay (m + 3)).coeff (F m).natDegree / (F m).leadingCoeff) +
      ∑ s ∈ (F m).roots.toFinset, 2 * s * resid m s * (1 - s ^ 2) / (ξ ^ 2 - s ^ 2) ^ 2 with hB
    have hTB : (Cay (m + 4)).eval ξ = (F m).eval ξ * ξ * B := by
      rw [show m + 4 = (m + 2) + 2 by ring, Cay_succ_succ, show m + 2 + 1 = m + 3 by ring, hT]
      ring
    have hBpos : 0 < B := by
      have hterm : ∀ s ∈ (F m).roots.toFinset, 0 ≤ 2 * s * resid m s * (1 - s ^ 2) / (ξ ^ 2 - s ^ 2) ^ 2 := by
        intro s hs
        have hsr := Multiset.mem_toFinset.mp hs
        have h1 : 0 ≤ 1 - s ^ 2 := by
          have := F_root_mem hsr; nlinarith
        have h2 : 0 ≤ s * resid m s := by
          by_cases hs0 : s = 0
          · rw [hs0]; simp
          · have := ih s hsr hs0
            unfold resid
            rcases eq_or_ne ((Cay (m + 2)).eval s) 0 with h0 | h0
            · rw [h0]; simp
            · rw [mul_div_assoc', div_eq_mul_inv]
              have : 0 < s * (Cay (m + 3)).eval s * (Cay (m + 2)).eval s *
                  ((Cay (m + 2)).eval s)⁻¹ ^ 2 := mul_pos this (by positivity)
              have heq : s * (Cay (m + 3)).eval s * (Cay (m + 2)).eval s *
                  ((Cay (m + 2)).eval s)⁻¹ ^ 2 = s * (Cay (m + 3)).eval s *
                  ((Cay (m + 2)).eval s)⁻¹ := by field_simp
              linarith
        have : 0 ≤ 2 * s * resid m s * (1 - s ^ 2) := by nlinarith
        positivity
      have := Finset.sum_nonneg hterm
      have := rho_pos m
      rw [hB]; linarith
    -- (3.3)–(3.4): `C_{m+3}(ξ) = (ξ² - 1) F_m''(ξ)` and `F_m''(ξ) F_m(ξ) < 0`
    have hN3 : (Cay (m + 3)).eval ξ = (ξ ^ 2 - 1) * (derivative (derivative (F m))).eval ξ := by
      rw [show m + 3 = (m + 2) + 1 by ring, Cay_succ_succ, eval_T,
        ((mem_roots (Cay_ne_zero _)).mp hξc').eq_zero, derivative_F]
      ring
    have hDD : (derivative (derivative (F m))).eval ξ * (F m).eval ξ < 0 :=
      critical_second_derivative_mul_neg (F_splits m) (by rw [roots_F]; simp) hDξ hcrit
    have hξ2 : ξ ^ 2 - 1 < 0 := by nlinarith [hξm.1, hξm.2]
    have hξpos : 0 < ξ ^ 2 := by positivity
    rw [show (m + 1) + 3 = m + 4 by ring, show (m + 1) + 2 = m + 3 by ring, hTB, hN3]
    have : ξ * ((F m).eval ξ * ξ * B) * ((ξ ^ 2 - 1) * (derivative (derivative (F m))).eval ξ) =
        ξ ^ 2 * B * (ξ ^ 2 - 1) * ((derivative (derivative (F m))).eval ξ * (F m).eval ξ) := by ring
    rw [this]
    have h1 : 0 < ξ ^ 2 * B := mul_pos hξpos hBpos
    have h2 : 0 < (ξ ^ 2 - 1) * ((derivative (derivative (F m))).eval ξ * (F m).eval ξ) :=
      mul_pos_of_neg_of_neg hξ2 hDD
    nlinarith

/-- **Corollary 3.2.**  At every positive root `r` of `f = C_{m+1}`, with `g = C_{m+2}` and
`h = C_{m+3}`: `h(r) g(r) > 0` (equivalently `h(r)/g(r) > 0`, with `g(r) ≠ 0`). -/
theorem cor_3_2 (m : ℕ) {r : ℝ} (hr : r ∈ (Cay (m + 1)).roots) (hpos : 0 < r) :
    0 < (Cay (m + 3)).eval r * (Cay (m + 2)).eval r := by
  have h := residue_pos m r (mem_roots_F.mpr (Or.inr (Or.inr hr))) hpos.ne'
  rw [mul_assoc] at h
  exact pos_of_mul_pos_right h hpos.le

/-- The paired coefficients `λ_s = 2 s κ_s` are positive at every positive pole, and the poles lie
in `(0, 1]`. -/
theorem lambda_pos (m : ℕ) {s : ℝ} (hs : s ∈ (F m).roots) (hpos : 0 < s) :
    0 < 2 * s * resid m s ∧ s ≤ 1 := by
  refine ⟨?_, (F_root_mem hs).2⟩
  have h := residue_pos m s hs hpos.ne'
  have hg : (Cay (m + 2)).eval s ≠ 0 := fun h0 => by rw [h0, mul_zero] at h; exact lt_irrefl _ h
  unfold resid
  have : 0 < s * (Cay (m + 3)).eval s * (Cay (m + 2)).eval s / ((Cay (m + 2)).eval s) ^ 2 :=
    div_pos h (by positivity)
  have heq : s * (Cay (m + 3)).eval s * (Cay (m + 2)).eval s / ((Cay (m + 2)).eval s) ^ 2 =
      s * ((Cay (m + 3)).eval s / (Cay (m + 2)).eval s) := by field_simp
  rw [heq] at this
  linarith

/-- **A (3.1), positive partial fractions.**  Away from the poles,
`C_{m+3}(z)/F_m(z) = ρ + Σ_{s > 0 pole} λ_s / (z² - s²)` with `ρ = lc C_{m+3}/lc F_m > 0`
(`rho_pos`), `λ_s = 2 s κ_s > 0` and `0 < s ≤ 1` (`lambda_pos`).  The zero pole present for odd
`F_m` contributes nothing (it is cancelled). -/
theorem positive_partial_fractions (m : ℕ) {z : ℝ} (hz : (F m).eval z ≠ 0) :
    (Cay (m + 3)).eval z / (F m).eval z =
      (Cay (m + 3)).coeff (F m).natDegree / (F m).leadingCoeff +
        ∑ s ∈ (F m).roots.toFinset.filter (fun s => 0 < s), 2 * s * resid m s / (z ^ 2 - s ^ 2) := by
  have h := pf_eval (F_splits m) (F_lc_pos m) (F_nodup m) (natDegree_Cay_add_three_eq_F m).le hz
  rw [derivative_F] at h
  have hsymm : ∀ s ∈ (F m).roots.toFinset, -s ∈ (F m).roots.toFinset := fun s hs =>
    Multiset.mem_toFinset.mpr (F_root_neg (Multiset.mem_toFinset.mp hs))
  have hne : ∀ s ∈ (F m).roots.toFinset, z ≠ s := fun s hs he =>
    hz (he ▸ ((mem_roots (F_ne_zero m)).mp (Multiset.mem_toFinset.mp hs)))
  have hpair := sum_residue_paired hsymm (fun s _ => resid_neg m s) hne
  have hresid : ∀ s, (Cay (m + 3)).eval s / (Cay (m + 2)).eval s = resid m s := fun _ => rfl
  simp only [hresid] at h
  rw [h, mul_div_assoc, mul_div_cancel₀ _ hz, ← hpair]

end EulerianRegion
