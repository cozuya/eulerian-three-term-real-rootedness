module

public import EulerianRegion.Separator
public import Mathlib.Algebra.CharZero.Infinite

/-!
# Sufficiency for `n ≥ 4` with `b > 0` or `n` odd (A §§5–6 Cases I–II)

Let `n = k + 3` (`k ≥ 1`), `f = C_{k+1}`, `g = C_{k+2}`, `h = C_{k+3}`.

* `Phat b c k = h + b (z+1) g + c (z+1)² f` (A (5.1)); `homog_combination`: it is the Cayley
  homogenization `homog (n - 1) P_n` of `P_n = combination n b c`.  `Phat_degree`: degree
  `k + 2 = n - 1`, positive leading coefficient (no degree drop); `eval_one_Phat`: `P̂(1) > 0`;
  `eval_neg_one_Phat`: `P̂(-1) = (-2)^(k+2)` (A (5.2)).
* `Phat_sign_neg_sep` (A (5.5) at the negative roots of `q`) and `Phat_sign_nonneg_f` (A (5.6) at
  the positive roots of `f` via Corollary 3.2, and at `0` via `P̂(0) = b g(0)` when `b > 0`).
* `Phat_signPattern`: strictly alternating signs on the `k + 3` hybrid test points, i.e. on
  `natDegree P̂ + 1` points (A §6 Cases I and II, all junctions and endpoints, `n = 4` included).
* `splits_of_homog` (transport back through `x = (z - 1)/(z + 1)`): if `homog d p` has degree `d`,
  splits, and is nonzero at `-1`, then `p` splits, with
  `p = (lc P̂/2^d) ∏ ((1 + z_i) x + (1 - z_i))` over the roots `z_i` of `P̂` (multiplicities kept).
* `combination_splits_of_branch`: `P_n` splits for `n ≥ 4`, `0 ≤ b`, `0 ≤ c ≤ b²/4 + b + 3`, when
  `b > 0` or `n` is odd.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace EulerianRegion

/-! ### The transformed target polynomial `P̂ = h + b(z+1) g + c(z+1)² f` -/

/-- `P̂_k = C_{k+3} + b (X+1) C_{k+2} + c (X+1)² C_{k+1}`; for `n = k + 3` this is the Cayley transform
of `P_n` (`homog_combination`). -/
def Phat (b c : ℝ) (k : ℕ) : ℝ[X] :=
  Cay (k + 3) + C b * (X + 1) * Cay (k + 2) + C c * (X + 1) ^ 2 * Cay (k + 1)

theorem Phat_eq_T (b c : ℝ) (k : ℕ) :
    Phat b c k = T (T (Cay (k + 1))) + C (2 * (1 + b / 2) - 2) * (X + 1) * T (Cay (k + 1)) +
      C c * (X + 1) ^ 2 * Cay (k + 1) := by
  rw [Phat, show k + 3 = (k + 1) + 2 by ring, Cay_succ_succ, show k + 1 + 1 = k + 2 by ring,
    Cay_succ_succ, show 2 * (1 + b / 2) - 2 = b by ring]

theorem eval_Phat (b c : ℝ) (k : ℕ) (z : ℝ) :
    (Phat b c k).eval z = (Cay (k + 3)).eval z + b * (z + 1) * (Cay (k + 2)).eval z +
      c * (z + 1) ^ 2 * (Cay (k + 1)).eval z := by
  simp [Phat]

theorem Phat_degree {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (k : ℕ) :
    (Phat b c k).natDegree = k + 2 ∧ 0 < (Phat b c k).leadingCoeff := by
  have h3 := natDegree_Cay (k + 2)
  have h2 := natDegree_Cay (k + 1)
  have h1 := natDegree_Cay k
  have hX1 : (X + 1 : ℝ[X]).natDegree = 1 := by simp
  have hX2 : ((X + 1 : ℝ[X]) ^ 2).natDegree = 2 := by simp
  have hcoeff : (Phat b c k).coeff (k + 2) =
      ((k + 3).factorial : ℝ) + b * ((k + 2).factorial : ℝ) + c * ((k + 1).factorial : ℝ) := by
    have e3 : (Cay (k + 3)).coeff (k + 2) = ((k + 3).factorial : ℝ) := by
      rw [← leadingCoeff_Cay (k + 2), leadingCoeff, h3]
    have e2 : ((X + 1) * Cay (k + 2)).coeff (k + 2) = ((k + 2).factorial : ℝ) := by
      obtain ⟨hd, hl⟩ := X_add_one_mul_degree (Cay_ne_zero (k + 1))
      rw [← leadingCoeff_Cay (k + 1), ← hl, leadingCoeff, hd, h2]
    have e1 : ((X + 1) ^ 2 * Cay (k + 1)).coeff (k + 2) = ((k + 1).factorial : ℝ) := by
      have hm : ((X + 1 : ℝ[X]) ^ 2).Monic :=
        (by simpa using monic_X_add_C (1 : ℝ) : (X + 1 : ℝ[X]).Monic).pow 2
      have hd : ((X + 1 : ℝ[X]) ^ 2 * Cay (k + 1)).natDegree = k + 2 := by
        rw [natDegree_mul hm.ne_zero (Cay_ne_zero k), hX2, h1]; ring
      have hlc : ((X + 1 : ℝ[X]) ^ 2 * Cay (k + 1)).coeff (k + 2) =
          ((X + 1 : ℝ[X]) ^ 2 * Cay (k + 1)).leadingCoeff := by
        rw [leadingCoeff, hd]
      rw [hlc, leadingCoeff_mul, hm.leadingCoeff, one_mul, leadingCoeff_Cay]
    simp only [Phat, coeff_add, mul_assoc, coeff_C_mul, e3, e2, e1]
  have hpos : 0 < ((k + 3).factorial : ℝ) + b * ((k + 2).factorial : ℝ) + c * ((k + 1).factorial : ℝ) := by
    have : (0 : ℝ) < (k + 3).factorial := by exact_mod_cast Nat.factorial_pos _
    positivity
  have hle : (Phat b c k).natDegree ≤ k + 2 := by
    unfold Phat
    refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le h3.le ?_)) ?_)
    · rw [mul_assoc]
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [(X_add_one_mul_degree (Cay_ne_zero (k + 1))).1, h2]
    · rw [mul_assoc]
      refine (natDegree_C_mul_le _ _).trans ((natDegree_mul_le).trans ?_)
      rw [hX2, h1]; omega
  have hdeg : (Phat b c k).natDegree = k + 2 :=
    le_antisymm hle (le_natDegree_of_ne_zero (by rw [hcoeff]; exact hpos.ne'))
  exact ⟨hdeg, by rw [leadingCoeff, hdeg, hcoeff]; exact hpos⟩

theorem eval_one_Phat {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (k : ℕ) : 0 < (Phat b c k).eval 1 := by
  rw [eval_Phat, show k + 3 = (k + 2) + 1 by ring, show k + 2 = (k + 1) + 1 by ring, eval_one_Cay,
    eval_one_Cay, eval_one_Cay]
  positivity

theorem eval_neg_one_Phat (b c : ℝ) (k : ℕ) : (Phat b c k).eval (-1) = (-2) ^ (k + 2) := by
  rw [eval_Phat, show k + 3 = (k + 2) + 1 by ring, eval_neg_one_Cay]; ring

section Hybrid

variable {b c : ℝ}

/-- **A (5.5) at the test points**: at a negative root `s` of `q`,
`(-1)^(N_f(s) + 1) P̂(s) > 0`. -/
theorem Phat_sign_neg_sep (hb : 0 ≤ b) (hbc : c ≤ b ^ 2 / 4 + b + 3) {k : ℕ} (hk : 1 ≤ k) {s : ℝ}
    (hsq : s ∈ (sep (1 + b / 2) (Cay (k + 1))).roots) (hs0 : s < 0) :
    0 < (-1 : ℝ) ^ (above (Cay (k + 1)).roots s + 1) * (Phat b c k).eval s := by
  have hα : 0 ≤ 1 + b / 2 := by linarith
  have hf := Cay_rootedIn k
  have hq := sep_signPattern hα hf
  have hqR := interlace_step_rootedIn hf hq
  have hsm := hqR.mem s hsq
  have hqs : (sep (1 + b / 2) (Cay (k + 1))).eval s = 0 := (mem_roots hqR.ne_zero).mp hsq
  have hfs : (Cay (k + 1)).eval s ≠ 0 := by
    intro h0
    exact (interlace_step_above_at_f_root hf hq ((mem_roots hf.ne_zero).mpr h0)).2 hqs
  have hroots_ne : (Cay (k + 1)).roots ≠ 0 := by
    intro h
    have := hf.card_roots
    rw [h, natDegree_Cay] at this
    simp at this; omega
  have hcα : c ≤ (1 + b / 2) ^ 2 + 2 := by nlinarith
  have h55 := sign_at_neg_separator_root hf (fun r hr => Cay_root_neg k hr) hroots_ne hcα hs0 hsm.1
    hqs hfs
  rw [← Phat_eq_T] at h55
  have hsf := sign_eval hf.splits hf.lc_pos (show ¬ (Cay (k + 1)).IsRoot s from hfs)
  have hsq1 : ((-1 : ℝ) ^ above (Cay (k + 1)).roots s) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [pow_succ]
  nlinarith [mul_pos hsf hsf]

/-- **A (5.6) at the test points**: at a nonnegative root `r` of `f`, with `r > 0` or `b > 0`,
`(-1)^(N_f(r) + 1) P̂(r) > 0`.  For `r > 0` this uses Corollary 3.2; for `r = 0` it uses
`P̂(0) = b g(0)` and `b > 0`. -/
theorem Phat_sign_nonneg_f (hb : 0 ≤ b) {k : ℕ} {r : ℝ} (hrf : r ∈ (Cay (k + 1)).roots)
    (hr0 : 0 ≤ r) (hbr : 0 < r ∨ 0 < b) :
    0 < (-1 : ℝ) ^ (above (Cay (k + 1)).roots r + 1) * (Phat b c k).eval r := by
  have hf := Cay_rootedIn k
  have hrm := hf.mem r hrf
  have hfr : (Cay (k + 1)).eval r = 0 := (mem_roots hf.ne_zero).mp hrf
  rw [pow_succ]
  set σ := (-1 : ℝ) ^ above (Cay (k + 1)).roots r with hσ
  have hd := sign_derivative hf.splits hf.lc_pos hf.nodup hrf
  rw [← hσ] at hd
  have hg : (Cay (k + 2)).eval r = (r ^ 2 - 1) * (derivative (Cay (k + 1))).eval r := by
    rw [Cay_succ_succ, eval_T, hfr]; ring
  have hσg : 0 < -σ * (Cay (k + 2)).eval r := by
    rw [hg]
    have : 0 < 1 - r ^ 2 := by nlinarith [hrm.1, hrm.2]
    nlinarith
  have hP : (Phat b c k).eval r = (Cay (k + 3)).eval r + b * (r + 1) * (Cay (k + 2)).eval r := by
    rw [eval_Phat, hfr]; ring
  rw [hP]
  have hσ2 : σ ^ 2 = 1 := by rw [hσ, ← pow_mul, mul_comm, pow_mul]; norm_num
  rcases lt_or_eq_of_le hr0 with hpos | hzero
  · have h32 := cor_3_2 k hrf hpos
    have hσh : 0 < -σ * (Cay (k + 3)).eval r := by
      have : 0 < (-σ * (Cay (k + 3)).eval r) * (-σ * (Cay (k + 2)).eval r) := by
        have : (-σ * (Cay (k + 3)).eval r) * (-σ * (Cay (k + 2)).eval r) =
            σ ^ 2 * ((Cay (k + 3)).eval r * (Cay (k + 2)).eval r) := by ring
        rw [this, hσ2, one_mul]; exact h32
      exact pos_of_mul_pos_left this hσg.le
    have : 0 ≤ b * (r + 1) * (-σ * (Cay (k + 2)).eval r) :=
      mul_nonneg (mul_nonneg hb (by linarith)) hσg.le
    nlinarith
  · subst hzero
    have hb0 : 0 < b := hbr.resolve_left (lt_irrefl 0)
    have hodd := Cay_odd_of_eval_zero hfr
    have hh0 : (Cay (k + 3)).eval 0 = 0 := by
      rw [show k + 3 = (k + 2) + 1 by ring]
      exact Cay_eval_zero_of_odd (by obtain ⟨j, hj⟩ := hodd; exact ⟨j + 1, by omega⟩)
    rw [hh0]
    nlinarith

/-- **The hybrid sign pattern** (A §6 Cases I and II; audit §3.5).  For `k ≥ 1` (`n = k + 3 ≥ 4`),
admissible `b, c`, and `b > 0` or `f(0) ≠ 0` (`n` odd), `P̂` has strictly alternating signs at the
`k + 3 = deg P̂ + 1` points of `hybridSet b k`.  `k = 1` (`n = 4`) is included. -/
theorem Phat_signPattern (hb : 0 ≤ b) (hc : 0 ≤ c) (hbc : c ≤ b ^ 2 / 4 + b + 3) {k : ℕ}
    (hk : 1 ≤ k) (hbranch : 0 < b ∨ (Cay (k + 1)).eval 0 ≠ 0) :
    SignPattern (Phat b c k) (hybridSet b k) := by
  obtain ⟨hcard, hm1, h1, hneg, hnn⟩ := hybridSet_counts hb k
  obtain ⟨hPdeg, hPlc⟩ := Phat_degree hb hc k
  refine ⟨hPlc, by rw [hcard, hPdeg], ?_⟩
  intro t ht
  rcases mem_hybridSet.mp ht with rfl | rfl | ⟨hsq, hs0⟩ | ⟨hrf, hr0⟩
  · rw [hm1, eval_neg_one_Phat, ← mul_pow]; norm_num
  · rw [h1]; simpa using eval_one_Phat hb hc k
  · rw [hneg t hsq hs0]; exact Phat_sign_neg_sep hb hbc hk hsq hs0
  · rw [hnn t hrf hr0]
    refine Phat_sign_nonneg_f hb hrf hr0 ?_
    rcases lt_or_eq_of_le hr0 with h | h
    · exact Or.inl h
    · rcases hbranch with hb' | hf0
      · exact Or.inr hb'
      · have h0 : (Cay (k + 1)).eval 0 = 0 := by
          have := ((mem_roots (Cay_ne_zero k)).mp hrf).eq_zero
          rwa [← h] at this
        exact absurd h0 hf0

end Hybrid

/-! ### Back to the original variable -/

/-- **Transport.**  If the Cayley homogenization `P̂ = homog d p` (with `natDegree p ≤ d`) has degree
`d`, splits, and does not vanish at `-1`, then `p` splits over `ℝ`: explicitly
`p = (lc P̂ / 2^d) ∏_{z root of P̂} ((1 + z) x + (1 - z))`, multiplicities included. -/
theorem splits_of_homog {d : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d) (hs : (homog d p).Splits)
    (hdeg : (homog d p).natDegree = d) (hm1 : (homog d p).eval (-1) ≠ 0) : p.Splits := by
  classical
  set P := homog d p with hP
  have hP0 : P ≠ 0 := fun h => hm1 (by rw [h, eval_zero])
  have hcard : P.roots.card = d := by rw [splits_iff_card_roots.mp hs, hdeg]
  have hZ : ∀ z ∈ P.roots, 1 + z ≠ 0 := by
    intro z hz h
    have : z = -1 := by linarith
    exact hm1 (this ▸ (mem_roots hP0).mp hz)
  set Q : ℝ[X] := C (P.leadingCoeff / 2 ^ d) *
    (P.roots.map (fun z => C (1 + z) * X + C (1 - z))).prod with hQ
  have hpQ : p = Q := by
    apply eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := {x : ℝ | x ≠ 1})
    · intro x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      have h1x : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
      set w := (1 + x) / (1 - x) with hw
      have hw1 : w + 1 = 2 / (1 - x) := by rw [hw]; field_simp; ring
      have hwne : w ≠ -1 := fun h => by
        rw [h] at hw1; have : (2 : ℝ) / (1 - x) ≠ 0 := div_ne_zero two_ne_zero h1x
        exact this (by linarith)
      have hwx : (w - 1) / (w + 1) = x := by
        rw [hw1, hw]; field_simp; ring
      have hev := eval_homog hp hwne
      rw [← hP, hwx, hw1, hs.eval_eq_prod_roots] at hev
      have hfac : ∀ z ∈ P.roots, (1 + z) * x + (1 - z) = (1 - x) * (w - z) := by
        intro z _; rw [hw]; field_simp; ring
      rw [hQ, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
      have hmap : (P.roots.map ((fun q => eval x q) ∘ fun z => C (1 + z) * X + C (1 - z))) =
          P.roots.map (fun z => (1 - x) * (w - z)) := by
        apply Multiset.map_congr rfl
        intro z hz
        simp only [Function.comp, eval_add, eval_mul, eval_C, eval_X]
        exact hfac z hz
      rw [hmap, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard]
      rw [show P.leadingCoeff / 2 ^ d * ((1 - x) ^ d * (P.roots.map (fun z => w - z)).prod) =
          ((1 - x) ^ d / 2 ^ d) * (P.leadingCoeff * (P.roots.map (fun z => w - z)).prod) by ring,
        hev]
      have hone : (1 - x) ^ d / 2 ^ d * (2 / (1 - x)) ^ d = 1 := by
        rw [div_pow, div_mul_div_comm, mul_comm ((1 - x) ^ d) (2 ^ d),
          div_self (mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ h1x))]
      rw [← mul_assoc, hone, one_mul]
    · exact (Set.finite_singleton (1 : ℝ)).infinite_compl
  rw [hpQ, hQ]
  refine (Splits.C _).mul (Splits.multisetProd ?_)
  intro g hg
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hg
  have hfz : C (1 + z) * X + C (1 - z) = C (1 + z) * (X - C (-(1 - z) / (1 + z))) := by
    rw [mul_sub, ← C_mul, mul_div_cancel₀ _ (hZ z hz)]; simp; ring
  rw [hfz]
  exact (Splits.C _).mul (Splits.X_sub_C _)

/-- The Cayley homogenization of `P_n` (`n = k + 3`) is `P̂`. -/
theorem homog_combination (b c : ℝ) (k : ℕ) :
    homog (k + 2) (combination (k + 3) b c) = Phat b c k := by
  have h1 : homog (k + 2) (A (k + 3)) = Cay (k + 3) := (Cay_succ_eq_homog (k + 2)).symm
  have h2 : homog (k + 2) (A (k + 2)) = (X + 1) * Cay (k + 2) := by
    rw [homog_succ (natDegree_A_succ (k + 1)).le, ← Cay_succ_eq_homog (k + 1)]
  have h3 : homog (k + 2) (A (k + 1)) = (X + 1) ^ 2 * Cay (k + 1) := by
    rw [homog_succ (by rw [natDegree_A_succ]; omega), homog_succ (natDegree_A_succ k).le,
      ← Cay_succ_eq_homog k]
    ring
  have hCmul : ∀ (a : ℝ) (q : ℝ[X]) (d : ℕ), homog d (C a * q) = C a * homog d q := by
    intro a q d; rw [← smul_eq_C_mul, LinearMap.map_smul, smul_eq_C_mul]
  rw [combination, show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    LinearMap.map_add, LinearMap.map_add, hCmul, hCmul, h1, h2, h3, Phat]
  ring

/-- **Sufficiency for `n ≥ 4` with `b > 0` or `n` odd** (A §6 Cases I and II). -/
theorem combination_splits_of_branch {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hbc : c ≤ b ^ 2 / 4 + b + 3) {n : ℕ} (hn : 4 ≤ n) (hbr : 0 < b ∨ Odd n) :
    (combination n b c).Splits := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hk : 1 ≤ k := by omega
  have hbranch : 0 < b ∨ (Cay (k + 1)).eval 0 ≠ 0 := by
    rcases hbr with h | h
    · exact Or.inl h
    · right
      intro h0
      have hk' := Cay_odd_of_eval_zero h0
      rw [show k + 3 = k + 1 + 2 by ring] at h
      exact (Nat.not_odd_iff_even.mpr (by
        obtain ⟨j, hj⟩ := hk'; exact ⟨j + 2, by omega⟩)) h
  have hsp := Phat_signPattern hb hc hbc hk hbranch
  have hdeg := (Phat_degree hb hc k).1
  rw [← homog_combination] at hsp hdeg
  apply splits_of_homog (d := k + 2) (by rw [combination_natDegree (by omega)]; omega) hsp.splits hdeg
  rw [homog_combination, eval_neg_one_Phat]
  exact pow_ne_zero _ (by norm_num)

end EulerianRegion
