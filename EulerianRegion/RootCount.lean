module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Normed.Order.Lattice

/-!
# Real roots, signs and test points

Generic infrastructure for counting real roots by sign changes.

* `above s x`: the number of elements of a multiset `s` (with multiplicity) strictly greater than `x`.
* `sign_eval`, `sign_derivative`: for a split polynomial with positive leading coefficient,
  `(-1)^(above roots x) * P x > 0` at non-roots, and, when all roots are simple (`P.roots.Nodup`),
  `(-1)^(above roots r) * P' r > 0` at every root `r`.
* `SignPattern P L`: `P` has positive leading coefficient, the finite test set `L ⊆ ℝ` has
  `natDegree P + 1` points, and `(-1)^(above L t) * P t > 0` for every `t ∈ L` (strictly alternating
  signs read from the right). Consequences, proved with the intermediate value theorem between
  consecutive test points: `P` splits (`SignPattern.splits`), its roots are simple
  (`SignPattern.nodup`), lie strictly between the extreme test points (`SignPattern.root_bounds`),
  satisfy `above roots t = above L t` at test points (`SignPattern.above_roots_eq`),
  `above roots ξ + 1 = above L ξ` at roots (`SignPattern.above_roots_at_root`), and
  `above roots x ≤ above L x ≤ above roots x + 1` in between (`SignPattern.above_roots_bounds`).
  The degree-zero case (one test point, no roots) is included.
* `eval_derivative_sq_sub_of_splits`: `f'(x)² - f(x) f''(x) = f(x)² Σ_z (x - z)⁻²` at non-roots (the second
  logarithmic derivative); mathlib's `Splits.eval_derivative_div_eval_of_ne_zero` gives the first.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace EulerianRegion

/-- `above s x` is the number of elements of the multiset `s` (with multiplicity) that are
strictly greater than `x`. -/
def above (s : Multiset ℝ) (x : ℝ) : ℕ := (s.filter (fun y => x < y)).card

theorem above_zero (x : ℝ) : above 0 x = 0 := by simp [above]

theorem above_cons (a : ℝ) (s : Multiset ℝ) (x : ℝ) :
    above (a ::ₘ s) x = above s x + if x < a then 1 else 0 := by
  unfold above
  by_cases h : x < a
  · simp [Multiset.filter_cons_of_pos _ h, h]
  · simp [Multiset.filter_cons_of_neg _ h, h]

theorem above_le_card (s : Multiset ℝ) (x : ℝ) : above s x ≤ s.card :=
  Multiset.card_le_card (Multiset.filter_le _ _)

/-- Splitting the count at two points `x ≤ y`. -/
theorem above_eq_add_Ioc (s : Multiset ℝ) {x y : ℝ} (hxy : x ≤ y) :
    above s x = above s y + (s.filter (fun z => x < z ∧ z ≤ y)).card := by
  unfold above
  have h := Multiset.filter_add_not (fun z => y < z) (s.filter (fun z => x < z))
  rw [Multiset.filter_filter, Multiset.filter_filter] at h
  have h1 : s.filter (fun z => y < z ∧ x < z) = s.filter (fun z => y < z) :=
    Multiset.filter_congr (fun z _ => ⟨fun h => h.1, fun h => ⟨h, lt_of_le_of_lt hxy h⟩⟩)
  have h2 : s.filter (fun z => ¬ y < z ∧ x < z) = s.filter (fun z => x < z ∧ z ≤ y) :=
    Multiset.filter_congr (fun z _ => ⟨fun h => ⟨h.2, not_lt.mp h.1⟩, fun h => ⟨not_lt.mpr h.2, h.1⟩⟩)
  rw [h1, h2] at h
  rw [← h, Multiset.card_add]

theorem above_antitone (s : Multiset ℝ) {x y : ℝ} (hxy : x ≤ y) : above s y ≤ above s x := by
  rw [above_eq_add_Ioc s hxy]; omega

/-- Sign of a product `∏ (x - r)`: multiplying by `(-1)^(# r > x)` makes it positive. -/
theorem sign_prod_sub (s : Multiset ℝ) {x : ℝ} (hx : x ∉ s) :
    0 < (-1 : ℝ) ^ above s x * (s.map (fun r => x - r)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [above_zero]
  | cons a s ih =>
    have hxa : x ≠ a := fun h => hx (h ▸ Multiset.mem_cons_self _ _)
    have hxs : x ∉ s := fun h => hx (Multiset.mem_cons_of_mem h)
    have ih := ih hxs
    rw [above_cons, Multiset.map_cons, Multiset.prod_cons]
    by_cases h : x < a
    · simp only [h, ite_true, pow_succ]
      have : 0 < a - x := by linarith
      nlinarith
    · simp only [h, ite_false, add_zero]
      have : 0 < x - a := lt_of_le_of_ne (by linarith [not_lt.mp h]) (Ne.symm (sub_ne_zero.mpr hxa))
      nlinarith

/-- Sign of a split polynomial with positive leading coefficient at a non-root. -/
theorem sign_eval {P : ℝ[X]} (hs : P.Splits) (hlc : 0 < P.leadingCoeff) {x : ℝ}
    (hx : ¬ P.IsRoot x) : 0 < (-1 : ℝ) ^ above P.roots x * P.eval x := by
  have hP : P ≠ 0 := fun h => by simp [h] at hlc
  have hxr : x ∉ P.roots := fun h => hx ((mem_roots hP).mp h)
  rw [hs.eval_eq_prod_roots, mul_left_comm]
  exact mul_pos hlc (sign_prod_sub _ hxr)

/-- Sign of the derivative at a simple root of a split polynomial with positive leading
coefficient. -/
theorem sign_derivative {P : ℝ[X]} (hs : P.Splits) (hlc : 0 < P.leadingCoeff)
    (hnd : P.roots.Nodup) {r : ℝ} (hr : r ∈ P.roots) :
    0 < (-1 : ℝ) ^ above P.roots r * (derivative P).eval r := by
  classical
  have hP : P ≠ 0 := fun h => by simp [h] at hlc
  set Q : ℝ[X] := C (P.leadingCoeff⁻¹) * P with hQ
  have hQm : Q.Monic := by
    rw [Monic, hQ, leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ hlc.ne']
  have hQr : Q.roots = P.roots := by rw [hQ, roots_C_mul _ (inv_ne_zero hlc.ne')]
  have hQs : Q.Splits := by
    rw [hQ]; exact (Splits.C _).mul hs
  have hd := hQs.eval_root_derivative hQm (hQr ▸ hr)
  have hPQ : derivative P = C P.leadingCoeff * derivative Q := by
    rw [hQ, derivative_mul, derivative_C, zero_mul, zero_add, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ hlc.ne', C_1, one_mul]
  rw [hPQ, eval_mul, eval_C, hd, hQr]
  have hnot : r ∉ P.roots.erase r := Multiset.Nodup.notMem_erase hnd
  have habove : above (P.roots.erase r) r = above P.roots r := by
    conv_rhs => rw [← Multiset.cons_erase hr]
    rw [above_cons]; simp
  rw [← habove, mul_left_comm]
  exact mul_pos hlc (sign_prod_sub _ hnot)



/-! ### Test-point sign patterns -/

theorem above_val (L : Finset ℝ) (t : ℝ) : above L.val t = (L.filter (fun y => t < y)).card := rfl

/-- Intermediate value theorem in counting form: if `P` has opposite signs at `t < t'`, it has a
root in `(t, t']`, so the number of roots above `t` exceeds the number above `t'`. -/
theorem above_succ_le_of_mul_neg {P : ℝ[X]} (hP : P ≠ 0) {t t' : ℝ} (htt : t < t')
    (hsign : P.eval t * P.eval t' < 0) : above P.roots t' + 1 ≤ above P.roots t := by
  have hcont : ContinuousOn (fun x => P.eval x) (Set.Icc t t') := P.continuous.continuousOn
  obtain ⟨ξ, hξ, hξ0⟩ : ∃ ξ ∈ Set.Ioo t t', P.eval ξ = 0 := by
    rcases lt_or_gt_of_ne (show P.eval t ≠ 0 from fun h => by simp [h] at hsign) with h | h
    · have h' : 0 < P.eval t' := by nlinarith
      exact intermediate_value_Ioo htt.le hcont ⟨h, h'⟩
    · have h' : P.eval t' < 0 := by nlinarith
      exact intermediate_value_Ioo' htt.le hcont ⟨h', h⟩
  rw [above_eq_add_Ioc _ htt.le]
  have : 0 < (P.roots.filter (fun z => t < z ∧ z ≤ t')).card :=
    Multiset.card_pos_iff_exists_mem.mpr
      ⟨ξ, Multiset.mem_filter.mpr ⟨(mem_roots hP).mpr hξ0, hξ.1, hξ.2.le⟩⟩
  omega

/-- The successor of `t` in a finite set `L` (smallest element strictly above `t`). -/
theorem exists_next {L : Finset ℝ} {t : ℝ} {k : ℕ} (hk : above L.val t = k + 1) :
    ∃ t' ∈ L, t < t' ∧ above L.val t' = k ∧ ∀ u ∈ L, t < u → t' ≤ u := by
  classical
  rw [above_val] at hk
  have hne : (L.filter (fun y => t < y)).Nonempty := Finset.card_pos.mp (by omega)
  set t' := (L.filter (fun y => t < y)).min' hne with ht'
  have hmem := Finset.min'_mem _ hne
  rw [← ht', Finset.mem_filter] at hmem
  have hmin : ∀ u ∈ L, t < u → t' ≤ u := fun u hu htu =>
    Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hu, htu⟩)
  refine ⟨t', hmem.1, hmem.2, ?_, hmin⟩
  have heq : L.filter (fun y => t' < y) = (L.filter (fun y => t < y)).erase t' := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hu, h⟩; exact ⟨ne_of_gt h, hu, lt_trans hmem.2 h⟩
    · rintro ⟨hne', hu, h⟩; exact ⟨hu, lt_of_le_of_ne (hmin u hu h) (Ne.symm hne')⟩
  rw [above_val, heq, Finset.card_erase_of_mem (Finset.mem_filter.mpr hmem), hk]
  rfl

/-- The predecessor of `t` in `L` (largest element strictly below `t`). -/
theorem exists_prev {L : Finset ℝ} {t : ℝ} (ht : t ∈ L)
    (hne : (L.filter (fun y => y < t)).Nonempty) :
    ∃ t' ∈ L, t' < t ∧ above L.val t' = above L.val t + 1 ∧
      (L.filter (fun y => y < t')).card + 1 = (L.filter (fun y => y < t)).card ∧
      ∀ u ∈ L, u < t → u ≤ t' := by
  classical
  set t' := (L.filter (fun y => y < t)).max' hne with ht'
  have hmem := Finset.max'_mem _ hne
  rw [← ht', Finset.mem_filter] at hmem
  have hmax : ∀ u ∈ L, u < t → u ≤ t' := fun u hu htu =>
    Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hu, htu⟩)
  refine ⟨t', hmem.1, hmem.2, ?_, ?_, hmax⟩
  · have heq : L.filter (fun y => t' < y) = insert t (L.filter (fun y => t < y)) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hu, h⟩
        rcases lt_trichotomy u t with h' | h' | h'
        · exact absurd (hmax u hu h') (not_le.mpr h)
        · exact Or.inl h'
        · exact Or.inr ⟨hu, h'⟩
      · rintro (rfl | ⟨hu, h⟩)
        · exact ⟨ht, hmem.2⟩
        · exact ⟨hu, lt_trans hmem.2 h⟩
    rw [above_val, above_val, heq, Finset.card_insert_of_notMem (by simp)]
  · have heq : L.filter (fun y => y < t) = insert t' (L.filter (fun y => y < t')) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hu, h⟩
        rcases lt_or_eq_of_le (hmax u hu h) with h' | h'
        · exact Or.inr ⟨hu, h'⟩
        · exact Or.inl h'
      · rintro (rfl | ⟨hu, h⟩)
        · exact ⟨hmem.1, hmem.2⟩
        · exact ⟨hu, lt_trans h hmem.2⟩
    rw [heq, Finset.card_insert_of_notMem (by simp)]

/-- `P` has strictly alternating signs on the finite test set `L`: at each `t ∈ L` the sign of
`P t` is `(-1) ^ (number of test points above t)`, and `L` has `natDegree P + 1` points. -/
structure SignPattern (P : ℝ[X]) (L : Finset ℝ) : Prop where
  lc_pos : 0 < P.leadingCoeff
  card_eq : L.card = P.natDegree + 1
  sign : ∀ t ∈ L, 0 < (-1 : ℝ) ^ above L.val t * P.eval t

namespace SignPattern

variable {P : ℝ[X]} {L : Finset ℝ}

theorem ne_zero (h : SignPattern P L) : P ≠ 0 := fun hP => by simpa [hP] using h.lc_pos

theorem eval_ne_zero (h : SignPattern P L) {t : ℝ} (ht : t ∈ L) : P.eval t ≠ 0 := fun h0 => by
  simpa [h0] using h.sign t ht

theorem mul_neg_of_succ (h : SignPattern P L) {t t' : ℝ} (ht : t ∈ L) (ht' : t' ∈ L)
    {k : ℕ} (hk : above L.val t = k + 1) (hk' : above L.val t' = k) :
    P.eval t * P.eval t' < 0 := by
  have h1 := h.sign t ht
  have h2 := h.sign t' ht'
  rw [hk, pow_succ] at h1
  rw [hk'] at h2
  have hsq : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  nlinarith [mul_pos h1 h2]

/-- Lower bound: at least as many roots above `t` as test points above `t`. -/
theorem le_above_roots (h : SignPattern P L) :
    ∀ k : ℕ, ∀ t ∈ L, above L.val t = k → k ≤ above P.roots t := by
  intro k
  induction k with
  | zero => intros; exact Nat.zero_le _
  | succ k ih =>
    intro t ht hk
    obtain ⟨t', ht'L, htt', hk', -⟩ := exists_next hk
    have := ih t' ht'L hk'
    have := above_succ_le_of_mul_neg h.ne_zero htt' (h.mul_neg_of_succ ht ht'L hk hk')
    omega

theorem exists_min (h : SignPattern P L) :
    ∃ t₀ ∈ L, above L.val t₀ = P.natDegree ∧ ∀ u ∈ L, t₀ ≤ u := by
  classical
  have hne : L.Nonempty := Finset.card_pos.mp (by rw [h.card_eq]; omega)
  refine ⟨L.min' hne, Finset.min'_mem _ _, ?_, fun u hu => Finset.min'_le _ _ hu⟩
  have heq : L.filter (fun y => L.min' hne < y) = L.erase (L.min' hne) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hu, h'⟩; exact ⟨ne_of_gt h', hu⟩
    · rintro ⟨hne', hu⟩; exact ⟨hu, lt_of_le_of_ne (Finset.min'_le _ _ hu) (Ne.symm hne')⟩
  rw [above_val, heq, Finset.card_erase_of_mem (Finset.min'_mem _ _), h.card_eq]
  rfl

theorem card_roots (h : SignPattern P L) : P.roots.card = P.natDegree := by
  obtain ⟨t₀, ht₀, hk, -⟩ := h.exists_min
  have := h.le_above_roots _ t₀ ht₀ hk
  have := above_le_card P.roots t₀
  have := card_roots' P
  omega

/-- `P` splits over `ℝ`. -/
theorem splits (h : SignPattern P L) : P.Splits :=
  splits_iff_card_roots.mpr h.card_roots

theorem below_card_add (h : SignPattern P L) {t : ℝ} (ht : t ∈ L) :
    above L.val t + (L.filter (fun y => y < t)).card + 1 = P.natDegree + 1 := by
  classical
  rw [← h.card_eq, above_val]
  have h1 := Finset.card_filter_add_card_filter_not (s := L) (fun y => t < y)
  have h2 : L.filter (fun y => ¬ t < y) = insert t (L.filter (fun y => y < t)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_insert, not_lt]
    constructor
    · rintro ⟨hu, h'⟩
      rcases lt_or_eq_of_le h' with h'' | h''
      · exact Or.inr ⟨hu, h''⟩
      · exact Or.inl h''
    · rintro (rfl | ⟨hu, h'⟩)
      · exact ⟨ht, le_rfl⟩
      · exact ⟨hu, h'.le⟩
  rw [h2, Finset.card_insert_of_notMem (by simp)] at h1
  omega

/-- Upper bound, by induction from the left end. -/
theorem above_roots_add_le (h : SignPattern P L) :
    ∀ j : ℕ, ∀ t ∈ L, (L.filter (fun y => y < t)).card = j →
      above P.roots t + j ≤ P.natDegree := by
  intro j
  induction j with
  | zero =>
    intro t _ _
    have := above_le_card P.roots t
    have := card_roots' P
    omega
  | succ j ih =>
    intro t ht hj
    have hne : (L.filter (fun y => y < t)).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨t', ht'L, ht't, habove, hcard, -⟩ := exists_prev ht hne
    have := ih t' ht'L (by omega)
    have := above_succ_le_of_mul_neg h.ne_zero ht't (h.mul_neg_of_succ ht'L ht habove rfl)
    omega

/-- Exact count at the test points. -/
theorem above_roots_eq (h : SignPattern P L) {t : ℝ} (ht : t ∈ L) :
    above P.roots t = above L.val t := by
  have h1 := h.le_above_roots _ t ht rfl
  have h2 := h.above_roots_add_le _ t ht rfl
  have h3 := h.below_card_add ht
  omega

end SignPattern


namespace SignPattern

variable {P : ℝ[X]} {L : Finset ℝ}

theorem exists_max (h : SignPattern P L) :
    ∃ t₁ ∈ L, above L.val t₁ = 0 ∧ ∀ u ∈ L, u ≤ t₁ := by
  classical
  have hne : L.Nonempty := Finset.card_pos.mp (by rw [h.card_eq]; omega)
  refine ⟨L.max' hne, Finset.max'_mem _ _, ?_, fun u hu => Finset.le_max' _ _ hu⟩
  rw [above_val, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u hu
  exact not_lt.mpr (Finset.le_max' _ _ hu)

/-- Every root lies strictly between the extreme test points. -/
theorem root_bounds (h : SignPattern P L) {ξ : ℝ} (hξ : ξ ∈ P.roots) :
    (∃ t₀ ∈ L, t₀ < ξ) ∧ (∃ t₁ ∈ L, ξ < t₁) := by
  constructor
  · obtain ⟨t₀, ht₀, hk, -⟩ := h.exists_min
    refine ⟨t₀, ht₀, ?_⟩
    have heq := h.above_roots_eq ht₀
    rw [hk, ← h.card_roots] at heq
    unfold above at heq
    have := (Multiset.filter_eq_self.mp (Multiset.eq_of_le_of_card_le (Multiset.filter_le _ _)
      heq.symm.le)) ξ hξ
    exact this
  · obtain ⟨t₁, ht₁, hk, -⟩ := h.exists_max
    refine ⟨t₁, ht₁, ?_⟩
    have heq := h.above_roots_eq ht₁
    rw [hk] at heq
    unfold above at heq
    rw [Multiset.card_eq_zero, Multiset.filter_eq_nil] at heq
    rcases lt_trichotomy ξ t₁ with h' | h' | h'
    · exact h'
    · exact absurd ((mem_roots h.ne_zero).mp (h' ▸ hξ)) (h.eval_ne_zero ht₁)
    · exact absurd h' (heq ξ hξ)

/-- Bracketing a point `x ∉ L` strictly inside the range of `L` by consecutive test points. -/
theorem _root_.EulerianRegion.exists_bracket {L : Finset ℝ} {x : ℝ} (hxL : x ∉ L)
    (hlo : ∃ t₀ ∈ L, t₀ < x) (hhi : ∃ t₁ ∈ L, x < t₁) :
    ∃ tm ∈ L, ∃ tp ∈ L, tm < x ∧ x < tp ∧ above L.val tm = above L.val tp + 1 ∧
      above L.val tm = above L.val x := by
  classical
  obtain ⟨t₁, ht₁, hxt₁⟩ := hhi
  obtain ⟨t₀, ht₀, ht₀x⟩ := hlo
  have hne : (L.filter (fun y => x < y)).Nonempty := ⟨t₁, Finset.mem_filter.mpr ⟨ht₁, hxt₁⟩⟩
  set tp := (L.filter (fun y => x < y)).min' hne with htp
  have hmem := Finset.min'_mem _ hne
  rw [← htp, Finset.mem_filter] at hmem
  have hmin : ∀ u ∈ L, x < u → tp ≤ u := fun u hu hxu =>
    Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hu, hxu⟩)
  have habove_tp : above L.val tp + 1 = above L.val x := by
    have heq : L.filter (fun y => tp < y) = (L.filter (fun y => x < y)).erase tp := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hu, h'⟩; exact ⟨ne_of_gt h', hu, lt_trans hmem.2 h'⟩
      · rintro ⟨hne', hu, h'⟩; exact ⟨hu, lt_of_le_of_ne (hmin u hu h') (Ne.symm hne')⟩
    rw [above_val, above_val, heq, Finset.card_erase_of_mem (Finset.mem_filter.mpr hmem)]
    exact Nat.sub_add_cancel (Finset.card_pos.mpr hne)
  have hne' : (L.filter (fun y => y < tp)).Nonempty :=
    ⟨t₀, Finset.mem_filter.mpr ⟨ht₀, lt_trans ht₀x hmem.2⟩⟩
  obtain ⟨tm, htmL, htmtp, habove, -, hmax⟩ := exists_prev hmem.1 hne'
  have htmx : tm < x := by
    rcases lt_trichotomy tm x with h' | h' | h'
    · exact h'
    · exact absurd (h' ▸ htmL) hxL
    · exact absurd (hmin tm htmL h') (not_le.mpr htmtp)
  exact ⟨tm, htmL, tp, hmem.1, htmx, hmem.2, habove, by omega⟩

/-- Exactly one root (with multiplicity) between consecutive test points. -/
theorem card_Ioc_eq_one (h : SignPattern P L) {tm tp : ℝ} (htm : tm ∈ L) (htp : tp ∈ L)
    (hlt : tm < tp) (habove : above L.val tm = above L.val tp + 1) :
    (P.roots.filter (fun z => tm < z ∧ z ≤ tp)).card = 1 := by
  have := above_eq_add_Ioc P.roots hlt.le
  rw [h.above_roots_eq htm, h.above_roots_eq htp] at this
  omega

/-- The roots are simple. -/
theorem nodup (h : SignPattern P L) : P.roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro ξ
  by_cases hξ : ξ ∈ P.roots
  · have hξL : ξ ∉ L := fun hL => h.eval_ne_zero hL ((mem_roots h.ne_zero).mp hξ)
    obtain ⟨hlo, hhi⟩ := h.root_bounds hξ
    obtain ⟨tm, htm, tp, htp, htmx, hxtp, habove, -⟩ := exists_bracket hξL hlo hhi
    have h1 := h.card_Ioc_eq_one htm htp (lt_trans htmx hxtp) habove
    rw [← Multiset.count_filter_of_pos (p := fun z => tm < z ∧ z ≤ tp) ⟨htmx, hxtp.le⟩]
    rw [← h1]
    exact Multiset.count_le_card _ _
  · rw [Multiset.count_eq_zero.mpr hξ]; omega

/-- At a root `ξ`, the roots above `ξ` are one fewer than the test points above `ξ`. -/
theorem above_roots_at_root (h : SignPattern P L) {ξ : ℝ} (hξ : ξ ∈ P.roots) :
    above P.roots ξ + 1 = above L.val ξ := by
  have hξL : ξ ∉ L := fun hL => h.eval_ne_zero hL ((mem_roots h.ne_zero).mp hξ)
  obtain ⟨hlo, hhi⟩ := h.root_bounds hξ
  obtain ⟨tm, htm, tp, htp, htmx, hxtp, habove, habx⟩ := exists_bracket hξL hlo hhi
  have h1 := above_eq_add_Ioc P.roots htmx.le
  have h2 := above_eq_add_Ioc P.roots hxtp.le
  have h3 := h.card_Ioc_eq_one htm htp (lt_trans htmx hxtp) habove
  have h4 : 0 < (P.roots.filter (fun z => tm < z ∧ z ≤ ξ)).card :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨ξ, Multiset.mem_filter.mpr ⟨hξ, htmx, le_rfl⟩⟩
  rw [h.above_roots_eq htm] at h1
  rw [h.above_roots_eq htp] at h2
  omega

/-- Between the extreme test points, the root count is within one of the test-point count. -/
theorem above_roots_bounds (h : SignPattern P L) {x : ℝ} (hxL : x ∉ L)
    (hlo : ∃ t₀ ∈ L, t₀ < x) (hhi : ∃ t₁ ∈ L, x < t₁) :
    above P.roots x ≤ above L.val x ∧ above L.val x ≤ above P.roots x + 1 := by
  obtain ⟨tm, htm, tp, htp, htmx, hxtp, habove, habx⟩ := exists_bracket hxL hlo hhi
  have h1 := above_antitone P.roots htmx.le
  have h2 := above_antitone P.roots hxtp.le
  rw [h.above_roots_eq htm] at h1
  rw [h.above_roots_eq htp] at h2
  omega

end SignPattern

/-! ### Logarithmic derivatives -/

theorem prod_X_sub_C_derivative_sq_sub (s : Multiset ℝ) {x : ℝ} (hx : x ∉ s) :
    ((derivative (s.map (fun a => X - C a)).prod).eval x) ^ 2 -
        ((s.map (fun a => X - C a)).prod).eval x *
          ((derivative (derivative (s.map (fun a => X - C a)).prod)).eval x) =
      (((s.map (fun a => X - C a)).prod).eval x) ^ 2 *
        (s.map (fun z => 1 / (x - z) ^ 2)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have hxa : x - a ≠ 0 := sub_ne_zero.mpr (fun h => hx (h ▸ Multiset.mem_cons_self _ _))
    have ih := ih (fun h => hx (Multiset.mem_cons_of_mem h))
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, derivative_mul,
      derivative_add, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add,
      eval_mul, eval_sub, eval_X, eval_C] at ih ⊢
    set q := ((s.map (fun a => X - C a)).prod).eval x
    set q1 := (derivative (s.map (fun a => X - C a)).prod).eval x
    set q2 := (derivative (derivative (s.map (fun a => X - C a)).prod)).eval x
    set S := (s.map (fun z => 1 / (x - z) ^ 2)).sum
    have hrhs : ((x - a) * q) ^ 2 * (1 / (x - a) ^ 2 + S) = q ^ 2 + (x - a) ^ 2 * (q ^ 2 * S) := by
      field_simp
    rw [hrhs]
    linear_combination (x - a) ^ 2 * ih

/-- Second logarithmic derivative of a split polynomial at a non-root:
`f'(x)² - f(x) f''(x) = f(x)² Σ_z 1/(x - z)²`. -/
theorem eval_derivative_sq_sub_of_splits {P : ℝ[X]} (hs : P.Splits) {x : ℝ} (hx : P.eval x ≠ 0) :
    ((derivative P).eval x) ^ 2 - P.eval x * (derivative (derivative P)).eval x =
      (P.eval x) ^ 2 * (P.roots.map (fun z => 1 / (x - z) ^ 2)).sum := by
  have hP : P ≠ 0 := fun h => by simp [h] at hx
  have hxr : x ∉ P.roots := fun h => hx ((mem_roots hP).mp h)
  have key := prod_X_sub_C_derivative_sq_sub P.roots hxr
  have hfac := hs.eq_prod_roots
  rw [hfac]
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C]
  rw [← hfac]
  linear_combination P.leadingCoeff ^ 2 * key

end EulerianRegion
