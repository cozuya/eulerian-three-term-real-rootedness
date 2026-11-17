module

public import EulerianRegion.Central

/-!
# The separator `q` and the hybrid test points (A §§5–6, audit §§3.4–3.5)

Let `f = C_{k+1}` (`k ≥ 1`, i.e. `m = k + 1 ≥ 2` and `n = k + 3 ≥ 4` in the source), `α = 1 + b/2`.

* `sep α f = T f + α (X + 1) f` is the separator `q = g + α (z + 1) f`.  `sep_degree`: degree
  `natDegree f + 1`, positive leading coefficient.  `sep_signPattern`: strictly alternating signs at
  `-1`, the roots of `f`, and `1` (`q(r) = (r² - 1) f'(r)`, `q(1) > 0`, `q(-1) = -2 f(-1)`); hence
  (`interlace_step_*` in `Cayley`) `q` has simple roots in `(-1, 1)`, one in each gap of `f`, no
  common root with `f`, and `N_q(s) = N_f(s)` at the roots `s` of `q`.
* `sep_nonnegCount`: `q` and `f` have the same number of roots `≥ 0`.  If `f(0) = 0` (Case II) this
  is interlacing; if `f(0) ≠ 0` (Case I, `f` even) then `q(0) = α f(0)` and the root of `q` in the
  central gap is negative (`sep_nonnegCount_of`, via `above_roots_bounds` and a parity argument).
* `hybridSet b k`: `-1`, the negative roots of `q`, the nonnegative roots of `f`, and `1` — the
  ordered test points of A §6 for both parities (the point `0` is present exactly when `f(0) = 0`).
  `hybridSet_counts`: it has `k + 3` points (the degree of `P̂` is `k + 2`, proved as
  `Phat_degree` in `Sufficiency`), and the number of test points above each point is `k + 2` at
  `-1`, `0` at `1`, and `N_f(t) + 1` at every other test point `t`.
* `m = 2` (`k = 1`): `f = C_2 = 2z`, `Cay_two_roots`; covered by the general statements.
* Parity at `0`: `Cay_eval_zero_of_odd`, `Cay_parity_zero`, `Cay_odd_of_eval_zero`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace EulerianRegion

/-! ### The separator `q = g + α (z + 1) f` (A §5, audit §3.4) -/

/-- `q = T f + α (X + 1) f`. -/
def sep (α : ℝ) (f : ℝ[X]) : ℝ[X] := T f + C α * (X + 1) * f

theorem eval_sep (α : ℝ) (f : ℝ[X]) (z : ℝ) :
    (sep α f).eval z = (T f).eval z + α * (z + 1) * f.eval z := by
  simp [sep]

/-- Degree and leading coefficient of `X + 1` times a polynomial. -/
theorem X_add_one_mul_degree {f : ℝ[X]} (hf : f ≠ 0) :
    ((X + 1) * f).natDegree = f.natDegree + 1 ∧ ((X + 1) * f).leadingCoeff = f.leadingCoeff := by
  have hm : (X + 1 : ℝ[X]).Monic := by simpa using monic_X_add_C (1 : ℝ)
  have h1 : (X + 1 : ℝ[X]).natDegree = 1 := by simp
  refine ⟨?_, by rw [leadingCoeff_mul, hm.leadingCoeff, one_mul]⟩
  rw [natDegree_mul hm.ne_zero hf, h1]; ring

theorem sep_degree {α : ℝ} (hα : 0 ≤ α) {f : ℝ[X]} (hf : RootedIn f) :
    (sep α f).natDegree = f.natDegree + 1 ∧ 0 < (sep α f).leadingCoeff := by
  obtain ⟨hTd, hTl⟩ := T_degree rfl hf.ne_zero
  obtain ⟨hXd, hXl⟩ := X_add_one_mul_degree hf.ne_zero
  have hT1 : (T f).coeff (f.natDegree + 1) = ((f.natDegree : ℝ) + 2) * f.leadingCoeff := by
    rw [← hTl, leadingCoeff, hTd]
  have hX1 : ((X + 1) * f).coeff (f.natDegree + 1) = f.leadingCoeff := by
    rw [← hXl, leadingCoeff, hXd]
  have hcoeff : (sep α f).coeff (f.natDegree + 1) =
      ((f.natDegree : ℝ) + 2) * f.leadingCoeff + α * f.leadingCoeff := by
    simp only [sep, coeff_add, mul_assoc, coeff_C_mul, hT1, hX1]
  have hpos : 0 < ((f.natDegree : ℝ) + 2) * f.leadingCoeff + α * f.leadingCoeff := by
    have := hf.lc_pos; positivity
  have hle : (sep α f).natDegree ≤ f.natDegree + 1 := by
    rw [sep, mul_assoc]
    refine (natDegree_add_le _ _).trans (max_le hTd.le ?_)
    exact (natDegree_C_mul_le _ _).trans hXd.le
  have hdeg : (sep α f).natDegree = f.natDegree + 1 :=
    le_antisymm hle (le_natDegree_of_ne_zero (by rw [hcoeff]; exact hpos.ne'))
  exact ⟨hdeg, by rw [leadingCoeff, hdeg, hcoeff]; exact hpos⟩

/-- The separator has strictly alternating signs at `-1`, the roots of `f`, and `1`. -/
theorem sep_signPattern {α : ℝ} (hα : 0 ≤ α) {f : ℝ[X]} (hf : RootedIn f) :
    SignPattern (sep α f) (testSet f) := by
  obtain ⟨hd, hl⟩ := sep_degree hα hf
  refine interlace_step hf hd hl ?_ ?_ ?_
  · intro r hr
    rw [eval_sep, eval_T, (mem_roots hf.ne_zero).mp hr]; ring
  · rw [eval_sep, eval_one_T]
    have := hf.eval_one_pos
    nlinarith
  · rw [eval_sep, eval_neg_one_T]; ring

/-! ### Counting nonnegative roots -/

/-- Number of roots `≥ 0`. -/
def nonnegCount (s : Multiset ℝ) : ℕ := (s.filter (fun y => 0 ≤ y)).card

theorem nonnegCount_eq_above_of_not_mem {s : Multiset ℝ} (h0 : (0 : ℝ) ∉ s) :
    nonnegCount s = above s 0 := by
  unfold nonnegCount above
  congr 1
  apply Multiset.filter_congr
  intro y hy
  exact ⟨fun h => lt_of_le_of_ne h (fun e => h0 (e ▸ hy)), le_of_lt⟩

theorem nonnegCount_eq_above_add_one_of_mem {s : Multiset ℝ} (hnd : s.Nodup) (h0 : (0 : ℝ) ∈ s) :
    nonnegCount s = above s 0 + 1 := by
  classical
  unfold nonnegCount above
  have hsplit : s.filter (fun y => 0 ≤ y) = 0 ::ₘ s.filter (fun y => 0 < y) := by
    rw [← Multiset.cons_erase h0]
    rw [Multiset.filter_cons_of_pos _ le_rfl, Multiset.filter_cons_of_neg _ (lt_irrefl 0)]
    congr 1
    apply Multiset.filter_congr
    intro y hy
    have : y ≠ 0 := fun e => (Multiset.Nodup.notMem_erase hnd) (e ▸ hy)
    exact ⟨fun h => lt_of_le_of_ne h (Ne.symm this), le_of_lt⟩
  rw [hsplit, Multiset.card_cons]


/-- **Nonnegative roots of the separator** (generic form).  If `α > 0`, `f` has simple roots in
`(-1, 1)`, and `(T f)(0) = 0` whenever `f(0) ≠ 0`, then `q = T f + α (z+1) f` and `f` have the same
number of roots `≥ 0`.  If `f(0) = 0` this is consecutive interlacing; otherwise `q(0) = α f(0)`
and the root of `q` in the central gap is negative (A §6 Case I). -/
theorem sep_nonnegCount_of {α : ℝ} (hα : 0 < α) {f : ℝ[X]} (hf : RootedIn f)
    (hpar : f.eval 0 ≠ 0 → (T f).eval 0 = 0) :
    nonnegCount (sep α f).roots = nonnegCount f.roots := by
  classical
  have hq := sep_signPattern hα.le hf
  have hqR := interlace_step_rootedIn hf hq
  by_cases hf0 : f.eval 0 = 0
  · have h0f : (0 : ℝ) ∈ f.roots := (mem_roots hf.ne_zero).mpr hf0
    obtain ⟨habove, hq0⟩ := interlace_step_above_at_f_root hf hq h0f
    have h0q : (0 : ℝ) ∉ (sep α f).roots := fun h => hq0 ((mem_roots hqR.ne_zero).mp h)
    rw [nonnegCount_eq_above_of_not_mem h0q, nonnegCount_eq_above_add_one_of_mem hf.nodup h0f,
      habove]
  · have hq0val : (sep α f).eval 0 = α * f.eval 0 := by
      rw [eval_sep, hpar hf0]; ring
    have hq0 : (sep α f).eval 0 ≠ 0 := by rw [hq0val]; exact mul_ne_zero hα.ne' hf0
    have h0q : (0 : ℝ) ∉ (sep α f).roots := fun h => hq0 ((mem_roots hqR.ne_zero).mp h)
    have h0f : (0 : ℝ) ∉ f.roots := fun h => hf0 ((mem_roots hf.ne_zero).mp h)
    rw [nonnegCount_eq_above_of_not_mem h0q, nonnegCount_eq_above_of_not_mem h0f]
    have hsq := sign_eval hqR.splits hqR.lc_pos (show ¬ (sep α f).IsRoot 0 from hq0)
    have hsf := sign_eval hf.splits hf.lc_pos (show ¬ f.IsRoot 0 from hf0)
    rw [hq0val] at hsq
    have h0L : (0 : ℝ) ∉ testSet f := by
      simp only [testSet, Finset.mem_insert, Multiset.mem_toFinset, not_or]
      exact ⟨by norm_num, by norm_num, h0f⟩
    obtain ⟨hb1, hb2⟩ := hq.above_roots_bounds h0L ⟨-1, by simp [testSet], by norm_num⟩
      ⟨1, by simp [testSet], by norm_num⟩
    rw [above_testSet hf, ite_eq_left (by norm_num : (0 : ℝ) < 1),
      ite_eq_right (by norm_num : ¬ (0 : ℝ) < -1), add_zero] at hb1 hb2
    rcases Nat.lt_or_ge (above (sep α f).roots 0) (above f.roots 0 + 1) with hlt | hge
    · omega
    · have heq : above (sep α f).roots 0 = above f.roots 0 + 1 := by omega
      rw [heq, pow_succ] at hsq
      have : 0 < (-1 : ℝ) ^ above f.roots 0 * f.eval 0 * α := mul_pos hsf hα
      nlinarith

/-- Parity at `0`: `C_{k+1}(0) = 0` for odd `k`. -/
theorem Cay_eval_zero_of_odd {k : ℕ} (hk : Odd k) : (Cay (k + 1)).eval 0 = 0 := by
  have h := eval_neg_Cay k 0
  rw [neg_zero, hk.neg_one_pow] at h
  linarith

/-- If `C_{k+1}(0) ≠ 0` then `C_{k+2}(0) = 0`. -/
theorem Cay_parity_zero (k : ℕ) :
    (Cay (k + 1)).eval 0 ≠ 0 → (T (Cay (k + 1))).eval 0 = 0 := by
  intro h
  rcases Nat.even_or_odd k with he | ho
  · rw [← Cay_succ_succ]; exact Cay_eval_zero_of_odd (k := k + 1) he.add_one
  · exact absurd (Cay_eval_zero_of_odd ho) h

theorem sep_nonnegCount {α : ℝ} (hα : 0 < α) (k : ℕ) :
    nonnegCount (sep α (Cay (k + 1))).roots = nonnegCount (Cay (k + 1)).roots :=
  sep_nonnegCount_of hα (Cay_rootedIn k) (Cay_parity_zero k)

/-! ### Splitting counts by sign -/

theorem above_split (s : Multiset ℝ) (x : ℝ) :
    above s x = above (s.filter (fun y => y < 0)) x + above (s.filter (fun y => 0 ≤ y)) x := by
  unfold above
  rw [Multiset.filter_filter, Multiset.filter_filter, ← Multiset.card_add]
  congr 1
  rw [← Multiset.filter_add_not (fun y => y < 0) (s.filter (fun y => x < y)),
    Multiset.filter_filter, Multiset.filter_filter]
  congr 1
  · exact Multiset.filter_congr (fun y _ => by tauto)
  · exact Multiset.filter_congr (fun y _ => by simp only [not_lt]; tauto)

theorem above_nonneg_of_neg (s : Multiset ℝ) {x : ℝ} (hx : x < 0) :
    above (s.filter (fun y => 0 ≤ y)) x = nonnegCount s := by
  unfold above nonnegCount
  rw [Multiset.filter_filter]
  congr 1
  exact Multiset.filter_congr (fun y _ => ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le hx h, h⟩⟩)

theorem above_neg_of_nonneg (s : Multiset ℝ) {x : ℝ} (hx : 0 ≤ x) :
    above (s.filter (fun y => y < 0)) x = 0 := by
  unfold above
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro y hy h
  exact absurd (lt_of_le_of_lt hx h) (not_lt.mpr (Multiset.mem_filter.mp hy).2.le)

theorem above_nonneg_of_nonneg (s : Multiset ℝ) {x : ℝ} (hx : 0 ≤ x) :
    above (s.filter (fun y => 0 ≤ y)) x = above s x := by
  have := above_split s x
  rw [above_neg_of_nonneg s hx, zero_add] at this
  exact this.symm

theorem above_union_val {A B : Finset ℝ} (hAB : Disjoint A B) (t : ℝ) :
    above (A ∪ B).val t = above A.val t + above B.val t := by
  classical
  rw [above_val, above_val, above_val, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hAB)]

theorem Finset_filter_val_of_nodup {s : Multiset ℝ} (hs : s.Nodup) (p : ℝ → Prop) [DecidablePred p] :
    (s.toFinset.filter p).val = s.filter p := by
  rw [Finset.filter_val, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hs]

/-- If `0` is a root of `C_{k+1}`, then `k` is odd. -/
theorem Cay_odd_of_eval_zero {k : ℕ} (h0 : (Cay (k + 1)).eval 0 = 0) : Odd k := by
  rcases Nat.even_or_odd k with he | ho
  · exfalso
    have hf := Cay_rootedIn k
    have h0r : (0 : ℝ) ∈ (Cay (k + 1)).roots := (mem_roots hf.ne_zero).mpr h0
    have hd := sign_derivative hf.splits hf.lc_pos hf.nodup h0r
    have hg : (Cay (k + 2)).eval 0 = 0 := Cay_eval_zero_of_odd (k := k + 1) he.add_one
    rw [Cay_succ_succ, eval_T, h0] at hg
    have : (derivative (Cay (k + 1))).eval 0 = 0 := by linarith
    rw [this, mul_zero] at hd
    exact lt_irrefl _ hd
  · exact ho

/-! ### The hybrid test points (A §6, audit §3.5) -/

/-- Negative roots of the separator `q` (with `α = 1 + b/2`) and nonnegative roots of `f = C_{k+1}`,
together with `±1`. -/
def hybridSet (b : ℝ) (k : ℕ) : Finset ℝ :=
  insert (-1) (insert 1 (((sep (1 + b / 2) (Cay (k + 1))).roots.toFinset.filter (fun y => y < 0)) ∪
    ((Cay (k + 1)).roots.toFinset.filter (fun y => 0 ≤ y))))

theorem hybrid_disjoint (b : ℝ) (k : ℕ) :
    Disjoint ((sep (1 + b / 2) (Cay (k + 1))).roots.toFinset.filter (fun y => y < 0))
      ((Cay (k + 1)).roots.toFinset.filter (fun y => 0 ≤ y)) := by
  rw [Finset.disjoint_left]
  intro y hy hy'
  exact absurd (Finset.mem_filter.mp hy').2 (not_le.mpr (Finset.mem_filter.mp hy).2)

/-- Membership in the hybrid test set. -/
theorem mem_hybridSet {b : ℝ} {k : ℕ} {t : ℝ} :
    t ∈ hybridSet b k ↔ t = -1 ∨ t = 1 ∨ (t ∈ (sep (1 + b / 2) (Cay (k + 1))).roots ∧ t < 0) ∨
      (t ∈ (Cay (k + 1)).roots ∧ 0 ≤ t) := by
  simp [hybridSet, Finset.mem_filter, Multiset.mem_toFinset]

/-- Counting data for the hybrid test set (A §6 Cases I–II).  With `f = C_{k+1}`, `q` the separator
for `α = 1 + b/2`:
* `card = k + 3` (one more than the degree `k + 2` of `P̂`, see `Phat_degree`);
* `above` at `-1` is `k + 2`, at `1` is `0`;
* at a negative root `s` of `q` it is `N_f(s) + 1`, at a nonnegative root `r` of `f` it is
  `N_f(r) + 1`, where `N_f(x)` counts roots of `f` above `x`. -/
theorem hybridSet_counts {b : ℝ} (hb : 0 ≤ b) (k : ℕ) :
    (hybridSet b k).card = k + 3 ∧
    above (hybridSet b k).val (-1) = k + 2 ∧
    above (hybridSet b k).val 1 = 0 ∧
    (∀ s ∈ (sep (1 + b / 2) (Cay (k + 1))).roots, s < 0 →
      above (hybridSet b k).val s = above (Cay (k + 1)).roots s + 1) ∧
    (∀ r ∈ (Cay (k + 1)).roots, 0 ≤ r →
      above (hybridSet b k).val r = above (Cay (k + 1)).roots r + 1) := by
  classical
  set α := 1 + b / 2 with hαdef
  have hα : 0 < α := by rw [hαdef]; linarith
  have hf := Cay_rootedIn k
  have hq := sep_signPattern hα.le hf
  have hqR := interlace_step_rootedIn hf hq
  set negQ := (sep α (Cay (k + 1))).roots.toFinset.filter (fun y => y < 0) with hnegQ
  set nnF := (Cay (k + 1)).roots.toFinset.filter (fun y => 0 ≤ y) with hnnF
  have hdisj : Disjoint negQ nnF := hybrid_disjoint b k
  have hnegQval : negQ.val = (sep α (Cay (k + 1))).roots.filter (fun y => y < 0) :=
    Finset_filter_val_of_nodup hqR.nodup _
  have hnnFval : nnF.val = (Cay (k + 1)).roots.filter (fun y => 0 ≤ y) :=
    Finset_filter_val_of_nodup hf.nodup _
  have hU : ∀ y ∈ negQ ∪ nnF, -1 < y ∧ y < 1 := by
    intro y hy
    rcases Finset.mem_union.mp hy with h | h
    · exact hqR.mem y (Multiset.mem_toFinset.mp (Finset.mem_filter.mp h).1)
    · exact hf.mem y (Multiset.mem_toFinset.mp (Finset.mem_filter.mp h).1)
  have h1U : (1 : ℝ) ∉ negQ ∪ nnF := fun h => lt_irrefl _ (hU 1 h).2
  have hm1U : (-1 : ℝ) ∉ insert 1 (negQ ∪ nnF) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨by norm_num, fun h => lt_irrefl _ (hU (-1) h).1⟩
  have hL : hybridSet b k = insert (-1) (insert 1 (negQ ∪ nnF)) := rfl
  have habove : ∀ t, above (hybridSet b k).val t =
      above negQ.val t + above nnF.val t + (if t < 1 then 1 else 0) + (if t < -1 then 1 else 0) := by
    intro t
    rw [hL, above_insert_val hm1U, above_insert_val h1U, above_union_val hdisj]
  have hcount := sep_nonnegCount hα k
  have hqcard : (sep α (Cay (k + 1))).roots.card = k + 1 := by
    rw [hqR.card_roots, (sep_degree hα.le hf).1, natDegree_Cay]
  have hnegcard0 : negQ.card + nonnegCount (sep α (Cay (k + 1))).roots =
      (sep α (Cay (k + 1))).roots.card := by
    rw [Finset.card_def, hnegQval]
    unfold nonnegCount
    rw [← Multiset.card_add]
    congr 1
    conv_rhs => rw [← Multiset.filter_add_not (fun y => y < 0) (sep α (Cay (k + 1))).roots]
    congr 1
    exact Multiset.filter_congr (fun y _ => not_lt.symm)
  have hnncard : nnF.card = nonnegCount (Cay (k + 1)).roots := by
    rw [Finset.card_def, hnnFval]; rfl
  have hcard : (hybridSet b k).card = k + 3 := by
    rw [hL, Finset.card_insert_of_notMem hm1U, Finset.card_insert_of_notMem h1U,
      Finset.card_union_of_disjoint hdisj, hnncard, ← hcount]
    omega
  refine ⟨hcard, ?_, ?_, ?_, ?_⟩
  · have h1 : above negQ.val (-1) = negQ.card := by
      rw [above_val, Finset.filter_true_of_mem (fun y hy => (hU y (Finset.mem_union_left _ hy)).1)]
    have h2 : above nnF.val (-1) = nnF.card := by
      rw [above_val, Finset.filter_true_of_mem (fun y hy => (hU y (Finset.mem_union_right _ hy)).1)]
    rw [habove, h1, h2, ite_eq_left (by norm_num), ite_eq_right (by norm_num), hnncard, ← hcount]
    omega
  · have h1 : above negQ.val 1 = 0 := by
      rw [above_val, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun y hy => not_lt.mpr (hU y (Finset.mem_union_left _ hy)).2.le
    have h2 : above nnF.val 1 = 0 := by
      rw [above_val, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun y hy => not_lt.mpr (hU y (Finset.mem_union_right _ hy)).2.le
    rw [habove, h1, h2, ite_eq_right (lt_irrefl 1), ite_eq_right (by norm_num)]
  · intro s hsq' hs0
    have hsm := hqR.mem s hsq'
    have hcnt : above negQ.val s + above nnF.val s = above (Cay (k + 1)).roots s := by
      rw [hnegQval, hnnFval, above_nonneg_of_neg _ hs0, ← hcount]
      have hsplit := above_split (sep α (Cay (k + 1))).roots s
      rw [above_nonneg_of_neg _ hs0] at hsplit
      rw [← hsplit]
      exact interlace_step_above_at_g_root hf hq hsq'
    rw [habove, hcnt, ite_eq_left hsm.2, ite_eq_right (by linarith [hsm.1]), add_zero]
  · intro r hrf' hr0
    have hrm := hf.mem r hrf'
    have hcnt : above negQ.val r + above nnF.val r = above (Cay (k + 1)).roots r := by
      rw [hnegQval, hnnFval, above_neg_of_nonneg _ hr0, above_nonneg_of_nonneg _ hr0, zero_add]
    rw [habove, hcnt, ite_eq_left hrm.2, ite_eq_right (by linarith [hrm.1]), add_zero]

/-- The smallest case `m = 2` (`n = 4`, `k = 1`): `f = C_2 = 2z` has the single root `0`, so the
test points are `-1`, one negative root of `q`, `0`, and `1`. -/
theorem Cay_two_roots : (Cay 2).roots = {0} := by
  rw [Cay_two, show (2 * X : ℝ[X]) = C 2 * X by simp [map_ofNat], roots_C_mul _ two_ne_zero, roots_X]

end EulerianRegion
