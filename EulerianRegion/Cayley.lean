module

public import EulerianRegion.Sanity
public import EulerianRegion.RootCount
public import Mathlib.Tactic.Positivity

/-!
# The Cayley-transformed Eulerian polynomials

Source: Candidate A §2, audit §3.1.  With `x = (z - 1)/(z + 1)`,
`C_j(z) = (1 + z)^(j-1) A_j((z - 1)/(z + 1))` for `j ≥ 1`.

* `T f = ((X² - 1) f)'` and `Cay`: `Cay 1 = 1`, `Cay (j + 2) = T (Cay (j + 1))` (A (2.5)); `Cay 0 = 0`
  is an unused placeholder.  `Cay_two`, `Cay_three` are the source's `C_2 = 2z`, `C_3 = 6z² - 2`.
* Bridge to the frozen `A`, for **every** index (`Cay_succ_eq_homog`): `Cay (k+1) = homog k (A (k+1))`
  with `homog d p = Σ_{i ≤ d} [x^i]p · (X - 1)^i (X + 1)^(d - i)` (the contract's denominator-free form),
  proved from the coefficient recurrence via `T_homog`; pointwise form `eval_Cay_succ`:
  `C_{k+1}(z) = (z + 1)^k A_{k+1}((z - 1)/(z + 1))` for `z ≠ -1`.
* Shape: degree `j - 1` (`natDegree_Cay`), leading coefficient `j!` (`leadingCoeff_Cay`),
  endpoints `C_j(1) = 2^(j-1)`, `C_j(-1) = (-2)^(j-1)`, parity `C_j(-z) = (-1)^(j-1) C_j(z)`
  (`Cay_comp_neg_X`, `eval_neg_Cay`).
* Roots: `Cay_rootedIn` (simple roots, all in `(-1, 1)`), consecutive interlacing `Cay_interlace`,
  via the generic `interlace_step` (sign count at `-1`, the roots of `f`, and `1`).

Indices: lemmas are stated for `Cay (k + 1)` (`= C_{k+1}`, degree `k`), so no natural-number
subtraction occurs.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace EulerianRegion

/-! ### The operator `T f = ((X² - 1) f)'` -/

/-- `T f = ((X^2 - 1) * f)'`. -/
def T (f : ℝ[X]) : ℝ[X] := derivative ((X ^ 2 - 1) * f)

theorem T_eq (f : ℝ[X]) : T f = (X ^ 2 - 1) * derivative f + 2 * X * f := by
  unfold T; rw [derivative_mul]; simp; ring

theorem T_add (f g : ℝ[X]) : T (f + g) = T f + T g := by
  unfold T; rw [mul_add, derivative_add]

theorem T_C_mul (a : ℝ) (f : ℝ[X]) : T (C a * f) = C a * T f := by
  unfold T; rw [mul_left_comm, derivative_C_mul]

theorem T_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ[X]) : T (∑ i ∈ s, F i) = ∑ i ∈ s, T (F i) := by
  unfold T; rw [Finset.mul_sum, derivative_sum]

theorem eval_T (f : ℝ[X]) (z : ℝ) :
    (T f).eval z = (z ^ 2 - 1) * (derivative f).eval z + 2 * z * f.eval z := by
  rw [T_eq]; simp

theorem eval_one_T (f : ℝ[X]) : (T f).eval 1 = 2 * f.eval 1 := by
  rw [eval_T]; ring

theorem eval_neg_one_T (f : ℝ[X]) : (T f).eval (-1) = -2 * f.eval (-1) := by
  rw [eval_T]; ring

theorem coeff_T_succ (f : ℝ[X]) (n : ℕ) :
    (T f).coeff (n + 1) = ((n : ℝ) + 2) * f.coeff n - ((n : ℝ) + 2) * f.coeff (n + 2) := by
  rw [T_eq]
  have h1 : ((X ^ 2 - 1) * derivative f).coeff (n + 1) =
      (n : ℝ) * f.coeff n - (n + 2 : ℝ) * f.coeff (n + 2) := by
    rw [sub_mul, one_mul, coeff_sub, coeff_derivative]
    cases n with
    | zero => simp [coeff_X_pow_mul']; ring
    | succ n =>
      rw [coeff_X_pow_mul', ite_eq_left (show 2 ≤ n + 1 + 1 by omega), show n + 1 + 1 - 2 = n by omega, coeff_derivative]
      push_cast; ring
  have h2 : (2 * X * f).coeff (n + 1) = 2 * f.coeff n := by
    rw [mul_assoc, show (2 : ℝ[X]) = C 2 by simp [map_ofNat], coeff_C_mul, coeff_X_mul]
  rw [coeff_add, h1, h2]; ring

/-- `T` raises the degree by one and multiplies the leading coefficient by `natDegree + 2`. -/
theorem T_degree {f : ℝ[X]} {k : ℕ} (hk : f.natDegree = k) (hf : f ≠ 0) :
    (T f).natDegree = k + 1 ∧ (T f).leadingCoeff = ((k : ℝ) + 2) * f.leadingCoeff := by
  have hcoeff : (T f).coeff (k + 1) = ((k : ℝ) + 2) * f.leadingCoeff := by
    rw [coeff_T_succ, leadingCoeff, coeff_eq_zero_of_natDegree_lt (show f.natDegree < k + 2 by omega), hk]; ring
  have hne : (T f).coeff (k + 1) ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (by positivity) (leadingCoeff_ne_zero.mpr hf)
  have hle : (T f).natDegree ≤ k + 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [coeff_T_succ, coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]
    ring
  have hdeg : (T f).natDegree = k + 1 := le_antisymm hle (le_natDegree_of_ne_zero hne)
  exact ⟨hdeg, by rw [leadingCoeff, hdeg, hcoeff]⟩

/-! ### The Cayley-transformed Eulerian polynomials -/

/-- `Cay j` is `C_j(z) = (1 + z)^(j-1) A_j((z - 1)/(z + 1))` for `j ≥ 1`, defined by the transformed
recurrence `C_1 = 1`, `C_{j+1} = T C_j`; `Cay 0 = 0` is an unused placeholder.  The bridge
to `A` is `Cay_succ_eq_homog`. -/
def Cay : ℕ → ℝ[X]
  | 0 => 0
  | 1 => 1
  | j + 2 => T (Cay (j + 1))

@[simp] theorem Cay_one : Cay 1 = 1 := rfl

theorem Cay_succ_succ (j : ℕ) : Cay (j + 2) = T (Cay (j + 1)) := rfl

theorem Cay_two : Cay 2 = 2 * X := by
  rw [Cay_succ_succ, Cay_one, T_eq]; simp

theorem Cay_three : Cay 3 = 6 * X ^ 2 - 2 := by
  rw [Cay_succ_succ, Cay_two, T_eq]
  simp only [derivative_mul, derivative_X, derivative_ofNat, zero_mul, zero_add, mul_one]
  ring

theorem Cay_degree (k : ℕ) :
    (Cay (k + 1)).natDegree = k ∧ (Cay (k + 1)).leadingCoeff = ((k + 1).factorial : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hne : Cay (k + 1) ≠ 0 := fun h => by
      have := ih.2; rw [h, leadingCoeff_zero] at this
      exact absurd this.symm (by positivity)
    obtain ⟨h1, h2⟩ := T_degree ih.1 hne
    rw [Cay_succ_succ]
    refine ⟨h1, ?_⟩
    rw [h2, ih.2, Nat.factorial_succ (k + 1)]
    push_cast; ring

theorem natDegree_Cay (k : ℕ) : (Cay (k + 1)).natDegree = k := (Cay_degree k).1

theorem leadingCoeff_Cay (k : ℕ) :
    (Cay (k + 1)).leadingCoeff = ((k + 1).factorial : ℝ) := (Cay_degree k).2

theorem leadingCoeff_Cay_pos (k : ℕ) : 0 < (Cay (k + 1)).leadingCoeff := by
  rw [leadingCoeff_Cay]; exact_mod_cast Nat.factorial_pos _

theorem Cay_ne_zero (k : ℕ) : Cay (k + 1) ≠ 0 := fun h => by
  have := leadingCoeff_Cay_pos k; rw [h, leadingCoeff_zero] at this; exact lt_irrefl _ this

theorem eval_one_Cay (k : ℕ) : (Cay (k + 1)).eval 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Cay_succ_succ, eval_one_T, ih]; ring

theorem eval_neg_one_Cay (k : ℕ) : (Cay (k + 1)).eval (-1) = (-2) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Cay_succ_succ, eval_neg_one_T, ih]; ring

/-! ### Parity -/

theorem derivative_comp_neg_X (f : ℝ[X]) :
    (derivative f).comp (-X) = -derivative (f.comp (-X)) := by
  rw [derivative_comp]; simp

theorem T_comp_neg_X (f : ℝ[X]) : (T f).comp (-X) = -T (f.comp (-X)) := by
  rw [T_eq, T_eq, add_comp, mul_comp, mul_comp, derivative_comp_neg_X]
  simp only [sub_comp, pow_comp, X_comp, one_comp, mul_comp, ofNat_comp]
  ring

/-- `C_j(-z) = (-1)^(j-1) C_j(z)`. -/
theorem Cay_comp_neg_X (k : ℕ) : (Cay (k + 1)).comp (-X) = C ((-1) ^ k) * Cay (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Cay_succ_succ, T_comp_neg_X, ih, T_C_mul, pow_succ, C_mul, C_neg, C_1]
    ring

theorem eval_neg_Cay (k : ℕ) (z : ℝ) : (Cay (k + 1)).eval (-z) = (-1) ^ k * (Cay (k + 1)).eval z := by
  have := congrArg (eval z) (Cay_comp_neg_X k)
  simpa [eval_comp] using this

/-! ### Homogenized Cayley substitution and the bridge to `A` -/

/-- `homog d p = Σ_{i ≤ d} p_i (X - 1)^i (X + 1)^(d - i)`.  For `natDegree p ≤ d` and `z ≠ -1` this
evaluates to `(z + 1)^d p((z - 1)/(z + 1))` (`eval_homog`). -/
def homog (d : ℕ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun p := ∑ i ∈ Finset.range (d + 1), C (p.coeff i) * ((X - 1) ^ i * (X + 1) ^ (d - i))
  map_add' p q := by simp [Finset.sum_add_distrib, add_mul]
  map_smul' a p := by simp [Finset.mul_sum, smul_eq_C_mul, mul_assoc]

theorem homog_apply (d : ℕ) (p : ℝ[X]) :
    homog d p = ∑ i ∈ Finset.range (d + 1), C (p.coeff i) * ((X - 1) ^ i * (X + 1) ^ (d - i)) :=
  rfl

theorem homog_X_pow {d i : ℕ} (hi : i ≤ d) :
    homog d (X ^ i) = (X - 1) ^ i * (X + 1) ^ (d - i) := by
  rw [homog_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [coeff_X_pow, hj]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

theorem T_mul_pow (a b : ℕ) :
    T ((X - 1) ^ a * (X + 1) ^ b) =
      C ((a : ℝ) + 1) * ((X - 1) ^ a * (X + 1) ^ (b + 1)) +
        C ((b : ℝ) + 1) * ((X - 1) ^ (a + 1) * (X + 1) ^ b) := by
  unfold T
  rw [show (X ^ 2 - 1 : ℝ[X]) * ((X - 1) ^ a * (X + 1) ^ b) =
      (X - 1) ^ (a + 1) * (X + 1) ^ (b + 1) by ring]
  simp only [derivative_mul, derivative_pow, derivative_sub, derivative_add, derivative_X,
    derivative_one, sub_zero, add_zero, mul_one, add_tsub_cancel_right]
  simp only [map_add, map_natCast, map_one, Nat.cast_add, Nat.cast_one]
  ring

theorem X_mul_derivative_X_pow (i : ℕ) : X * derivative (X ^ i : ℝ[X]) = C (i : ℝ) * X ^ i := by
  cases i with
  | zero => simp
  | succ i => rw [derivative_X_pow]; simp; ring

/-- One step of the transformed recurrence on a monomial. -/
theorem T_homog_X_pow {k i : ℕ} (hi : i ≤ k) :
    T (homog k (X ^ i)) = homog (k + 1)
      ((1 + C ((k : ℝ) + 1) * X) * X ^ i + X * (1 - X) * derivative (X ^ i)) := by
  have hrw : (1 + C ((k : ℝ) + 1) * X) * X ^ i + X * (1 - X) * derivative (X ^ i : ℝ[X]) =
      ((i : ℝ) + 1) • X ^ i + ((k : ℝ) + 1 - i) • X ^ (i + 1) := by
    rw [show X * (1 - X) * derivative (X ^ i : ℝ[X]) = (1 - X) * (X * derivative (X ^ i)) by ring,
      X_mul_derivative_X_pow]
    simp only [smul_eq_C_mul, map_add, map_sub, map_one, map_natCast]
    ring
  rw [hrw, homog_X_pow hi, T_mul_pow, LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul,
    homog_X_pow (by omega),
    homog_X_pow (by omega), smul_eq_C_mul, smul_eq_C_mul, show k + 1 - i = k - i + 1 by omega,
    show k + 1 - (i + 1) = k - i by omega, Nat.cast_sub hi]
  rw [show (k : ℝ) - i + 1 = k + 1 - i by ring]

/-- The transformed recurrence: `T (homog k p) = homog (k + 1) (R p)` where `R` is the Eulerian
recurrence operator, for every `p` of degree at most `k`. -/
theorem T_homog {k : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ k) :
    T (homog k p) = homog (k + 1)
      ((1 + C ((k : ℝ) + 1) * X) * p + X * (1 - X) * derivative p) := by
  have hsum := p.as_sum_range' (k + 1) (by omega)
  simp only [← C_mul_X_pow_eq_monomial] at hsum
  conv_lhs => rw [hsum]
  conv_rhs => rw [hsum]
  simp only [map_sum, T_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi : i ≤ k := by have := Finset.mem_range.mp hi; omega
  have e1 : homog k (C (p.coeff i) * X ^ i) = C (p.coeff i) * homog k (X ^ i) := by
    rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul]
  have e2 : (1 + C ((k : ℝ) + 1) * X) * (C (p.coeff i) * X ^ i) +
      X * (1 - X) * derivative (C (p.coeff i) * X ^ i) =
      C (p.coeff i) * ((1 + C ((k : ℝ) + 1) * X) * X ^ i + X * (1 - X) * derivative (X ^ i)) := by
    rw [derivative_C_mul]; ring
  rw [e1, T_C_mul, T_homog_X_pow hi, e2]
  simp only [← smul_eq_C_mul, LinearMap.map_smul]

/-- **Cayley bridge** (denominator-free form): `C_{k+1} = Σ_i [x^i]A_{k+1} (z-1)^i (z+1)^(k-i)`. -/
theorem Cay_succ_eq_homog (k : ℕ) : Cay (k + 1) = homog k (A (k + 1)) := by
  induction k with
  | zero =>
    rw [Cay_one, A_one, homog_apply]; simp
  | succ k ih =>
    rw [Cay_succ_succ, ih, T_homog (natDegree_A_succ k).le, A_succ (k + 1)]
    push_cast
    rfl

theorem eval_homog {d : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d) {z : ℝ} (hz : z ≠ -1) :
    (homog d p).eval z = (z + 1) ^ d * p.eval ((z - 1) / (z + 1)) := by
  have hz1 : z + 1 ≠ 0 := fun h => hz (by linarith)
  rw [homog_apply, eval_finsetSum, eval_eq_sum_range' (n := d + 1) (by omega), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi : i ≤ d := by have := Finset.mem_range.mp hi; omega
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_add, eval_X, eval_one]
  rw [div_pow, show (z + 1) ^ d = (z + 1) ^ (d - i) * (z + 1) ^ i by
    rw [← pow_add, Nat.sub_add_cancel hi]]
  field_simp

/-- **Cayley bridge** (pointwise form of the contract): for `z ≠ -1`,
`C_{k+1}(z) = (1 + z)^k A_{k+1}((z - 1)/(z + 1))`. -/
theorem eval_Cay_succ (k : ℕ) {z : ℝ} (hz : z ≠ -1) :
    (Cay (k + 1)).eval z = (z + 1) ^ k * (A (k + 1)).eval ((z - 1) / (z + 1)) := by
  rw [Cay_succ_eq_homog, eval_homog (natDegree_A_succ k).le hz]

theorem homog_succ {d : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d) :
    homog (d + 1) p = (X + 1) * homog d p := by
  rw [homog_apply, homog_apply, Finset.sum_range_succ,
    coeff_eq_zero_of_natDegree_lt (show p.natDegree < d + 1 by omega), C_0, zero_mul, add_zero,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi : i ≤ d := by have := Finset.mem_range.mp hi; omega
  rw [show d + 1 - i = (d - i) + 1 by omega, pow_succ]
  ring

/-! ### Simple roots in `(-1, 1)` and the interlacing step -/

theorem above_insert_val {L : Finset ℝ} {a : ℝ} (ha : a ∉ L) (t : ℝ) :
    above (insert a L).val t = above L.val t + if t < a then 1 else 0 := by
  rw [Finset.insert_val_of_notMem ha, above_cons]

/-- `f` splits with simple roots, all in the open interval `(-1, 1)`, and has positive leading
coefficient. -/
structure RootedIn (f : ℝ[X]) : Prop where
  splits : f.Splits
  lc_pos : 0 < f.leadingCoeff
  nodup : f.roots.Nodup
  mem : ∀ r ∈ f.roots, -1 < r ∧ r < 1

namespace RootedIn

variable {f : ℝ[X]}

theorem ne_zero (hf : RootedIn f) : f ≠ 0 := fun h => by simpa [h] using hf.lc_pos

theorem card_roots (hf : RootedIn f) : f.roots.card = f.natDegree :=
  splits_iff_card_roots.mp hf.splits

theorem toFinset_val (hf : RootedIn f) : f.roots.toFinset.val = f.roots := by
  rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hf.nodup]

theorem not_isRoot_one (hf : RootedIn f) : ¬ f.IsRoot 1 := fun h =>
  lt_irrefl _ (hf.mem 1 ((mem_roots hf.ne_zero).mpr h)).2

theorem not_isRoot_neg_one (hf : RootedIn f) : ¬ f.IsRoot (-1) := fun h =>
  lt_irrefl _ (hf.mem (-1) ((mem_roots hf.ne_zero).mpr h)).1

theorem above_one (hf : RootedIn f) : above f.roots 1 = 0 := by
  unfold above
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  exact fun r hr => not_lt.mpr (hf.mem r hr).2.le

theorem above_neg_one (hf : RootedIn f) : above f.roots (-1) = f.natDegree := by
  unfold above
  rw [Multiset.filter_eq_self.mpr (fun r hr => (hf.mem r hr).1), hf.card_roots]

theorem eval_one_pos (hf : RootedIn f) : 0 < f.eval 1 := by
  simpa [hf.above_one] using sign_eval hf.splits hf.lc_pos hf.not_isRoot_one

theorem eval_neg_one_sign (hf : RootedIn f) : 0 < (-1 : ℝ) ^ f.natDegree * f.eval (-1) := by
  simpa [hf.above_neg_one] using sign_eval hf.splits hf.lc_pos hf.not_isRoot_neg_one

end RootedIn

/-- The test points `-1`, the roots of `f`, and `1`. -/
def testSet (f : ℝ[X]) : Finset ℝ := insert (-1) (insert 1 f.roots.toFinset)

theorem testSet_ge {f : ℝ[X]} (hf : RootedIn f) {t : ℝ} (ht : t ∈ testSet f) : -1 ≤ t ∧ t ≤ 1 := by
  simp only [testSet, Finset.mem_insert, Multiset.mem_toFinset] at ht
  rcases ht with rfl | rfl | ht
  · norm_num
  · norm_num
  · exact ⟨(hf.mem t ht).1.le, (hf.mem t ht).2.le⟩

theorem RootedIn.one_notMem_toFinset {f : ℝ[X]} (hf : RootedIn f) : (1 : ℝ) ∉ f.roots.toFinset :=
  fun h => hf.not_isRoot_one ((mem_roots hf.ne_zero).mp (Multiset.mem_toFinset.mp h))

theorem RootedIn.neg_one_notMem_insert {f : ℝ[X]} (hf : RootedIn f) :
    (-1 : ℝ) ∉ insert 1 f.roots.toFinset := by
  simp only [Finset.mem_insert, Multiset.mem_toFinset, not_or]
  exact ⟨by norm_num, fun h => hf.not_isRoot_neg_one ((mem_roots hf.ne_zero).mp h)⟩

/-- Counting test points above `t`. -/
theorem above_testSet {f : ℝ[X]} (hf : RootedIn f) (t : ℝ) :
    above (testSet f).val t =
      above f.roots t + (if t < 1 then 1 else 0) + (if t < -1 then 1 else 0) := by
  rw [testSet, above_insert_val hf.neg_one_notMem_insert, above_insert_val hf.one_notMem_toFinset,
    hf.toFinset_val]

/-- **Interlacing step.**  If `f` has simple roots in `(-1, 1)` and `g` has degree one more, positive
leading coefficient, `g(r) = (r² - 1) f'(r)` at the roots of `f`, `g(1) > 0` and
`g(-1) = -2 f(-1)`, then `g` has strictly alternating signs at `-1`, the roots of `f`, and `1`. -/
theorem interlace_step {f g : ℝ[X]} (hf : RootedIn f) (hdeg : g.natDegree = f.natDegree + 1)
    (hglc : 0 < g.leadingCoeff)
    (hroot : ∀ r ∈ f.roots, g.eval r = (r ^ 2 - 1) * (derivative f).eval r)
    (h1 : 0 < g.eval 1) (hm1 : g.eval (-1) = -2 * f.eval (-1)) :
    SignPattern g (testSet f) := by
  classical
  have h1nf := hf.one_notMem_toFinset
  have hm1nf := hf.neg_one_notMem_insert
  refine ⟨hglc, ?_, ?_⟩
  · rw [testSet, Finset.card_insert_of_notMem hm1nf, Finset.card_insert_of_notMem h1nf,
      Multiset.card_toFinset, Multiset.dedup_eq_self.mpr hf.nodup, hf.card_roots, hdeg]
  · intro t ht
    rw [above_testSet hf]
    simp only [testSet, Finset.mem_insert, Multiset.mem_toFinset] at ht
    rcases ht with rfl | rfl | ht
    · rw [hf.above_neg_one, hm1, ite_eq_left (by norm_num), ite_eq_right (by norm_num), pow_succ]
      have := hf.eval_neg_one_sign
      nlinarith
    · rw [hf.above_one, ite_eq_right (by norm_num), ite_eq_right (by norm_num)]
      simpa using h1
    · obtain ⟨hlo, hhi⟩ := hf.mem t ht
      rw [ite_eq_left hhi, ite_eq_right (by linarith), add_zero, hroot t ht, pow_succ]
      have := sign_derivative hf.splits hf.lc_pos hf.nodup ht
      have h2 : 0 < 1 - t ^ 2 := by nlinarith
      nlinarith

/-- Consequences of the interlacing step for `g`. -/
theorem interlace_step_rootedIn {f g : ℝ[X]} (hf : RootedIn f) (hg : SignPattern g (testSet f)) :
    RootedIn g := by
  refine ⟨hg.splits, hg.lc_pos, hg.nodup, fun ξ hξ => ?_⟩
  obtain ⟨⟨t₀, ht₀, h₀⟩, ⟨t₁, ht₁, h₁⟩⟩ := hg.root_bounds hξ
  exact ⟨lt_of_le_of_lt (testSet_ge hf ht₀).1 h₀, lt_of_lt_of_le h₁ (testSet_ge hf ht₁).2⟩

theorem interlace_step_above_at_f_root {f g : ℝ[X]} (hf : RootedIn f)
    (hg : SignPattern g (testSet f)) {r : ℝ} (hr : r ∈ f.roots) :
    above g.roots r = above f.roots r + 1 ∧ g.eval r ≠ 0 := by
  classical
  have hrt : r ∈ testSet f := by simp [testSet, hr]
  refine ⟨?_, hg.eval_ne_zero hrt⟩
  rw [hg.above_roots_eq hrt, above_testSet hf, ite_eq_left (hf.mem r hr).2,
    ite_eq_right (by linarith [(hf.mem r hr).1])]

theorem interlace_step_above_at_g_root {f g : ℝ[X]} (hf : RootedIn f)
    (hg : SignPattern g (testSet f)) {ξ : ℝ} (hξ : ξ ∈ g.roots) :
    above g.roots ξ = above f.roots ξ := by
  classical
  have h := hg.above_roots_at_root hξ
  have hgr := (interlace_step_rootedIn hf hg).mem ξ hξ
  rw [above_testSet hf, ite_eq_left hgr.2, ite_eq_right (by linarith [hgr.1])] at h
  omega

/-! ### Roots of the Cayley sequence -/

theorem T_signPattern {f : ℝ[X]} (hf : RootedIn f) : SignPattern (T f) (testSet f) := by
  obtain ⟨hdeg, hlc⟩ := T_degree rfl hf.ne_zero
  refine interlace_step hf hdeg (by rw [hlc]; exact mul_pos (by positivity) hf.lc_pos) ?_ ?_
    (eval_neg_one_T f)
  · intro r hr
    rw [eval_T, (mem_roots hf.ne_zero).mp hr]; ring
  · rw [eval_one_T]; exact mul_pos two_pos hf.eval_one_pos

/-- `C_{k+1}` has `k` simple roots, all in `(-1, 1)`, and positive leading coefficient. -/
theorem Cay_rootedIn (k : ℕ) : RootedIn (Cay (k + 1)) := by
  induction k with
  | zero => exact ⟨by simp, by simp, by simp, by simp⟩
  | succ k ih =>
    rw [Cay_succ_succ]
    exact interlace_step_rootedIn ih (T_signPattern ih)

/-- Consecutive interlacing: at every root `r` of `C_{k+1}`, `C_{k+2}(r) ≠ 0` and `C_{k+2}` has
exactly one more root above `r` than `C_{k+1}`. -/
theorem Cay_interlace (k : ℕ) {r : ℝ} (hr : r ∈ (Cay (k + 1)).roots) :
    above (Cay (k + 2)).roots r = above (Cay (k + 1)).roots r + 1 ∧ (Cay (k + 2)).eval r ≠ 0 := by
  rw [Cay_succ_succ]
  exact interlace_step_above_at_f_root (Cay_rootedIn k) (T_signPattern (Cay_rootedIn k)) hr

/-- Consecutive interlacing seen from the roots of `C_{k+2}`: at every root `ξ` of `C_{k+2}`,
`C_{k+1}` and `C_{k+2}` have the same number of roots above `ξ`. -/
theorem Cay_interlace_dual (k : ℕ) {ξ : ℝ} (hξ : ξ ∈ (Cay (k + 2)).roots) :
    above (Cay (k + 2)).roots ξ = above (Cay (k + 1)).roots ξ := by
  rw [Cay_succ_succ] at hξ ⊢
  exact interlace_step_above_at_g_root (Cay_rootedIn k) (T_signPattern (Cay_rootedIn k)) hξ

theorem Cay_root_neg (k : ℕ) {r : ℝ} (hr : r ∈ (Cay (k + 1)).roots) : -r ∈ (Cay (k + 1)).roots := by
  rw [mem_roots (Cay_ne_zero k)] at hr ⊢
  rw [IsRoot, eval_neg_Cay, hr.eq_zero, mul_zero]

end EulerianRegion
