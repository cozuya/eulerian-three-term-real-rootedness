module

public import EulerianRegion.Residue

/-!
# The negative half-interval: A Lemma 4.1 and the central identity (5.4)

Source: Candidate A §§4–5, audit §§3.3–3.4.

* `pair_poly_pos`: `N(u, a) = u²(1 + 2u - u²) + a(1 - 2u - u²) > 0` for `0 < u < 1`, `0 ≤ a < 1`, via
  the decomposition (4.2) `N = a(1-u)³(1+u) + (1-a)u²(1+2u-u²)`.
* `pair_term_pos`: a symmetric pair `±r` (or a root at `0`, counted from both sides) contributes
  `2 N(-z, r²)/(z² - r²)² > 0` to `E(z) = Σ_r [(1 - z²)/(z - r)² - 2/(z - r)]`.
* `lemma_4_1` (**A Lemma 4.1**, only for `-1 < z < 0`): `(1 - z²) V(z) - 2 L(z) > 0`, with
  `L = Σ 1/(z - r)`, `V = Σ 1/(z - r)²`, for `f` with simple roots in `(-1, 1)`, symmetric about `0`,
  at least one root, and `f(z) ≠ 0`.  `lemma_4_1_bracket` is the polynomial-bracket form
  `(1 - z²)(f'² - f f'') - 2 f f' = f² E > 0`.  The lemma is not claimed for `z ≥ 0`.
* `central_identity` (**A (5.4)**), a polynomial identity for an arbitrary `f`, proved by `ring`:
  `P̂ f = q² + (z+1)²(c - α² - 2) f² - (1 - z²)[(1 - z²)(f'² - f f'') - 2 f f']` with `g = T f`,
  `h = T g`, `q = g + α (z+1) f`, `P̂ = h + (2α - 2)(z+1) g + c (z+1)² f`.
* `sign_at_neg_separator_root` (**A (5.5)**): at a root `s ∈ (-1, 0)` of `q` with `f(s) ≠ 0` and
  `c ≤ α² + 2` (boundary included), `P̂(s) f(s) < 0`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace EulerianRegion

/-! ### A Lemma 4.1: the one-sided inequality on `(-1, 0)` -/

/-- The pairing polynomial `N(u, a) = u²(1 + 2u - u²) + a(1 - 2u - u²)` is positive for
`0 < u < 1`, `0 ≤ a < 1`, via `N = a(1-u)³(1+u) + (1-a)u²(1+2u-u²)` (A (4.2)). -/
theorem pair_poly_pos {u a : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    0 < u ^ 2 * (1 + 2 * u - u ^ 2) + a * (1 - 2 * u - u ^ 2) := by
  have hdecomp : u ^ 2 * (1 + 2 * u - u ^ 2) + a * (1 - 2 * u - u ^ 2) =
      a * (1 - u) ^ 3 * (1 + u) + (1 - a) * u ^ 2 * (1 + 2 * u - u ^ 2) := by ring
  rw [hdecomp]
  have h1 : 0 ≤ a * (1 - u) ^ 3 * (1 + u) := by
    have : 0 < 1 - u := by linarith
    positivity
  have h2 : 0 < (1 - a) * u ^ 2 * (1 + 2 * u - u ^ 2) := by
    have : 0 < 1 + 2 * u - u ^ 2 := by nlinarith
    have : 0 < 1 - a := by linarith
    positivity
  linarith

/-- The contribution of a symmetric pair `±r` (or of a root at `0`, counted twice) to
`E(z) = Σ_r [(1 - z²)/(z - r)² - 2/(z - r)]`, for `-1 < z < 0`: it is `2 N(-z, r²)/(z² - r²)² > 0`. -/
theorem pair_term_pos {z r : ℝ} (hz0 : z < 0) (hz1 : -1 < z) (hr : r ^ 2 < 1) (hzr : z ≠ r)
    (hzr' : z ≠ -r) :
    0 < ((1 - z ^ 2) / (z - r) ^ 2 - 2 / (z - r)) + ((1 - z ^ 2) / (z - -r) ^ 2 - 2 / (z - -r)) := by
  have hne1 : z - r ≠ 0 := sub_ne_zero.mpr hzr
  have hne2 : z - -r ≠ 0 := sub_ne_zero.mpr hzr'
  have hne : z ^ 2 - r ^ 2 ≠ 0 := by
    rw [show z ^ 2 - r ^ 2 = (z - r) * (z - -r) by ring]; exact mul_ne_zero hne1 hne2
  have hkey : ((1 - z ^ 2) / (z - r) ^ 2 - 2 / (z - r)) + ((1 - z ^ 2) / (z - -r) ^ 2 - 2 / (z - -r)) =
      2 * ((-z) ^ 2 * (1 + 2 * (-z) - (-z) ^ 2) + r ^ 2 * (1 - 2 * (-z) - (-z) ^ 2)) /
        (z ^ 2 - r ^ 2) ^ 2 := by
    field_simp
    ring
  rw [hkey]
  have := pair_poly_pos (u := -z) (a := r ^ 2) (by linarith) (by linarith) (sq_nonneg r) hr
  positivity

/-- **A Lemma 4.1** (log-derivative form).  If `f` has simple roots, all in `(-1, 1)`, symmetric
about `0`, and at least one root, then for `-1 < z < 0` with `f(z) ≠ 0`,
`(1 - z²) V(z) - 2 L(z) > 0` where `L = Σ 1/(z - r)`, `V = Σ 1/(z - r)²`. -/
theorem lemma_4_1 {f : ℝ[X]} (hf : RootedIn f) (hsym : ∀ r ∈ f.roots, -r ∈ f.roots)
    (hne : f.roots ≠ 0) {z : ℝ} (hz0 : z < 0) (hz1 : -1 < z) (hfz : f.eval z ≠ 0) :
    0 < (1 - z ^ 2) * (f.roots.map (fun r => 1 / (z - r) ^ 2)).sum -
      2 * (f.roots.map (fun r => 1 / (z - r))).sum := by
  classical
  set S := f.roots.toFinset with hS
  have hval : S.val = f.roots := hf.toFinset_val
  have hsum1 : (f.roots.map (fun r => 1 / (z - r) ^ 2)).sum = ∑ r ∈ S, 1 / (z - r) ^ 2 := by
    rw [Finset.sum_eq_multiset_sum, hval]
  have hsum2 : (f.roots.map (fun r => 1 / (z - r))).sum = ∑ r ∈ S, 1 / (z - r) := by
    rw [Finset.sum_eq_multiset_sum, hval]
  rw [hsum1, hsum2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  set e : ℝ → ℝ := fun r => (1 - z ^ 2) / (z - r) ^ 2 - 2 / (z - r) with he
  have hrw : ∀ r ∈ S, (1 - z ^ 2) * (1 / (z - r) ^ 2) - 2 * (1 / (z - r)) = e r := by
    intro r _; simp only [he]; ring
  rw [Finset.sum_congr rfl hrw]
  have hSsym : ∀ r ∈ S, -r ∈ S := fun r hr =>
    Multiset.mem_toFinset.mpr (hsym r (Multiset.mem_toFinset.mp hr))
  have h2 : 2 * ∑ r ∈ S, e r = ∑ r ∈ S, (e r + e (-r)) := by
    rw [Finset.sum_add_distrib, sum_neg_eq hSsym e]; ring
  have hSne : S.Nonempty := by
    obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hne
    exact ⟨r, Multiset.mem_toFinset.mpr hr⟩
  have hpos : 0 < ∑ r ∈ S, (e r + e (-r)) := by
    apply Finset.sum_pos _ hSne
    intro r hr
    have hrm := hf.mem r (Multiset.mem_toFinset.mp hr)
    have hr2 : r ^ 2 < 1 := by nlinarith [hrm.1, hrm.2]
    have hroot : ∀ t ∈ S, z ≠ t := fun t ht h => hfz (h ▸ ((mem_roots hf.ne_zero).mp
      (Multiset.mem_toFinset.mp ht)).eq_zero)
    exact pair_term_pos hz0 hz1 hr2 (hroot r hr) (hroot (-r) (hSsym r hr))
  linarith

/-- Lemma 4.1 in polynomial-bracket form:
`(1 - z²)(f'(z)² - f(z) f''(z)) - 2 f(z) f'(z) = f(z)² E(z) > 0`. -/
theorem lemma_4_1_bracket {f : ℝ[X]} (hf : RootedIn f) (hsym : ∀ r ∈ f.roots, -r ∈ f.roots)
    (hne : f.roots ≠ 0) {z : ℝ} (hz0 : z < 0) (hz1 : -1 < z) (hfz : f.eval z ≠ 0) :
    0 < (1 - z ^ 2) * (((derivative f).eval z) ^ 2 - f.eval z * (derivative (derivative f)).eval z) -
      2 * f.eval z * (derivative f).eval z := by
  have hE := lemma_4_1 hf hsym hne hz0 hz1 hfz
  have hV := eval_derivative_sq_sub_of_splits hf.splits hfz
  have hL : (derivative f).eval z = f.eval z * (f.roots.map (fun r => 1 / (z - r))).sum := by
    have := hf.splits.eval_derivative_div_eval_of_ne_zero hfz
    field_simp at this ⊢
    linarith
  rw [hV, hL]
  have hf2 : 0 < (f.eval z) ^ 2 := by positivity
  have : (1 - z ^ 2) * ((f.eval z) ^ 2 * (f.roots.map (fun r => 1 / (z - r) ^ 2)).sum) -
      2 * f.eval z * (f.eval z * (f.roots.map (fun r => 1 / (z - r))).sum) =
      (f.eval z) ^ 2 * ((1 - z ^ 2) * (f.roots.map (fun r => 1 / (z - r) ^ 2)).sum -
        2 * (f.roots.map (fun r => 1 / (z - r))).sum) := by ring
  rw [this]
  exact mul_pos hf2 hE

/-! ### The central identity (A (5.4)) -/

/-- **A (5.4)**, for an arbitrary polynomial `f`: with `g = T f`, `h = T g`,
`q = g + α (z+1) f` and `P̂ = h + (2α - 2)(z+1) g + c (z+1)² f`,
`P̂ f = q² + (z+1)²(c - α² - 2) f² - (1 - z²)[(1 - z²)(f'² - f f'') - 2 f f']`. -/
theorem central_identity (f : ℝ[X]) (α c : ℝ) :
    (T (T f) + C (2 * α - 2) * (X + 1) * T f + C c * (X + 1) ^ 2 * f) * f =
      (T f + C α * (X + 1) * f) ^ 2 + (X + 1) ^ 2 * (C c - C α ^ 2 - 2) * f ^ 2 -
        (1 - X ^ 2) * ((1 - X ^ 2) * (derivative f ^ 2 - f * derivative (derivative f)) -
          2 * f * derivative f) := by
  simp only [T_eq, derivative_mul, derivative_add, derivative_X_pow,
    derivative_X, derivative_one, derivative_ofNat, map_sub, map_mul, map_ofNat]
  simp only [Nat.cast_ofNat, map_ofNat]
  ring

/-- **A (5.5).**  At a root `s ∈ (-1, 0)` of `q = T f + α (z+1) f` where `f(s) ≠ 0`, for every
`c ≤ α² + 2` (including equality): `P̂(s) f(s) < 0`. -/
theorem sign_at_neg_separator_root {f : ℝ[X]} (hf : RootedIn f)
    (hsym : ∀ r ∈ f.roots, -r ∈ f.roots) (hne : f.roots ≠ 0) {α c : ℝ} (hc : c ≤ α ^ 2 + 2)
    {s : ℝ} (hs0 : s < 0) (hs1 : -1 < s) (hq : (T f + C α * (X + 1) * f).eval s = 0)
    (hfs : f.eval s ≠ 0) :
    (T (T f) + C (2 * α - 2) * (X + 1) * T f + C c * (X + 1) ^ 2 * f).eval s * f.eval s < 0 := by
  have hid := congrArg (eval s) (central_identity f α c)
  rw [eval_mul] at hid
  rw [hid]
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_one, eval_ofNat] at hq ⊢
  rw [hq]
  have hbr := lemma_4_1_bracket hf hsym hne hs0 hs1 hfs
  have h1 : 0 < 1 - s ^ 2 := by nlinarith
  have h2 : (s + 1) ^ 2 * (c - α ^ 2 - 2) * (f.eval s) ^ 2 ≤ 0 := by
    have : c - α ^ 2 - 2 ≤ 0 := by linarith
    have : 0 ≤ (s + 1) ^ 2 * (f.eval s) ^ 2 := by positivity
    nlinarith
  nlinarith [mul_pos h1 hbr]

end EulerianRegion
