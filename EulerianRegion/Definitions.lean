module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic

/-!
# Definitions (frozen interface)

* `EulerianRegion.A n` is the Eulerian polynomial `A_n(x) = ∑_{π ∈ S_n} x^{des π}`, specified here by
  the recurrence from the task contract:
  `A 0 = 1`, `A (n + 1) = (1 + n x) A n + x (1 - x) (A n)'`.
  At `n = 0` the recurrence gives `A 1 = 1`, so this is the contract's recurrence (stated for
  `n ≥ 1`) extended to a total definition; it is not an extra hypothesis.  The permutation-sum
  description is *not* formalized here; the recurrence is the defining specification.
* `EulerianRegion.combination n b c = A n + b A (n - 1) + c A (n - 2)`, the polynomial
  `P_n(x; b, c)`.  It is only used for `n ≥ 3`, where the natural-number subtractions are exact.

The variable of `ℝ[X]` is read as `x`.  Splitting is mathlib's `Polynomial.Splits` over `ℝ`
(factorization into real linear factors, multiplicities retained).
-/

@[expose] public section

open Polynomial

noncomputable section

namespace EulerianRegion

/-- The Eulerian polynomials, defined by `A 0 = 1` and
`A (n + 1) = (1 + n X) * A n + X * (1 - X) * (A n)'`. -/
def A : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (1 + C (n : ℝ) * X) * A n + X * (1 - X) * derivative (A n)

/-- `P_n(x; b, c) = A_n(x) + b A_{n-1}(x) + c A_{n-2}(x)` (used for `n ≥ 3`). -/
def combination (n : ℕ) (b c : ℝ) : ℝ[X] :=
  A n + C b * A (n - 1) + C c * A (n - 2)

@[simp] theorem A_zero : A 0 = 1 := rfl

theorem A_succ (n : ℕ) :
    A (n + 1) = (1 + C (n : ℝ) * X) * A n + X * (1 - X) * derivative (A n) := rfl

end EulerianRegion
