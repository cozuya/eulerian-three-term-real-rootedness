module

public import EulerianRegion.Definitions

/-!
# The primary claim (frozen statement)

`PrimaryClaim` records the exact target as a proposition.  It is *not* assumed anywhere.  It is
proved as `EulerianRegion.primaryClaim_holds`, via the exported theorem
`EulerianRegion.eulerian_three_term_realRooted_iff` (`EulerianRegion/MainTheorem.lean`).

For every fixed real `b, c` with `0 ≤ b`, `0 ≤ c`:
`(∀ n : ℕ, 3 ≤ n → (combination n b c).Splits) ↔ c ≤ b ^ 2 / 4 + b + 3`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace EulerianRegion

/-- The exact statement to be proved: for fixed real `b, c ≥ 0`, every `P_n(·; b, c)` with `n ≥ 3`
splits over `ℝ` if and only if `c ≤ b² / 4 + b + 3`. -/
def PrimaryClaim : Prop :=
  ∀ b c : ℝ, 0 ≤ b → 0 ≤ c →
    ((∀ n : ℕ, 3 ≤ n → (combination n b c).Splits) ↔ c ≤ b ^ 2 / 4 + b + 3)

end EulerianRegion
