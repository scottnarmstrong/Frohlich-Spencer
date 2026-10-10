/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import FroehlichSpencer.BKT.Surface.ClockDisorderLimit
import FroehlichSpencer.BKT.Provider.ClockDisorderLowerBound

/-! # FS81 (7.5): the disorder lower bound of the `ℤ_n` clock model on the grid `ξ = k/n` -/

open Filter

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/-- FS81 §7.1, Remark 3, (7.5) (J p. 585), for the `ℤ_n` disorder operators
`ξ = k/n`, `k = 1, …, n - 1`: there is a threshold `n₁(β)` with `n₁(β) → ∞` as
`β → ∞` such that for each `β ≥ 0` and every clock order `n ≥ n₁(β)`, a thermodynamic limit of the
disorder expectations exists for every such `ξ`, and for some finite `β''' = β'''(β, n) ≥ 0` and a
constant `C > 0`, both shared over `k`, every thermodynamic limit satisfies
`⟨D^ξ_{0x}⟩^{(n)}(β) ≥ C (1 + |x|)^{-ξ²β'''/(2π)}` for `x = (r, 0)`, `r ≥ 1`. The constant may
depend on `β` and `n`, not on `k`, `r` or the limit. -/
theorem clock_disorder_lowerBound :
    ∃ n₁ : ℝ → ℕ, Tendsto n₁ atTop atTop ∧
      ∀ β : ℝ, 0 ≤ β → ∀ (n : ℕ) (hn : 0 < n), n₁ β ≤ n →
        (∀ k : ℕ, 1 ≤ k → k < n → ∃ D : ℕ → ℝ, IsClockDisorderLimit n hn β ((k : ℝ) / n) D) ∧
        ∃ β''' : ℝ, 0 ≤ β''' ∧ ∃ C : ℝ, 0 < C ∧
          ∀ k : ℕ, 1 ≤ k → k < n → ∀ D : ℕ → ℝ, IsClockDisorderLimit n hn β ((k : ℝ) / n) D →
            ∀ r : ℕ, 0 < r →
              C * (1 + (r : ℝ)) ^ (-(((k : ℝ) / n) ^ 2 * β''' / (2 * Real.pi))) ≤ D r :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.clock_disorder_lowerBound
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
