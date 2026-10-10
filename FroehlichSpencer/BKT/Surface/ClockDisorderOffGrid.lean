/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import FroehlichSpencer.BKT.Surface.ClockDisorderLimit
import FroehlichSpencer.BKT.Provider.ClockDisorderOffGrid

/-! # FS81 (7.5) fails off the grid `ξ = k/n`  -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/-- FS81's (7.5) read for every `ξ ∈ (0, 1)` is false . There is no threshold `n₁` such that for every `β > 0` and every clock order `n ≥ n₁(β)`
one `β'''` serves every `ξ ∈ (0, 1)`, with a positive constant for each `ξ`, in the bound
`⟨D^ξ_{0x}⟩^{(n)}(β) ≥ C (1 + |x|)^{-ξ²β'''/(2π)}` at every thermodynamic limit and every
`x = (r, 0)`, `r ≥ 1`. It fails at `ξ = 1/(2n)`: off the grid `ξ ∈ ℤ/n` the disorder expectation
decays exponentially in `r`. -/
theorem not_clock_disorder_lowerBound_offGrid :
    ¬ ∃ n₁ : ℝ → ℕ, ∀ β : ℝ, 0 < β → ∀ (n : ℕ) (hn : 0 < n), n₁ β ≤ n →
      ∃ β''' : ℝ, ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∃ C : ℝ, 0 < C ∧
        ∀ D : ℕ → ℝ, IsClockDisorderLimit n hn β ξ D → ∀ r : ℕ, 0 < r →
          C * (1 + (r : ℝ)) ^ (-(ξ ^ 2 * β''' / (2 * Real.pi))) ≤ D r :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.not_clock_disorder_lowerBound_offGrid
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
