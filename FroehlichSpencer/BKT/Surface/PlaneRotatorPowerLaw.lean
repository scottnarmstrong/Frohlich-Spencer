/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import FroehlichSpencer.BKT.Surface.PlaneRotatorCorrelation
import FroehlichSpencer.BKT.Provider.PlaneRotatorPowerLaw

/-! # FS81 Theorem C for the plane rotator: power-law lower bound -/

open Filter

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
FS81 Theorem C (J p. 534), plane rotator part.

In the two-dimensional plane
rotator model, for sufficiently large `β`,
`⟨S_j · S_ℓ⟩(β) ≥ const (1 + |j - ℓ|) ^ (-1 / (2π β'))` for some `β' = β'(β) > 1/(4π)`, and
`β'(β) → ∞` as `β → ∞`.

Here `⟨S_j · S_ℓ⟩(β) = ⟨cos (θ_j - θ_ℓ)⟩(β)` (1.29) is the free
thermodynamic limit `planeRotatorCorrelation β hβ 1 j ℓ`, `|·|` is the Euclidean norm, and the
constant is positive and independent of the sites.
-/
theorem planeRotator_powerLaw_lower_bound :
    ∃ β₀ : ℝ, ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧
      ∀ (β : ℝ) (hβ : 0 ≤ β), β₀ < β → 1 / (4 * Real.pi) < β' β ∧
        ∃ A : ℝ, 0 < A ∧ ∀ j ℓ : ℤ × ℤ,
          A * (1 + Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2)) ^
              (-(1 / (2 * Real.pi * β' β))) ≤
            planeRotatorCorrelation β hβ 1 j ℓ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.planeRotator_powerLaw_lower_bound
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
