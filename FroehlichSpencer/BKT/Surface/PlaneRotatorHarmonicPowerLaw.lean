/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import FroehlichSpencer.BKT.Surface.PlaneRotatorCorrelation
import FroehlichSpencer.BKT.Provider.PlaneRotatorHarmonicPowerLaw

/-! # FS81 (6.1): power-law lower bounds for every integer harmonic of the plane rotator -/

open Filter

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
FS81 (6.1) (J p. 575).

There is a finite `β₀` such that for all `β > β₀`,
`⟨e^{iξ(θ_0 - θ_x)}⟩(β) ≥ const exp [-(ξ² / (2π β')) ln (1 + |x|)]` for every integer `ξ ≠ 0`,
for some `β' = β'(β) > 0` tending to `∞` as `β → ∞`.

The two-point function is the free
thermodynamic limit `planeRotatorCorrelation β hβ ξ 0 x = ⟨cos (ξ (θ_0 - θ_x))⟩(β)` (equal to
`⟨e^{iξ(θ_0 - θ_x)}⟩(β)` by the `θ ↦ -θ` symmetry, (1.29)); `|·|` is the Euclidean norm; one
`β'(β)` serves every harmonic; the positive constant may depend on `β` and `ξ`, not on `x`.
-/
theorem planeRotator_harmonic_powerLaw_lower_bound :
    ∃ β₀ : ℝ, ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧
      ∀ (β : ℝ) (hβ : 0 ≤ β), β₀ < β → 0 < β' β ∧
        ∀ ξ : ℤ, ξ ≠ 0 → ∃ A : ℝ, 0 < A ∧ ∀ x : ℤ × ℤ,
          A * Real.exp (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β)) *
              Real.log (1 + Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2))) ≤
            planeRotatorCorrelation β hβ ξ 0 x :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.planeRotator_harmonic_powerLaw_lower_bound
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
