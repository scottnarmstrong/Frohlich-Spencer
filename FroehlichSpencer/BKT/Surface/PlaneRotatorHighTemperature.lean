/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import FroehlichSpencer.BKT.Surface.PlaneRotatorCorrelation
import FroehlichSpencer.BKT.Provider.PlaneRotatorHighTemperature

/-! # FS81 (1.30): exponential decay of the plane rotator at high temperature -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
FS81 (1.30) (J p. 533; a "standard high temperature expansion", cited, not an FS81
theorem).

`⟨S_j · S_ℓ⟩(β) → 0` as `|j - ℓ| → ∞` exponentially fast, provided `β` is small enough:
there is `β₁ > 0` such that for `0 ≤ β < β₁` there are `C` and `m > 0` with
`⟨S_j · S_ℓ⟩(β) ≤ C e^{-m |j - ℓ|}` for all sites, `|·|` the Euclidean norm.
-/
theorem planeRotator_highTemperature_expDecay :
    ∃ β₁ : ℝ, 0 < β₁ ∧ ∀ (β : ℝ) (hβ : 0 ≤ β), β < β₁ →
      ∃ C m : ℝ, 0 < m ∧ ∀ j ℓ : ℤ × ℤ,
        planeRotatorCorrelation β hβ 1 j ℓ ≤
          C * Real.exp (-m * Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2)) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.planeRotator_highTemperature_expDecay
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
