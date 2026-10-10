/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.PlaneRotatorTransition
public import FroehlichSpencer.BKT.Surface.PlaneRotatorCorrelation
public import FroehlichSpencer.BKT.Surface.PlaneRotatorPowerLaw
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Provider for `FroehlichSpencer.BKT.planeRotator_kosterlitzThouless_transition`

This module contains `FroehlichSpencer.BKT.Provider.planeRotator_kosterlitzThouless_transition`, the
proof of the statement `FroehlichSpencer.BKT.planeRotator_kosterlitzThouless_transition` (file
`FroehlichSpencer/BKT/Surface/PlaneRotatorTransition.lean`).

-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

theorem planeRotator_kosterlitzThouless_transition :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ (β : ℝ) (hβ : 0 ≤ β), β < βc →
        ∃ C m : ℝ, 0 < m ∧ ∀ j ℓ : ℤ × ℤ,
          planeRotatorCorrelation β hβ 1 j ℓ ≤
            C * Real.exp (-m * Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2))) ∧
      (∀ (β : ℝ) (hβ : 0 ≤ β), βc < β →
        (¬ ∃ C m : ℝ, 0 < m ∧ ∀ j ℓ : ℤ × ℤ,
          planeRotatorCorrelation β hβ 1 j ℓ ≤
            C * Real.exp (-m * Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2))) ∧
        ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ j ℓ : ℤ × ℤ,
          R ≤ Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2) →
            planeRotatorCorrelation β hβ 1 j ℓ ≤ ε) :=
  Bridge.PlaneRotatorTransition.kosterlitzThouless_of_powerLaw planeRotator_powerLaw_lower_bound

end FroehlichSpencer.BKT.Provider

end
