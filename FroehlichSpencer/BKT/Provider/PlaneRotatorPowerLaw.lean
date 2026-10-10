/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.PlaneRotatorCorrelation
public import FroehlichSpencer.BKT.PlaneRotator.TheoremC
public import FroehlichSpencer.BKT.Surface.PlaneRotatorCorrelation
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.planeRotator_powerLaw_lower_bound`

This module contains `FroehlichSpencer.BKT.Provider.planeRotator_powerLaw_lower_bound`, the proof of
the statement `FroehlichSpencer.BKT.planeRotator_powerLaw_lower_bound` (file
`FroehlichSpencer/BKT/Surface/PlaneRotatorPowerLaw.lean`).

-/

@[expose] public section

open Filter
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Rotator.Transition
open FroehlichSpencer.BKT.Bridge.PlaneRotatorCorrelation

noncomputable section

namespace FroehlichSpencer.BKT.Provider

/-- The internal Theorem C theorem, transported to the package's exact TC type. -/
theorem planeRotator_powerLaw_lower_bound :
    ∃ β₀ : ℝ, ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧
      ∀ (β : ℝ) (hβ : 0 ≤ β), β₀ < β → 1 / (4 * Real.pi) < β' β ∧
        ∃ A : ℝ, 0 < A ∧ ∀ j ℓ : ℤ × ℤ,
          A * (1 + Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2)) ^
              (-(1 / (2 * Real.pi * β' β))) ≤
            planeRotatorCorrelation β hβ 1 j ℓ := by
  obtain ⟨β₀, β', hβ', hinternal⟩ := FroehlichSpencer.BKT.PlaneRotator.rotator_theoremC
  refine ⟨β₀, β', hβ', fun β hβ hβ₀ => ?_⟩
  obtain ⟨hthreshold, hpoint⟩ := hinternal β hβ hβ₀.le
  refine ⟨hthreshold, ?_⟩
  let q : ℝ := 1 / (2 * Real.pi * β' β)
  have hβ'pos : 0 < β' β := lt_trans (by positivity) hthreshold
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  let A : ℝ := Real.exp (-q) * (2 : ℝ) ^ (-q)
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨A, hA, fun j ℓ => ?_⟩
  have hfree : Real.exp (-q) * ((l1Norm (j - ℓ) : ℝ) + 1) ^ (-q) ≤
      freeTwoPointLimit β hβ 1 j ℓ := by
    simpa [q] using hpoint 1 j ℓ
  have hprofile := euclideanProfile_le_l1Profile q hq j ℓ
  rw [planeRotatorCorrelation_eq_freeTwoPointLimit]
  simpa [A, q] using hprofile.trans hfree

end FroehlichSpencer.BKT.Provider

end
