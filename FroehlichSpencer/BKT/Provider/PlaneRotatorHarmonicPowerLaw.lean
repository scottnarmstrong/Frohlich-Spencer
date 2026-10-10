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
# Provider for `FroehlichSpencer.BKT.planeRotator_harmonic_powerLaw_lower_bound`

This module contains `FroehlichSpencer.BKT.Provider.planeRotator_harmonic_powerLaw_lower_bound`, the
proof of the statement `FroehlichSpencer.BKT.planeRotator_harmonic_powerLaw_lower_bound` (file
`FroehlichSpencer/BKT/Surface/PlaneRotatorHarmonicPowerLaw.lean`).

-/

@[expose] public section

open Filter
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Rotator.Transition
open FroehlichSpencer.BKT.Bridge.PlaneRotatorCorrelation

noncomputable section

namespace FroehlichSpencer.BKT.Provider

/-- The internal all-harmonic bound, transported to the package's exact (6.1) type. -/
theorem planeRotator_harmonic_powerLaw_lower_bound :
    ∃ β₀ : ℝ, ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧
      ∀ (β : ℝ) (hβ : 0 ≤ β), β₀ < β → 0 < β' β ∧
        ∀ ξ : ℤ, ξ ≠ 0 → ∃ A : ℝ, 0 < A ∧ ∀ x : ℤ × ℤ,
          A * Real.exp (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β)) *
              Real.log (1 + Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2))) ≤
            planeRotatorCorrelation β hβ ξ 0 x := by
  obtain ⟨β₀, β', hβ', hinternal⟩ := FroehlichSpencer.BKT.PlaneRotator.rotator_theoremC
  refine ⟨β₀, β', hβ', fun β hβ hβ₀ => ?_⟩
  obtain ⟨hthreshold, hpoint⟩ := hinternal β hβ hβ₀.le
  have hβ'pos : 0 < β' β := lt_trans (by positivity) hthreshold
  refine ⟨hβ'pos, fun ξ hξ => ?_⟩
  let q : ℝ := (ξ : ℝ) ^ 2 / (2 * Real.pi * β' β)
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  let A : ℝ := Real.exp (-q) * (2 : ℝ) ^ (-q)
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨A, hA, fun x => ?_⟩
  have hfree : Real.exp (-q) * ((l1Norm ((0 : ℤ × ℤ) - x) : ℝ) + 1) ^ (-q) ≤
      freeTwoPointLimit β hβ ξ 0 x := by
    simpa [q] using hpoint ξ 0 x
  have hprofile := euclideanProfile_le_l1Profile q hq 0 x
  have hcor := planeRotatorCorrelation_eq_freeTwoPointLimit β hβ ξ 0 x
  have hdistance :
      Real.sqrt (((((0 : ℤ × ℤ).1 - x.1 : ℤ) : ℝ) ^ 2 +
          (((0 : ℤ × ℤ).2 - x.2 : ℤ) : ℝ) ^ 2)) =
        Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) := by
    congr 1; simp
  rw [hcor]
  have hbound := hprofile.trans hfree
  rw [hdistance] at hbound
  have hlog : Real.exp (-q * Real.log (1 +
      Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2))) =
      (1 + Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2)) ^ (-q) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  rw [← hlog] at hbound
  simpa [A, q] using hbound

end FroehlichSpencer.BKT.Provider

end
