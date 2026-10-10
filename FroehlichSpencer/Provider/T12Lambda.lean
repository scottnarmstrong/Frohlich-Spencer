/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Norm
public import FroehlichSpencer.Surface.BoundedDensityLaw
public import FroehlichSpencer.Surface.ConfigurationMeasure
public import FroehlichSpencer.Surface.FiniteGreen
public import FroehlichSpencer.Surface.GaussianLaw
public import FroehlichSpencer.Surface.LatticeLength
import FroehlichSpencer.T12.Assembly.ProbabilityBound
import FroehlichSpencer.T12.Assembly.T21Interface

/-!
# Provider for `FroehlichSpencer.finiteVolumeGreen_probability_bound`

This module contains `FroehlichSpencer.Provider.finiteVolumeGreen_probability_bound`, the proof of
the statement `FroehlichSpencer.finiteVolumeGreen_probability_bound` (file
`FroehlichSpencer/Surface/T12Lambda.lean`).

-/

@[expose] public section

open MeasureTheory

namespace FroehlichSpencer.Provider


theorem finiteVolumeGreen_probability_bound (ν : ℕ) (hν : 0 < ν) :
    ∃ (largeDisorder : ℝ → ℝ → ℝ)
      (highEnergy : ℝ → ℝ → ℝ → ℝ)
      (Kp : ℝ → ℝ)
      (Kgauss : ℝ → ℝ → ℝ → ℝ),
      (∀ p m, 0 < m → 0 < p → 0 < largeDisorder p m) ∧
      (∀ γ p m, 0 < γ → 0 < m → 0 < p → 0 < highEnergy γ p m) ∧
      (∀ p, 0 < p → 0 ≤ Kp p) ∧
      (∀ γ p m, 0 < γ → 0 < m → 0 < p → 0 ≤ Kgauss γ p m) ∧
      ∀ (m p : ℝ), 0 < m → 0 < p →
        ∀ (law : Measure ℝ), [MeasureTheory.IsProbabilityMeasure law] →
        ∀ (E : ℝ) (Λ : Finset (Site ν)) (x : Site ν),
          (h0 : (0 : Site ν) ∈ Λ) → (hx : x ∈ Λ) →
        ∀ (N : ℝ), 0 < N →
          let S : Set (Configuration ν) :=
            {v | ∀ ε : ℝ, ∀ hε : ε ≠ 0,
              ‖finiteGreen ν Λ v E ε hε ⟨0, h0⟩ ⟨x, hx⟩‖ ≤
                Real.exp (m * (N - latticeLength ν x))}
          ((∃ δ : ℝ, HasBoundedDensity law δ ∧ δ⁻¹ ≤ largeDisorder p m) →
              MeasurableSet S ∧
                ENNReal.ofReal (1 - Kp p / Real.rpow N p) ≤ configurationMeasure ν law S) ∧
            (∀ (γ : ℝ) (hγ : 0 < γ), law = gaussianLaw γ hγ →
              highEnergy γ p m ≤ |E - 2 * (ν : ℝ)| →
              MeasurableSet S ∧
                ENNReal.ofReal (1 - Kgauss γ p m / Real.rpow N p) ≤
                  configurationMeasure ν law S) :=
  FroehlichSpencer.T12.Assembly.probability_bound_of_T21 ν hν
    (FroehlichSpencer.T12.Assembly.t21Hyp ν hν)

end FroehlichSpencer.Provider

end
