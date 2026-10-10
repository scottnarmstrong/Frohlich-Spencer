/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Norm
public import FroehlichSpencer.Surface.BoundedDensityLaw
public import FroehlichSpencer.Surface.ConfigurationMeasure
public import FroehlichSpencer.Surface.GaussianLaw
public import FroehlichSpencer.Surface.GreenFunctionSpec
public import FroehlichSpencer.Surface.LatticeLength
import FroehlichSpencer.Reduction.GreenAlmostSure
import FroehlichSpencer.Surface.T12

/-!
# Provider for `FroehlichSpencer.green_almostSure_decay`

-/

@[expose] public section

open MeasureTheory

namespace FroehlichSpencer.Provider

/--
FS83 abstract (provider): the statement of `FroehlichSpencer.green_almostSure_decay`,
proved from the T1.2 by Borel–Cantelli.
-/
theorem green_almostSure_decay (ν : ℕ) (hν : 0 < ν) :
    ∃ (largeDisorder : ℝ → ℝ) (highEnergy : ℝ → ℝ → ℝ),
      (∀ m, 0 < m → 0 < largeDisorder m) ∧
      (∀ γ m, 0 < γ → 0 < m → 0 < highEnergy γ m) ∧
      ∀ (m : ℝ), 0 < m →
        ∀ (law : Measure ℝ), [MeasureTheory.IsProbabilityMeasure law] →
        ∀ (E : ℝ),
          let S : Set (Configuration ν) :=
            {v | ∃ R : ℝ, ∀ x : Site ν, R ≤ latticeLength ν x →
              ∀ ε : ℝ, ∀ hε : ε ≠ 0,
                ‖greenFunction ν hν
                    ((E : ℂ) + (ε : ℂ) * Complex.I) (by simpa using hε)
                    v (0 : Site ν) x‖ ≤
                  Real.exp (-(m / 2) * latticeLength ν x)}
          ((∃ δ : ℝ, HasBoundedDensity law δ ∧ δ⁻¹ ≤ largeDisorder m) →
              MeasurableSet S ∧ configurationMeasure ν law S = 1) ∧
            (∀ (γ : ℝ) (hγ : 0 < γ), law = gaussianLaw γ hγ →
              highEnergy γ m ≤ |E - 2 * (ν : ℝ)| →
              MeasurableSet S ∧ configurationMeasure ν law S = 1) :=
  FroehlichSpencer.Reduction.green_almostSure_decay_of_T12 ν hν
    (FroehlichSpencer.green_probability_bound ν hν)

end FroehlichSpencer.Provider

end
