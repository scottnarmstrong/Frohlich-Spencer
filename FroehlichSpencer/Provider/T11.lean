/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Surface.GaussianBoundedDensity
public import FroehlichSpencer.Surface.GaussianProbability
public import FroehlichSpencer.Surface.IntegratedDensityOfStatesSpec
public import FroehlichSpencer.Surface.IsDiffusionCoefficient
public import Mathlib.Analysis.Calculus.Deriv.Basic
import FroehlichSpencer.Reduction.T12ImpliesT11
import FroehlichSpencer.Surface.T12

/-!
# Provider for `FroehlichSpencer.theorem_1_1`

This module contains `FroehlichSpencer.Provider.theorem_1_1`, the proof of the statement
`FroehlichSpencer.theorem_1_1` (file `FroehlichSpencer/Surface/Theorem11.lean`, FS83 Theorem 1.1).

-/

@[expose] public section

open MeasureTheory

namespace FroehlichSpencer.Provider

/--
FS83 Theorem 1.1 (provider): the statement of `FroehlichSpencer.theorem_1_1`, proved
from the T1.2 by the Kubo-formula reduction.
-/
theorem theorem_1_1 (ν : ℕ) (hν : 0 < ν) :
    ∃ largeDisorder : ℝ, 0 < largeDisorder ∧
      ∃ highEnergy : {γ : ℝ // 0 < γ} → ℝ,
        (∀ γ : {γ : ℝ // 0 < γ}, 0 < highEnergy γ) ∧
        (∀ (law : Measure ℝ) [MeasureTheory.IsProbabilityMeasure law]
          (δ : ℝ) (hlaw : HasBoundedDensity law δ),
          δ⁻¹ ≤ largeDisorder →
          ∀ E r : ℝ,
            HasDerivAt (integratedDensityOfStates ν hν law δ hlaw) r E →
            0 < r →
              ∃! D : ℝ,
              is_diffusion_coefficient ν hν law E r D ∧ D = 0) ∧
        (∀ (γ : ℝ) (hγ : 0 < γ),
          ∀ E r : ℝ,
            highEnergy ⟨γ, hγ⟩ < |E - 2 * (ν : ℝ)| →
            HasDerivAt
              (integratedDensityOfStates ν hν (gaussianLaw γ hγ)
                (Real.sqrt (2 * Real.pi * γ)) (has_bounded_density_gaussian_law γ hγ))
              r E →
            0 < r →
            ∃! D : ℝ,
              is_diffusion_coefficient ν hν (gaussianLaw γ hγ) E r D ∧ D = 0) :=
  FroehlichSpencer.Reduction.theorem_1_1_of_green_probability_bound_statement ν hν
    (FroehlichSpencer.green_probability_bound ν hν)

end FroehlichSpencer.Provider

end
