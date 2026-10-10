/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Surface.GaussianLaw

/-! # Probability instance for the Gaussian single-site law -/

public section

namespace FroehlichSpencer

/-- The Gaussian single-site law is a probability measure. -/
instance instIsProbabilityMeasureFSGaussianLaw (γ : ℝ) (hγ : 0 < γ) :
    MeasureTheory.IsProbabilityMeasure (gaussianLaw γ hγ) := by
  change MeasureTheory.IsProbabilityMeasure
    (ProbabilityTheory.gaussianReal 0 ⟨γ, le_of_lt hγ⟩)
  exact ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0
    ⟨γ, le_of_lt hγ⟩

end FroehlichSpencer

end
