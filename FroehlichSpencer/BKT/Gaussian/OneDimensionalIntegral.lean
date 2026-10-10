/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# One dimensional Gaussian integrability adapter

This adapter confines the Mathlib Gaussian integral API used by the finite
graph GFF normalization proof to the one dimensional integrability statement.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- Every one dimensional Gaussian with positive decay rate is integrable. -/
theorem integrableRealGaussian {a : ℝ} (ha : 0 < a) :
    MeasureTheory.Integrable (fun x : ℝ => Real.exp (-a * x ^ 2))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
  _root_.integrable_exp_neg_mul_sq ha

end FroehlichSpencer.BKT
