/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

open scoped FourierTransform

namespace FroehlichSpencer.FS82.Poisson

/-- Fourier inversion at the origin on a finite-dimensional torus.  This is the
pointwise step that turns the coefficients of a periodized Schwartz function
into the multidimensional lattice sum. -/
theorem torus_fourier_sum_at_zero {d : Type*} [Fintype d]
    (F : C(UnitAddTorus d, ℂ))
    (hcoeff : Summable (UnitAddTorus.mFourierCoeff F)) :
    F 0 = ∑' k : d → ℤ, UnitAddTorus.mFourierCoeff F k := by
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hcoeff 0
  simpa [UnitAddTorus.mFourier] using h.tsum_eq.symm


end FroehlichSpencer.FS82.Poisson
