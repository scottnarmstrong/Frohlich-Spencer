/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Probability.ProductMeasure
public import FroehlichSpencer.Surface.ConfigurationSpace

open MeasureTheory

/-! # Product law of the potential -/

public section

namespace FroehlichSpencer

/-- The iid product probability measure with single-site law `law`. -/
@[expose] noncomputable def configurationMeasure (ν : ℕ) (law : Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure law] : Measure (Configuration ν) :=
  Measure.infinitePi (fun _ : Site ν => law)

end FroehlichSpencer


end
