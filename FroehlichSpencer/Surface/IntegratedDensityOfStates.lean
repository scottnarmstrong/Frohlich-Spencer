/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Surface.IDSWellDefined

/-! # Integrated density of states -/

public section

open MeasureTheory

namespace FroehlichSpencer

/-- The integrated density of states, selected from its proved almost-sure
cube-limit characterization. -/
@[expose] noncomputable def integratedDensityOfStates (ν : ℕ) (hν : 0 < ν)
    (law : Measure ℝ) [MeasureTheory.IsProbabilityMeasure law] (δ : ℝ)
    (hlaw : HasBoundedDensity law δ) : ℝ → ℝ :=
  Classical.choose (existsUnique_integratedDensityOfStates ν hν law δ hlaw).exists

end FroehlichSpencer

end
