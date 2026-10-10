/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Filter.AtTopBot.Basic
public import FroehlichSpencer.Surface.BoundedDensityLaw
public import FroehlichSpencer.Surface.ConfigurationMeasure
public import FroehlichSpencer.Surface.FiniteEigenvalueCount
import FroehlichSpencer.Provider.IDSWellDefined

open MeasureTheory

/-! # Integrated density of states -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer

/--
existence and uniqueness of the integrated density of states.
-/
theorem existsUnique_integratedDensityOfStates (ν : ℕ) (hν : 0 < ν) (law : Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure law] (δ : ℝ) (hlaw : HasBoundedDensity law δ) :
    ∃! N : ℝ → ℝ,
      ∀ᵐ v ∂configurationMeasure ν law, ∀ E : ℝ,
        Filter.Tendsto
          (fun L : ℕ =>
            (finiteEigenvalueCount ν
              (Fintype.piFinset fun _ : Fin ν => Finset.Icc (-(L : ℤ)) (L : ℤ))
              E v : ℝ) /
            ((Fintype.piFinset fun _ : Fin ν => Finset.Icc (-(L : ℤ)) (L : ℤ)).card : ℝ))
          Filter.atTop (nhds (N E)) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.Provider.existsUnique_integratedDensityOfStates ν hν law δ hlaw
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer

end
-- FROZEN_ANCHOR_SUFFIX_END
