/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Surface.IntegratedDensityOfStates

/-! # Characterization of the integrated density of states -/

public section

open MeasureTheory

namespace FroehlichSpencer

/-- The selected integrated density of states is exactly the unique almost-sure
limit of the normalized cube eigenvalue counts. -/
theorem integratedDensityOfStates_spec (ν : ℕ) (hν : 0 < ν) (law : Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure law] (δ : ℝ) (hlaw : HasBoundedDensity law δ) :
    (∀ᵐ v ∂configurationMeasure ν law, ∀ E : ℝ,
      Filter.Tendsto
        (fun L : ℕ =>
          (finiteEigenvalueCount ν
            (Fintype.piFinset fun _ : Fin ν => Finset.Icc (-(L : ℤ)) (L : ℤ)) E v : ℝ) /
            ((Fintype.piFinset fun _ : Fin ν => Finset.Icc (-(L : ℤ)) (L : ℤ)).card : ℝ))
        Filter.atTop (nhds (integratedDensityOfStates ν hν law δ hlaw E))) ∧
      ∀ N' : ℝ → ℝ,
        (∀ᵐ v ∂configurationMeasure ν law, ∀ E : ℝ,
          Filter.Tendsto
            (fun L : ℕ =>
              (finiteEigenvalueCount ν
                (Fintype.piFinset fun _ : Fin ν => Finset.Icc (-(L : ℤ)) (L : ℤ)) E v : ℝ) /
                ((Fintype.piFinset fun _ : Fin ν => Finset.Icc (-(L : ℤ)) (L : ℤ)).card : ℝ))
            Filter.atTop (nhds (N' E))) →
        N' = integratedDensityOfStates ν hν law δ hlaw := by
  let hW := existsUnique_integratedDensityOfStates ν hν law δ hlaw
  have hchosen :
      ∀ᵐ v ∂configurationMeasure ν law, ∀ E : ℝ,
        Filter.Tendsto
          (fun L : ℕ =>
            (finiteEigenvalueCount ν
              (Fintype.piFinset fun _ : Fin ν => Finset.Icc (-(L : ℤ)) (L : ℤ)) E v : ℝ) /
              ((Fintype.piFinset fun _ : Fin ν => Finset.Icc (-(L : ℤ)) (L : ℤ)).card : ℝ))
          Filter.atTop
          (nhds ((Classical.choose hW.exists) E)) :=
    Classical.choose_spec hW.exists
  constructor
  · simpa only [integratedDensityOfStates] using hchosen
  · intro N' hN'
    have hEq := hW.unique hN' hchosen
    simpa only [integratedDensityOfStates] using hEq

end FroehlichSpencer

end
