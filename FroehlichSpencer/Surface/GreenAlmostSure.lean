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
import FroehlichSpencer.Provider.GreenAlmostSure

open MeasureTheory

/-!
# Almost-sure exponential decay of the infinite-volume Green function (FS83, abstract)
-/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer

/--
in each regime , for every `m > 0` and energy `E`,
almost every configuration `v` has a radius `R(v)` beyond which
`|G(E + iε, v; 0, x)| ≤ e^{-(m/2)|x|}` for all `ε ≠ 0`; the event is measurable .
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
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.Provider.green_almostSure_decay ν hν
  -- FROZEN_ANCHOR_PROOF_END

-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer

end
-- FROZEN_ANCHOR_SUFFIX_END
