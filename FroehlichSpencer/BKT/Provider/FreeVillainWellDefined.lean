/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.FreeVillainLaw
public import FroehlichSpencer.BKT.Surface.FreeVillainLaw
public import Mathlib.Probability.Notation

/-!
# Provider for `FroehlichSpencer.BKT.isProbabilityMeasure_freeVillainLaw`

This module contains `FroehlichSpencer.BKT.Provider.isProbabilityMeasure_freeVillainLaw`, the proof
of the statement `FroehlichSpencer.BKT.isProbabilityMeasure_freeVillainLaw` (file
`FroehlichSpencer/BKT/Surface/FreeVillainWellDefined.lean`, the normalization gate of FS81
(1.26)).

The total mass of `freeVillainLaw` is in `(0, ∞)`
(`Bridge.FreeVillainLaw.freeVillainMass_pos_lt_top`).
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open FroehlichSpencer.BKT.Bridge.FreeVillainLaw

/-- **The gate `isProbabilityMeasure_freeVillainLaw`** (package §4.9). -/
theorem isProbabilityMeasure_freeVillainLaw (β : ℝ) (hβ : 0 < β) (Λ : Finset (ℤ × ℤ)) :
    IsProbabilityMeasure (freeVillainLaw β hβ Λ) := by
  obtain ⟨hpos, htop⟩ := freeVillainMass_pos_lt_top β hβ Λ
  rw [freeVillainLaw_eq]
  constructor
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' htop.ne

end FroehlichSpencer.BKT.Provider

end
