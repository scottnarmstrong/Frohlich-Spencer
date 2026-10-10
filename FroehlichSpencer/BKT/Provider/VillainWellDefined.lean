/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.VillainMeasure
public import FroehlichSpencer.BKT.Surface.VillainLaw
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Provider for `FroehlichSpencer.BKT.isProbabilityMeasure_villainLaw`

This module will contain `FroehlichSpencer.BKT.Provider.isProbabilityMeasure_villainLaw`, the proof of the
statement `FroehlichSpencer.BKT.isProbabilityMeasure_villainLaw` (file `FroehlichSpencer/BKT/Surface/VillainWellDefined.lean`).

-/

@[expose] public section

namespace FroehlichSpencer.BKT.Provider

open MeasureTheory

/--
The wired finite-volume Villain law is normalized because its KP partition integral is
strictly positive and finite.
-/
theorem isProbabilityMeasure_villainLaw (L : ℕ) (β : ℝ) (hβ : 0 < β) :
    IsProbabilityMeasure (villainLaw L β hβ) := by
  rw [isProbabilityMeasure_iff, villainLaw_eq_normalizedDensityMeasure L β hβ]
  rw [Measure.smul_apply, smul_eq_mul]
  have hmass := villainDensityMeasure_univ_pos_lt_top L β hβ
  exact ENNReal.inv_mul_cancel (ne_of_gt hmass.1) (ne_of_lt hmass.2)

end FroehlichSpencer.BKT.Provider

end
