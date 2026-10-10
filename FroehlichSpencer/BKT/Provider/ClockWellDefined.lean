/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.ClockLaw
public import FroehlichSpencer.BKT.Surface.ClockLaw
public import Mathlib.Probability.Notation
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.isProbabilityMeasure_clockLaw`

This module contains `FroehlichSpencer.BKT.Provider.isProbabilityMeasure_clockLaw`, the proof of the
statement `FroehlichSpencer.BKT.isProbabilityMeasure_clockLaw` (file
`FroehlichSpencer/BKT/Surface/ClockWellDefined.lean`).

-/

@[expose] public section

open MeasureTheory
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Bridge.ClockLaw

noncomputable section

namespace FroehlichSpencer.BKT.Provider

theorem isProbabilityMeasure_clockLaw (n : ℕ) (hn : 0 < n) (β : ℝ) (Λ : Finset (ℤ × ℤ)) :
    IsProbabilityMeasure (clockLaw n hn β Λ) := by
  rw [clockLaw_eq_pairGibbs n hn]
  exact isProbabilityMeasure_pairGibbs (clockMeasure_univ_ne_zero hn)
    (isBondWeight_clockBondWeight β Λ)

end FroehlichSpencer.BKT.Provider

end
