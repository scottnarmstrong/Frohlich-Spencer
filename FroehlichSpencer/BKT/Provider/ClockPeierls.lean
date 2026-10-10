/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.ClockPhases
public import FroehlichSpencer.BKT.Clock.Peierls.ClockPeierls
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.clock_lowTemperature_longRangeOrder`

This module contains `FroehlichSpencer.BKT.Provider.clock_lowTemperature_longRangeOrder`, the proof
of the statement `FroehlichSpencer.BKT.clock_lowTemperature_longRangeOrder` (file
`FroehlichSpencer/BKT/Surface/ClockPeierls.lean`, the low-temperature phase).

From `Clock.Peierls.clockPeierlsStatement_holds` through
`Bridge.ClockPhases.isClockLongRangeOrder_of_internal`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open Filter Topology
open FroehlichSpencer.BKT.Clock
open FroehlichSpencer.BKT.Bridge.ClockPhases
  (isClockExpDecay_of_internal isClockLongRangeOrder_of_internal)


theorem clock_lowTemperature_longRangeOrder :
    ∀ (n : ℕ) (hn : 0 < n), 2 ≤ n → ∃ βbar : ℝ, ∀ (β : ℝ) (hβ : 0 ≤ β), βbar < β →
      ∀ ξ : ℤ, IsClockLongRangeOrder n hn β hβ ξ := by
  intro n hn h2
  obtain ⟨βbar, h⟩ := Peierls.clockPeierlsStatement_holds n h2
  exact ⟨βbar, fun β hβ hlt ξ => isClockLongRangeOrder_of_internal hn hβ (h β hβ hlt ξ)⟩

end FroehlichSpencer.BKT.Provider

end
