/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.ClockPhases
public import FroehlichSpencer.BKT.Clock.HighTemp.Limit
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.clock_highTemperature_expDecay`

This module contains `FroehlichSpencer.BKT.Provider.clock_highTemperature_expDecay`, the proof of
the statement `FroehlichSpencer.BKT.clock_highTemperature_expDecay` (file
`FroehlichSpencer/BKT/Surface/ClockHighTemperature.lean`, the high-temperature phase).

It is
imported only by that statement.

From `Clock.HighTemp.clockHighTemperatureStatement_holds` through
`Bridge.ClockPhases.isClockExpDecay_of_internal`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open Filter Topology
open FroehlichSpencer.BKT.Clock
open FroehlichSpencer.BKT.Bridge.ClockPhases
  (isClockExpDecay_of_internal isClockLongRangeOrder_of_internal)


theorem clock_highTemperature_expDecay :
    ∃ βh : ℝ, 0 < βh ∧ ∀ (n : ℕ) (hn : 0 < n), 2 ≤ n → ∀ (β : ℝ) (hβ : 0 ≤ β), β < βh →
      IsClockExpDecay n hn β hβ 1 := by
  obtain ⟨βh, hβh, h⟩ := HighTemp.clockHighTemperatureStatement_holds
  exact ⟨βh, hβh, fun n hn h2 β hβ hlt => isClockExpDecay_of_internal hn hβ (h n h2 β hβ hlt)⟩

end FroehlichSpencer.BKT.Provider

end
