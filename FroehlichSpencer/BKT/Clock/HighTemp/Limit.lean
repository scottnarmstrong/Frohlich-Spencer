/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Window.MasslessWindow
public import FroehlichSpencer.BKT.Clock.HighTemp.FreeBoxEstimate
import Mathlib.Tactic.Linarith

/-!
# Transfer the finite-box clock bound to the free limit

The finite estimate is uniform in the box. Convergence along centered free
boxes therefore gives exponential decay of the infinite-volume clock
correlation with constants independent of the clock order.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.HighTemp

open Filter Topology
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Clock.Window
open FroehlichSpencer.BKT.Clock.Compact (l1Dist)

/-- The free-limit clock correlation inherits the uniform finite-box estimate. -/
theorem clockModel_twoPointLimit_le_exp {n : ℕ} (hn : 2 ≤ n) {β : ℝ} (hβ : 0 ≤ β)
    (hβsmall : β ≤ Real.log (8 / 7) / 2) (u v : ℤ × ℤ) :
    (clockModel n (by omega) β hβ).twoPointLimit 1 u v ≤
      2 * Real.exp (-Real.log 2 * (l1Dist u v : ℝ)) := by
  let M := clockModel n (by omega) β hβ
  have ht := M.tendsto_twoPointLimit 1 u v
  refine le_of_tendsto ht ?_
  filter_upwards [eventually_ge_atTop (max (boxRadius u) (boxRadius v))] with L hL
  exact clockModel_twoPoint_freeBox_le_exp_small n L hn hβ hβsmall u v
    ((le_max_left _ _).trans hL) ((le_max_right _ _).trans hL)

/-- **Clock high-temperature exponential decay.** The bond expansion gives a
uniform high-temperature interval and the correlation decays with constants
`C = 2` and `m = log 2`, uniformly over all `n ≥ 2`. -/
theorem clockHighTemperatureStatement_holds : ClockHighTemperatureStatement := by
  have hbeta : 0 < Real.log (8 / 7) / 2 := by
    apply div_pos
    · apply Real.log_pos
      norm_num
    · norm_num
  refine ⟨Real.log (8 / 7) / 2, hbeta, fun n hn β hβ hβsmall => ?_⟩
  refine ⟨2, Real.log 2, Real.log_pos (by norm_num), fun u v => ?_⟩
  change (clockModel n (by omega) β hβ).twoPointLimit 1 u v ≤
    2 * Real.exp (-Real.log 2 * (l1Dist u v : ℝ))
  exact clockModel_twoPointLimit_le_exp hn hβ hβsmall.le u v

end FroehlichSpencer.BKT.Clock.HighTemp

end
