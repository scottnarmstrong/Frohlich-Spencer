/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.HardCoreSecondMoment
public import FroehlichSpencer.BKT.Surface.PeriodicHardCoreSecondMoment
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.existsUnique_tendsto_periodicHardCoreSecondMoment`

This module contains
`FroehlichSpencer.BKT.Provider.existsUnique_tendsto_periodicHardCoreSecondMoment`, the proof of the
statement `FroehlichSpencer.BKT.existsUnique_tendsto_periodicHardCoreSecondMoment` (file
`FroehlichSpencer/BKT/Surface/HardCoreSecondMomentWellDefined.lean`).

-/

@[expose] public section

open MeasureTheory Filter Topology
open Fin.CommRing
open FroehlichSpencer.BKT.Coulomb
open FroehlichSpencer.BKT.Bridge.HardCoreSecondMoment

noncomputable section

namespace FroehlichSpencer.BKT.Provider

theorem existsUnique_tendsto_periodicHardCoreSecondMoment (β : ℝ) (hβ : 0 < β) (z : ℝ)
    (hz : 0 ≤ z) (Λ : Finset (ℤ × ℤ)) (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ)
    (hg : (g.sum fun _ a => a) = 0) :
    ∃! m : ℝ, Tendsto (fun n : ℕ =>
      periodicHardCoreSecondMoment β hβ z Λ g (2 * n + 2) (Nat.one_lt_succ_succ (2 * n)))
      atTop (𝓝 m) := by
  have hlim := tendsto_periodicHardCoreSecondMoment β hβ z hz Λ g hgΛ hg
  exact ⟨_, hlim, fun m hm => tendsto_nhds_unique hm hlim⟩

end FroehlichSpencer.BKT.Provider

end
