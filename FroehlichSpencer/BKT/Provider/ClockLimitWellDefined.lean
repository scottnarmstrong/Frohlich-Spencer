/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.ClockLaw
public import FroehlichSpencer.BKT.Bridge.PlaneRotatorLaw
public import FroehlichSpencer.BKT.Surface.ClockLaw
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.existsUnique_tendsto_clockTwoPoint`

This module contains `FroehlichSpencer.BKT.Provider.existsUnique_tendsto_clockTwoPoint`, the proof
of the statement `FroehlichSpencer.BKT.existsUnique_tendsto_clockTwoPoint` (file
`FroehlichSpencer/BKT/Surface/ClockLimitWellDefined.lean`).

-/

@[expose] public section

open MeasureTheory Filter Topology
open FroehlichSpencer.BKT.Bridge.ClockLaw

noncomputable section

namespace FroehlichSpencer.BKT.Provider

theorem existsUnique_tendsto_clockTwoPoint (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ)
    (j ℓ : ℤ × ℤ) :
    ∃! c : ℝ, Tendsto (fun Λ : {Λ : Finset (ℤ × ℤ) // j ∈ Λ ∧ ℓ ∈ Λ} =>
      ∫ θ : Λ.1 → ℝ, Real.cos ((ξ : ℝ) * (θ ⟨j, Λ.2.1⟩ - θ ⟨ℓ, Λ.2.2⟩))
        ∂clockLaw n hn β Λ.1) atTop (𝓝 c) := by
  have := Bridge.PlaneRotatorLaw.atTop_neBot_regions j ℓ
  have hlim := tendsto_clockTwoPoint n hn β hβ ξ j ℓ
  exact ⟨_, hlim, fun c hc => tendsto_nhds_unique hc hlim⟩

end FroehlichSpencer.BKT.Provider

end
