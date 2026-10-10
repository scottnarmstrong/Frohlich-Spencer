/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.PlaneRotatorLaw
public import FroehlichSpencer.BKT.Surface.PlaneRotatorLaw
public import Mathlib.Probability.Notation
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.existsUnique_tendsto_planeRotatorTwoPoint`

This module contains `FroehlichSpencer.BKT.Provider.existsUnique_tendsto_planeRotatorTwoPoint`, the
proof of the statement `FroehlichSpencer.BKT.existsUnique_tendsto_planeRotatorTwoPoint` (file
`FroehlichSpencer/BKT/Surface/PlaneRotatorLimitWellDefined.lean`).

-/

@[expose] public section

open MeasureTheory Filter Topology
open FroehlichSpencer.BKT.Rotator FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Bridge.PlaneRotatorLaw

noncomputable section

namespace FroehlichSpencer.BKT.Provider

theorem existsUnique_tendsto_planeRotatorTwoPoint (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ)
    (j ℓ : ℤ × ℤ) :
    ∃! c : ℝ, Tendsto (fun Λ : {Λ : Finset (ℤ × ℤ) // j ∈ Λ ∧ ℓ ∈ Λ} =>
      ∫ θ : Λ.1 → ℝ, Real.cos ((ξ : ℝ) * (θ ⟨j, Λ.2.1⟩ - θ ⟨ℓ, Λ.2.2⟩))
        ∂planeRotatorLaw β Λ.1) atTop (𝓝 c) := by
  have := atTop_neBot_regions j ℓ
  have hlim := tendsto_planeRotatorTwoPoint β hβ ξ j ℓ
  exact ⟨_, hlim, fun c hc => tendsto_nhds_unique hc hlim⟩

end FroehlichSpencer.BKT.Provider

end
