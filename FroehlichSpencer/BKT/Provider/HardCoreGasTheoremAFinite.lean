/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.HardCoreSecondMomentFree
public import FroehlichSpencer.BKT.Surface.CoulombPotential
public import FroehlichSpencer.BKT.Surface.HardCoreSecondMoment
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.hardCoreGas_secondMoment_lower_bound`

This module contains `FroehlichSpencer.BKT.Provider.hardCoreGas_secondMoment_lower_bound`, the proof
of the statement `FroehlichSpencer.BKT.hardCoreGas_secondMoment_lower_bound` (file
`FroehlichSpencer/BKT/Surface/HardCoreGasTheoremAFinite.lean`).

-/

@[expose] public section

open MeasureTheory Filter Topology
open FroehlichSpencer.BKT.Coulomb
open FroehlichSpencer.BKT.Bridge.HardCoreSecondMoment
open FroehlichSpencer.BKT.Bridge.HardCoreSecondMomentFree

noncomputable section

namespace FroehlichSpencer.BKT.Provider


theorem hardCoreGas_secondMoment_lower_bound :
    ∀ δ : ℝ, 0 < δ → ∀ α : ℝ, ∃ β₀ : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
      ∀ (z : ℝ) (hz : 0 ≤ z), z ≤ Real.exp (β / 17 + α) →
        ∀ (Λ : Finset (ℤ × ℤ)) (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ)
          (hg : (g.sum fun _ a => a) = 0),
          (1 - δ) * β * (g.sum fun x a => g.sum fun y b => a * b * coulombPotential (x - y)) ≤
            hardCoreSecondMoment β hβ z hz Λ g hgΛ hg := by
  intro δ hδ α
  obtain ⟨κ₀, -, h⟩ := free_secondMoment_lower_bound δ hδ α
  refine ⟨κ₀, fun β hβ hβκ z hz hzβ Λ g hgΛ hg => ?_⟩
  rw [quad_eq_freeQuad Λ g hgΛ, hardCoreSecondMoment_eq_free]
  exact h Λ β hβ hβκ z hz hzβ (fun v => g v) (sum_region_eq_zero Λ g hgΛ hg)

end FroehlichSpencer.BKT.Provider

end
