/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Topology.Order.LiminfLimsup
public import FroehlichSpencer.BKT.Bridge.VillainClockModel

@[expose] public section

open MeasureTheory Filter
open FroehlichSpencer.BKT.Bridge.VillainClockModel

namespace FroehlichSpencer.BKT.Bridge.VillainClockCorrelation

theorem villainClockLaw_twoPoint_eq (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 < β)
    (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    (∫ θ, Real.cos (ξ *
      (Rotator.Ginibre.latticeAngle θ u - Rotator.Ginibre.latticeAngle θ v))
      ∂FroehlichSpencer.BKT.villainClockModel N hN β hβ Λ) =
      (Clock.VillainClock.model N hN β hβ).twoPoint ξ Λ u v := by
  rw [villainClockModel_eq_gibbs]
  rfl

theorem villainClockLaw_limsup_eq_twoPointLimit (N : ℕ) (hN : 0 < N) (β : ℝ)
    (hβ : 0 < β) (ξ : ℤ) (u v : ℤ × ℤ) :
    Filter.limsup
      (fun L : ℕ => ∫ θ, Real.cos (ξ *
        (Rotator.Ginibre.latticeAngle θ u - Rotator.Ginibre.latticeAngle θ v))
        ∂FroehlichSpencer.BKT.villainClockModel N hN β hβ
          (Rotator.Ginibre.freeBox L)) atTop =
      (Clock.VillainClock.model N hN β hβ).twoPointLimit ξ u v := by
  apply Filter.Tendsto.limsup_eq
  convert (Clock.VillainClock.model N hN β hβ).tendsto_twoPointLimit ξ u v using 1
  funext L
  exact villainClockLaw_twoPoint_eq N hN β hβ ξ (Rotator.Ginibre.freeBox L) u v

end FroehlichSpencer.BKT.Bridge.VillainClockCorrelation

end
