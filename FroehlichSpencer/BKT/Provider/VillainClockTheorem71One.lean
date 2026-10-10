/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Topology.Order.LiminfLimsup
public import FroehlichSpencer.BKT.Surface.VillainClockModel
public import FroehlichSpencer.BKT.Rotator.FreeBox
public import FroehlichSpencer.BKT.Clock.Source.ComplexObservable
public import FroehlichSpencer.BKT.Clock.VillainClock.Model
public import FroehlichSpencer.BKT.Bridge.VillainClockCorrelation


@[expose] public section

open MeasureTheory Filter
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Clock.VillainClock
open FroehlichSpencer.BKT.Bridge.VillainClockCorrelation

namespace FroehlichSpencer.BKT.Provider

theorem villain_clock_theorem71_1 :
    ∀ (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 < β),
      ∀ (ξ : ℕ), 1 ≤ ξ → ξ < N →
        (∀ (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ), u ∈ Λ → v ∈ Λ →
          (Ginibre.villainModel β hβ).twoPoint (ξ : ℤ) Λ u v ≤
            ∫ θ, Real.cos ((ξ : ℤ) *
              (Rotator.Ginibre.latticeAngle θ u - Rotator.Ginibre.latticeAngle θ v))
              ∂villainClockModel N hN β hβ Λ) ∧
        ∀ x : ℤ × ℤ,
          (Ginibre.villainModel β hβ).twoPointLimit (ξ : ℤ) (0, 0) x ≤
            Filter.limsup
              (fun L : ℕ => ∫ θ, Real.cos ((ξ : ℤ) *
                (Rotator.Ginibre.latticeAngle θ (0, 0) -
                  Rotator.Ginibre.latticeAngle θ x))
                ∂villainClockModel N hN β hβ
                  (Finset.Icc (-(L : ℤ)) L ×ˢ Finset.Icc (-(L : ℤ)) L))
              atTop := by
  intro N hN β hβ ξ hξ0 hξN
  constructor
  · intro Λ u v hu hv
    have h := Clock.VillainClock.finite_correlation_dominates hN hβ (ξ : ℤ) Λ u v
    exact h.trans_eq (villainClockLaw_twoPoint_eq N hN β hβ (ξ : ℤ) Λ u v).symm
  · intro x
    have h := Clock.VillainClock.limit_correlation_dominates hN hβ (ξ : ℤ) (0, 0) x
    exact h.trans_eq
      (villainClockLaw_limsup_eq_twoPointLimit N hN β hβ (ξ : ℤ) (0, 0) x).symm

end FroehlichSpencer.BKT.Provider

end
