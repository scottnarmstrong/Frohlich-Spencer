module
public import Mathlib.Topology.Order.LiminfLimsup
public import FroehlichSpencer.BKT.Surface.VillainClockModel
public import FroehlichSpencer.BKT.Surface.VillainClock.LatticeAngle
public import FroehlichSpencer.BKT.Surface.VillainClock.FreeBox
public import FroehlichSpencer.BKT.Surface.VillainClock.VillainContinuousCorrelation
public import FroehlichSpencer.BKT.Surface.VillainClock.VillainContinuousLimit
import FroehlichSpencer.BKT.Provider.VillainClockCorrelation

-- FROZEN_ANCHOR_PREFIX_BEGIN
@[expose] public section

open Filter Topology MeasureTheory

namespace FroehlichSpencer.BKT.Surface.VillainClock

theorem villain_clock_theorem71_1 :
    ∀ (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 < β),
      ∀ (ξ : ℕ), 1 ≤ ξ → ξ < N →
        (∀ (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ), u ∈ Λ → v ∈ Λ →
          VillainClock.villainContinuousCorrelation β hβ (ξ : ℤ) Λ u v ≤
            ∫ θ, Real.cos ((ξ : ℤ) *
              (VillainClock.latticeAngleLiteral θ u - VillainClock.latticeAngleLiteral θ v))
              ∂FroehlichSpencer.BKT.villainClockModel N hN β hβ Λ) ∧
        ∀ x : ℤ × ℤ,
          VillainClock.villainContinuousLimit β hβ (ξ : ℤ) (0, 0) x ≤
            Filter.limsup
              (fun L : ℕ => ∫ θ, Real.cos ((ξ : ℤ) *
                (VillainClock.latticeAngleLiteral θ (0, 0) - VillainClock.latticeAngleLiteral θ x))
                ∂FroehlichSpencer.BKT.villainClockModel N hN β hβ (VillainClock.freeBox L))
              atTop :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Surface.VillainClock.Provider.villain_clock_theorem71_one
  -- FROZEN_ANCHOR_PROOF_END

-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT.Surface.VillainClock
-- FROZEN_ANCHOR_SUFFIX_END
