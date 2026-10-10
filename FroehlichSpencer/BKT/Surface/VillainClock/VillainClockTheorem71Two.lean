module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.LiminfLimsup
public import FroehlichSpencer.BKT.Surface.VillainClockModel
public import FroehlichSpencer.BKT.Surface.VillainClock.LatticeAngle
public import FroehlichSpencer.BKT.Surface.VillainClock.RotatorSpinSite
public import FroehlichSpencer.BKT.Surface.VillainClock.SiteToZ
public import FroehlichSpencer.BKT.Surface.VillainClock.SquareBoxZ
public import FroehlichSpencer.BKT.Surface.VillainClock.BoxRadius
public import FroehlichSpencer.BKT.Surface.VillainClock.FreeBox
public import FroehlichSpencer.BKT.Surface.VillainClock.L1Dist
public import FroehlichSpencer.BKT.Surface.VillainClock.FreeRadius
public import FroehlichSpencer.BKT.Surface.VillainClock.DipoleGap
import FroehlichSpencer.BKT.Provider.VillainClockDisorder

-- FROZEN_ANCHOR_PREFIX_BEGIN
@[expose] public section

open Filter Topology MeasureTheory

namespace FroehlichSpencer.BKT.Surface.VillainClock

theorem villain_clock_theorem71_2 :
    ∃ n₀ : ℝ → ℝ → ℕ, ∃ β'' : ℝ → ℕ → ℝ → ℝ,
      (∀ q : ℝ, 0 < q →
        Tendsto (fun β : ℝ => n₀ β q) atTop atTop) ∧
      (∀ β : ℝ, Tendsto (fun q : ℝ => n₀ β q) (𝓝[>] 0) atTop) ∧
      (∀ (β : ℝ) (N : ℕ) (q : ℝ), n₀ β q ≤ N →
        0 < β'' β N q) ∧
      ∀ q : ℝ, 0 < q →
        ∀ (β : ℝ) (hβ : 0 < β) (N : ℕ), n₀ β q ≤ N →
          ∀ (hN : 0 < N) (ξ : ℕ), 0 < ξ → ξ < N →
            q ≤ VillainClock.dipoleGap ((ξ : ℝ) / N) →
              ((∀ (L : ℕ) (a b : VillainClock.rotatorSpinSite L),
                  ∫ θ, Real.cos ((ξ : ℤ) *
                    (VillainClock.latticeAngleLiteral θ (VillainClock.siteToZ a) -
                      VillainClock.latticeAngleLiteral θ (VillainClock.siteToZ b)))
                    ∂FroehlichSpencer.BKT.villainClockModel N hN β hβ (VillainClock.squareBoxZ L) ≤
                    2 * ((↑(VillainClock.freeRadius a b) : ℝ) + 1) ^
                      (-((↑ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β N q)))) ∧
                (∀ (L : ℕ) (u v : ℤ × ℤ),
                  VillainClock.boxRadius u ≤ L → VillainClock.boxRadius v ≤ L →
                    ∫ θ, Real.cos ((ξ : ℤ) *
                      (VillainClock.latticeAngleLiteral θ u - VillainClock.latticeAngleLiteral θ v))
                      ∂FroehlichSpencer.BKT.villainClockModel N hN β hβ (VillainClock.freeBox L) ≤
                      2 * ((↑(VillainClock.l1Dist u v) : ℝ) + 1) ^
                      (-((↑ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β N q)))) ∧
              ∀ (u v : ℤ × ℤ),
                Filter.limsup
                    (fun L : ℕ => ∫ θ, Real.cos ((ξ : ℤ) *
                      (VillainClock.latticeAngleLiteral θ u - VillainClock.latticeAngleLiteral θ v))
                      ∂FroehlichSpencer.BKT.villainClockModel N hN β hβ (VillainClock.freeBox L))
                    atTop ≤
                  2 * ((↑(VillainClock.l1Dist u v) : ℝ) + 1) ^
                    (-((↑ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β N q)))) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Surface.VillainClock.Provider.villain_clock_theorem71_two
  -- FROZEN_ANCHOR_PROOF_END

-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT.Surface.VillainClock
-- FROZEN_ANCHOR_SUFFIX_END
