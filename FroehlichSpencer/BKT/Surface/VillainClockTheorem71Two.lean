module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.LiminfLimsup
public import FroehlichSpencer.BKT.Surface.VillainClockModel
public import FroehlichSpencer.BKT.Rotator.FreeBox
public import FroehlichSpencer.BKT.Clock.Compact.Theorem71
public import FroehlichSpencer.BKT.Generic.Marked.Gap
public import FroehlichSpencer.BKT.Lattice2D.LogLowerBound
import FroehlichSpencer.BKT.Provider.VillainClockTheorem71Two

-- FROZEN_ANCHOR_PREFIX_BEGIN
@[expose] public section

open Filter Topology
open FroehlichSpencer.BKT.Clock.Compact (l1Dist)

namespace FroehlichSpencer.BKT

/-- FS81 Theorem 7.1(2), for the Villain-constrained clock model. One threshold and exponent
are shared by the finite, centered-box, and limiting statements. -/
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
            q ≤ Generic.Marked.dipoleGap ((ξ : ℝ) / N) →
              ((∀ (L : ℕ) (a b : Rotator.RotatorSpinSite L),
                  ∫ θ, Real.cos ((ξ : ℤ) *
                    (Rotator.Ginibre.latticeAngle θ (Rotator.Ginibre.siteToZ a) -
                      Rotator.Ginibre.latticeAngle θ (Rotator.Ginibre.siteToZ b)))
                    ∂villainClockModel N hN β hβ (Rotator.Ginibre.squareBoxZ L) ≤
                    2 * ((↑(Lattice2D.freeRadius a b) : ℝ) + 1) ^
                      (-((↑ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β N q)))) ∧
                (∀ (L : ℕ) (u v : ℤ × ℤ),
                  Rotator.Ginibre.boxRadius u ≤ L → Rotator.Ginibre.boxRadius v ≤ L →
                    ∫ θ, Real.cos ((ξ : ℤ) *
                      (Rotator.Ginibre.latticeAngle θ u - Rotator.Ginibre.latticeAngle θ v))
                      ∂villainClockModel N hN β hβ (Rotator.Ginibre.freeBox L) ≤
                      2 * ((↑(l1Dist u v) : ℝ) + 1) ^
                      (-((↑ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β N q)))) ∧
              ∀ (u v : ℤ × ℤ),
                Filter.limsup
                    (fun L : ℕ => ∫ θ, Real.cos ((ξ : ℤ) *
                      (Rotator.Ginibre.latticeAngle θ u - Rotator.Ginibre.latticeAngle θ v))
                      ∂villainClockModel N hN β hβ (Rotator.Ginibre.freeBox L))
                    atTop ≤
                  2 * ((↑(l1Dist u v) : ℝ) + 1) ^
                    (-((↑ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β N q)))) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.villain_clock_theorem71_2
  -- FROZEN_ANCHOR_PROOF_END

-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
