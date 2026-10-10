module
public import Mathlib.Topology.Order.LiminfLimsup
public import FroehlichSpencer.BKT.Surface.VillainClockModel
public import FroehlichSpencer.BKT.Rotator.FreeBox
public import FroehlichSpencer.BKT.Clock.Source.ComplexObservable
import FroehlichSpencer.BKT.Provider.VillainClockTheorem71One

-- FROZEN_ANCHOR_PREFIX_BEGIN
@[expose] public section

open Filter

namespace FroehlichSpencer.BKT

/-- FS81 Theorem 7.1(1), in the real form identified with the complex character by reflection. -/
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
              atTop :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.villain_clock_theorem71_1
  -- FROZEN_ANCHOR_PROOF_END

-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
