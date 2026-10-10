module
public import Mathlib
public import FroehlichSpencer.BKT.Surface.VillainClockTheorem71One
public import FroehlichSpencer.BKT.Surface.VillainClock.VillainContinuousCorrelation
public import FroehlichSpencer.BKT.Surface.VillainClock.VillainContinuousLimit
public import FroehlichSpencer.BKT.Surface.VillainClock.FreeBox
import FroehlichSpencer.BKT.Surface.VillainClock.Bridge

@[expose] public section

open Filter Topology MeasureTheory

namespace FroehlichSpencer.BKT.Surface.VillainClock.Provider

theorem villain_clock_theorem71_one :
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
              atTop := by
  intro N hN β hβ ξ hξ0 hξN
  obtain ⟨hfin, hlim⟩ := FroehlichSpencer.BKT.villain_clock_theorem71_1
      N hN β hβ ξ hξ0 hξN
  constructor
  · intro Λ u v hu hv
    have h := hfin Λ u v hu hv
    rw [← FroehlichSpencer.BKT.Surface.VillainClock.Bridge.villainContinuousCorrelation_eq_internal β hβ (ξ : ℤ) Λ u v] at h
    simp only [← FroehlichSpencer.BKT.Surface.VillainClock.Bridge.latticeAngleLiteral_eq_internal] at h
    exact h
  · intro x
    have h := hlim x
    rw [← FroehlichSpencer.BKT.Surface.VillainClock.Bridge.villainContinuousLimit_eq_internal β hβ (ξ : ℤ) (0, 0) x] at h
    simp only [← FroehlichSpencer.BKT.Surface.VillainClock.Bridge.latticeAngleLiteral_eq_internal,
      ← FroehlichSpencer.BKT.Surface.VillainClock.Bridge.freeBox_eq_explicit] at h
    exact h

end FroehlichSpencer.BKT.Surface.VillainClock.Provider
