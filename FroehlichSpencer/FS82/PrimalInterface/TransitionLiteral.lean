/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.PrimalInterface.AreaLawLiteral

/-!
# the literal Wilson transition on centred cubes

One family of finite volumes, the centred cubes `[-N, N]⁴` with `N ≥ max(L, T) + 1`, carries both
laws of the loop `ℒ_{L×T}`: the area law for `0 < β ≤ β₀` and the perimeter law for `β ≥ β₁`, with
`0 < β₀ < β₁`.

Source: FS82 (2.7), (2.8).
-/

@[expose] public section

namespace FroehlichSpencer.FS82.PrimalInterface

open FroehlichSpencer.FS82.Infinite

theorem areaThreshold_lt_wilsonBetaThreshold : (1 / 80 : ℝ) < Wilson.wilsonBetaThreshold := by
  unfold Wilson.wilsonBetaThreshold
  have hrate : 0 ≤ FroehlichSpencer.FS82.Root.MomentComparisonAssembly.rootRate :=
    FroehlichSpencer.FS82.Root.MomentComparisonAssembly.rootRate_nonneg
  nlinarith

/-- **The literal Wilson transition on centred cubes.** -/
theorem fs82WilsonLoopTransitionCube :
    ∃ β₀ β₁ c : ℝ, 0 < β₀ ∧ β₀ < β₁ ∧ 0 < c ∧
      (∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ →
        ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ (N : ℕ) (hN : 0 < N), max L T + 1 ≤ N →
          (Surface.wilsonLoopExpectation (Surface.centredCube N hN) β hβ
            (Surface.rectangularLoop L T)).im = 0 ∧
          0 ≤ (Surface.wilsonLoopExpectation (Surface.centredCube N hN) β hβ
            (Surface.rectangularLoop L T)).re ∧
          (Surface.wilsonLoopExpectation (Surface.centredCube N hN) β hβ
            (Surface.rectangularLoop L T)).re ≤ Real.exp (-(c * ((L : ℝ) * T)))) ∧
      (∀ (β : ℝ) (hβ : 0 < β), β₁ ≤ β → ∃ d : ℝ, 0 ≤ d ∧
        ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ (N : ℕ) (hN : 0 < N), max L T + 1 ≤ N →
          (Surface.wilsonLoopExpectation (Surface.centredCube N hN) β hβ
            (Surface.rectangularLoop L T)).im = 0 ∧
          Real.exp (-(d * ((L : ℝ) + T))) ≤
            (Surface.wilsonLoopExpectation (Surface.centredCube N hN) β hβ
              (Surface.rectangularLoop L T)).re) := by
  refine ⟨1 / 80, Wilson.wilsonBetaThreshold, 1 / 2, by norm_num,
    areaThreshold_lt_wilsonBetaThreshold, by norm_num, ?_, ?_⟩
  · intro β hβ hsmall L T hL hT N hN hmax
    exact wilsonLoopExpectation_centredCube_areaLaw β hβ hsmall L T hL hT N hN hmax
  · intro β hβ hlarge
    refine ⟨Wilson.wilsonPerimeterConstant β, Wilson.wilsonPerimeterConstant_nonneg hlarge,
      fun L T hL hT N hN hmax => ?_⟩
    rw [wilsonLoopExpectation_centredCube β hβ L T N hN (by omega) (by omega)]
    obtain ⟨w, hw, hbound⟩ := Wilson.fs82_wilson_perimeter_cube hlarge hL hT hmax
    refine ⟨Wilson.primalWilsonExpectation_im_eq_zero β hβ _, ?_⟩
    rw [hw]
    simpa using hbound

end FroehlichSpencer.FS82.PrimalInterface

end
