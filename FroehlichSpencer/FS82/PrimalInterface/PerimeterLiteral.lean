/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Surface.WilsonCubeSequence
public import FroehlichSpencer.FS82.PrimalInterface.PrimalBridge
public import FroehlichSpencer.FS82.PrimalInterface.LoopBridge
public import FroehlichSpencer.FS82.Wilson.PerimeterLimit

/-!
# the literal perimeter root and its cube-limit form

Source: FS82 (1.13), (2.6), (2.8).
-/

@[expose] public section

namespace FroehlichSpencer.FS82.PrimalInterface

open Filter Topology
open FroehlichSpencer.FS82.Infinite

/-- The literal expectation on the centred cube is the internal one when the loop fits. -/
theorem wilsonLoopExpectation_centredCube (β : ℝ) (hβ : 0 < β) (L T N : ℕ) (hN : 0 < N)
    (hL : L ≤ N) (hT : T ≤ N) :
    Surface.wilsonLoopExpectation (Surface.centredCube N hN) β hβ
        (Surface.rectangularLoop L T) =
      Wilson.primalWilsonExpectation (B := cube N) β (Wilson.cubePrimalSheet L T N) :=
  wilsonLoopExpectation_eq (Surface.centredCube N hN) β hβ (Surface.rectangularLoop L T)
    (Wilson.cubePrimalSheet L T N) fun c => rectangularLoop_apply_embedding hL hT c


/-- Every Wilson loop expectation has absolute value at most one: `|W| = 1` and the law is a
probability measure. -/
theorem norm_wilsonLoopExpectation_le_one (R : Surface.RectBox4) (β : ℝ) (hβ : 0 < β)
    (loop : Surface.LatticeChain) : ‖Surface.wilsonLoopExpectation R β hβ loop‖ ≤ 1 := by
  have := primalVillainLaw_isProbabilityMeasure R β hβ
  unfold Surface.wilsonLoopExpectation
  refine (MeasureTheory.norm_integral_le_of_norm_le_const
    (C := 1) (Filter.Eventually.of_forall fun θ => ?_)).trans (by simp)
  unfold Surface.wilsonLoopObservable
  rw [norm_prod]
  exact le_of_eq (Finset.prod_eq_one fun ℓ _ => Complex.norm_exp_I_mul_ofReal _)

/-- The literal cube sequence is bounded by one. -/
theorem abs_wilsonCubeSequence_le_one (β : ℝ) (hβ : 0 < β) (L T n : ℕ) :
    |Surface.wilsonCubeSequence β hβ L T n| ≤ 1 :=
  (Complex.abs_re_le_norm _).trans (norm_wilsonLoopExpectation_le_one _ β hβ _)

/-- **The literal perimeter root on centred cubes.** -/
theorem fs82WilsonLoopPerimeterLawCube :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ (β : ℝ) (hβ : 0 < β), β₀ ≤ β → ∃ d : ℝ, 0 ≤ d ∧
      ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ (N : ℕ) (hN : 0 < N), max L T + 1 ≤ N →
        (Surface.wilsonLoopExpectation (Surface.centredCube N hN) β hβ
          (Surface.rectangularLoop L T)).im = 0 ∧
        Real.exp (-(d * ((L : ℝ) + T))) ≤
          (Surface.wilsonLoopExpectation (Surface.centredCube N hN) β hβ
            (Surface.rectangularLoop L T)).re := by
  obtain ⟨β₀, hβ₀, h⟩ := Wilson.fs82_wilson_perimeter_root_re
  refine ⟨β₀, hβ₀, fun β hβ hββ₀ => ?_⟩
  obtain ⟨d, hd, hd'⟩ := h β hββ₀
  refine ⟨d, hd, fun L T hL hT N hN hmax => ?_⟩
  rw [wilsonLoopExpectation_centredCube β hβ L T N hN (by omega) (by omega)]
  exact hd' L T hL hT N hmax

/-- The literal cube sequence and the internal one have the same image filter. -/
theorem map_wilsonCubeSequence (β : ℝ) (hβ : 0 < β) (L T : ℕ) :
    Filter.map (Surface.wilsonCubeSequence β hβ L T) atTop =
      Filter.map (Wilson.wilsonCubeExpectationReal β L T) atTop := by
  have hev : Surface.wilsonCubeSequence β hβ L T =ᶠ[atTop]
      (Wilson.wilsonCubeExpectationReal β L T ∘ fun n : ℕ => n + 1) := by
    filter_upwards [eventually_ge_atTop (max L T)] with n hn
    change (Surface.wilsonLoopExpectation (Surface.centredCube (n + 1) (Nat.succ_pos n)) β hβ
      (Surface.rectangularLoop L T)).re = _
    rw [wilsonLoopExpectation_centredCube β hβ L T (n + 1) (Nat.succ_pos n) (by omega) (by omega)]
    rfl
  rw [Filter.map_congr hev, ← Filter.map_map, Filter.map_add_atTop_eq_nat]

/-- **The literal perimeter law along the centred cubes, in limit form.** -/
theorem fs82WilsonLoopPerimeterLawCubeLimit :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ (β : ℝ) (hβ : 0 < β), β₀ ≤ β → ∃ d : ℝ, 0 ≤ d ∧
      ∀ L T : ℕ, 1 ≤ L → 1 ≤ T →
        (∃ x : ℝ, MapClusterPt x atTop (Surface.wilsonCubeSequence β hβ L T)) ∧
        (∀ x : ℝ, MapClusterPt x atTop (Surface.wilsonCubeSequence β hβ L T) →
          Real.exp (-(d * ((L : ℝ) + T))) ≤ x) ∧
        Real.exp (-(d * ((L : ℝ) + T))) ≤
          Filter.liminf (Surface.wilsonCubeSequence β hβ L T) atTop ∧
        ∀ w : ℝ, Tendsto (Surface.wilsonCubeSequence β hβ L T) atTop (nhds w) →
          Real.exp (-(d * ((L : ℝ) + T))) ≤ w := by
  obtain ⟨β₀, hβ₀, h⟩ := Wilson.fs82_wilson_perimeter_cube_limit
  refine ⟨β₀, hβ₀, fun β hβ hββ₀ => ?_⟩
  obtain ⟨d, hd, hd'⟩ := h β hββ₀
  refine ⟨d, hd, fun L T hL hT => ?_⟩
  obtain ⟨-, -, hcl, hcl', hlim, hten⟩ := hd' L T hL hT
  have hmap := map_wilsonCubeSequence β hβ L T
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hcl
    exact ⟨x, by unfold MapClusterPt at hx ⊢; rwa [hmap]⟩
  · intro x hx
    exact hcl' x (by unfold MapClusterPt at hx ⊢; rwa [← hmap])
  · have hl : Filter.liminf (Surface.wilsonCubeSequence β hβ L T) atTop =
        Filter.liminf (Wilson.wilsonCubeExpectationReal β L T) atTop := by
      unfold Filter.liminf
      rw [hmap]
    rw [hl]
    exact hlim
  · intro w hw
    exact hten w (by unfold Tendsto at hw ⊢; rwa [← hmap])

end FroehlichSpencer.FS82.PrimalInterface

end
