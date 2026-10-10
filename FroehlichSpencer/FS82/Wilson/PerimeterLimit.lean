/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.PerimeterRoot
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.Ultrafilter
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# the perimeter law along cubes in limit form

For every positive `β` and rectangle, the real Wilson expectations along the centered cube
exhaustion lie in `[0, 1]` and have a cluster point.

Above the perimeter threshold, every cluster
point and the `liminf` satisfy the uniform perimeter lower bound.

If the sequence converges, its
limit satisfies the same estimate.

The existence of the thermodynamic limit in FS82 (2.6) is the cited Ginibre input.

Convergence is a hypothesis of the conditional limit theorem below.
-/

@[expose] public section

open Filter Topology MeasureTheory

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The real representative of the free finite-volume Wilson expectation for the canonical
`L × T` loop on the centered cube of half-side `N`. -/
def wilsonCubeExpectationReal (β : ℝ) (L T : ℕ) : ℕ → ℝ :=
  fun N => (primalWilsonExpectation β (cubePrimalSheet L T N)).re

/-- The absolute value of every finite-volume Wilson expectation is at most one. -/
theorem primalWilsonExpectation_norm_le_one {B : Box 4} (β : ℝ) (hβ : 0 < β)
    (S : Chain 4 B) : ‖primalWilsonExpectation β S‖ ≤ 1 := by
  rw [primalWilsonExpectation, primalWilsonNumerator, Complex.norm_div]
  have hden : 0 < primalVillainPartition (B := B) β := primalVillainPartition_pos β hβ
  rw [Complex.norm_real, Real.norm_of_nonneg hden.le]
  have hnum :
      ‖∫ θ : PrimalAngleConfig B,
        (primalVillainDensity (B := B) β θ : ℂ) * primalWilsonObservable θ S‖ ≤
      ∫ θ : PrimalAngleConfig B,
        ‖(primalVillainDensity (B := B) β θ : ℂ) * primalWilsonObservable θ S‖ :=
    norm_integral_le_integral_norm _
  have hnorm : ∀ θ : PrimalAngleConfig B,
      ‖(primalVillainDensity (B := B) β θ : ℂ) * primalWilsonObservable θ S‖ =
        primalVillainDensity (B := B) β θ := by
    intro θ
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (primalVillainDensity_pos β θ hβ).le]
    simp [primalWilsonObservable]
  calc
    ‖∫ θ : PrimalAngleConfig B,
        (primalVillainDensity (B := B) β θ : ℂ) * primalWilsonObservable θ S‖ /
        primalVillainPartition (B := B) β
      ≤ (∫ θ : PrimalAngleConfig B,
          ‖(primalVillainDensity (B := B) β θ : ℂ) * primalWilsonObservable θ S‖) /
          primalVillainPartition (B := B) β :=
        div_le_div_of_nonneg_right hnum hden.le
    _ = 1 := by
      rw [integral_congr_ae]
      · rw [primalVillainPartition]
        exact div_self hden.ne'
      · filter_upwards with θ
        rw [hnorm θ]

/-- The real part of every finite-volume Wilson expectation lies in `[0, 1]`. -/
theorem primalWilsonExpectation_re_mem_Icc {B : Box 4} (β : ℝ) (hβ : 0 < β)
    (S : Chain 4 B) : (primalWilsonExpectation β S).re ∈ Set.Icc 0 1 := by
  constructor
  · exact primalWilsonExpectation_re_nonneg β hβ S
  · exact (Complex.re_le_norm _).trans (primalWilsonExpectation_norm_le_one β hβ S)

/-- The cube Wilson expectation is real for every positive inverse temperature and every cube,
including cubes too small for the perimeter estimate. -/
theorem primalWilsonExpectation_cube_im_eq_zero {β : ℝ} (hβ : 0 < β)
    (L T N : ℕ) :
    (primalWilsonExpectation β (cubePrimalSheet L T N)).im = 0 := by
  exact primalWilsonExpectation_im_eq_zero β hβ _

/-- The real Wilson expectation sequence is contained in `[0,1]`. -/
theorem wilsonCubeExpectationReal_mem_Icc {β : ℝ} (hβ : 0 < β) (L T N : ℕ) :
    wilsonCubeExpectationReal β L T N ∈ Set.Icc 0 1 :=
  primalWilsonExpectation_re_mem_Icc β hβ _


/-- The bounded real cube-expectation sequence always has a cluster point. -/
theorem wilsonCubeExpectationReal_hasClusterPoint {β : ℝ} (hβ : 0 < β) (L T : ℕ) :
    ∃ x : ℝ, MapClusterPt x atTop (wilsonCubeExpectationReal β L T) := by
  let M := wilsonCubeExpectationReal β L T
  have hmem : ∀ n : ℕ, M n ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    exact wilsonCubeExpectationReal_mem_Icc hβ L T n
  obtain ⟨x, _, s, hs, hMs⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_Icc (0 : ℝ) 1) hmem
  have hsTop : Tendsto s atTop atTop := hs.tendsto_atTop
  exact ⟨x, MapClusterPt.of_comp hsTop hMs.mapClusterPt⟩

/-- Every sufficiently large cube carries the finite-volume perimeter lower bound. -/
theorem wilsonCubeExpectationReal_lower_of_large_cube {β : ℝ}
    (hβ : wilsonBetaThreshold ≤ β) {L T N : ℕ} (hL : 1 ≤ L) (hT : 1 ≤ T)
    (hN : max L T + 1 ≤ N) :
    Real.exp (-(wilsonPerimeterConstant β * ((L : ℝ) + T))) ≤
      wilsonCubeExpectationReal β L T N := by
  obtain ⟨w, hw, hlower⟩ := fs82_wilson_perimeter_cube hβ hL hT hN
  rw [wilsonCubeExpectationReal, hw]
  exact hlower

/-- Every cluster value along cubes obeys the uniform perimeter lower bound. -/
theorem wilsonCubeExpectationReal_cluster_lower {β : ℝ}
    (hβ : wilsonBetaThreshold ≤ β) {L T : ℕ} (hL : 1 ≤ L) (hT : 1 ≤ T)
    (x : ℝ) (hx : MapClusterPt x atTop (wilsonCubeExpectationReal β L T)) :
    Real.exp (-(wilsonPerimeterConstant β * ((L : ℝ) + T))) ≤ x := by
  rcases mapClusterPt_iff_ultrafilter.mp hx with ⟨U, hU, hM⟩
  have htail : ∀ᶠ N : ℕ in atTop,
      Real.exp (-(wilsonPerimeterConstant β * ((L : ℝ) + T))) ≤
        wilsonCubeExpectationReal β L T N := by
    filter_upwards [eventually_ge_atTop (max L T + 1)] with N hN
    exact wilsonCubeExpectationReal_lower_of_large_cube hβ hL hT hN
  have htailU := htail.filter_mono hU
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hM htailU

/-- The `liminf` of the cube-expectation sequence obeys the perimeter lower bound. -/
theorem wilsonCubeExpectationReal_liminf_lower {β : ℝ}
    (hβ : wilsonBetaThreshold ≤ β) {L T : ℕ} (hL : 1 ≤ L) (hT : 1 ≤ T) :
    Real.exp (-(wilsonPerimeterConstant β * ((L : ℝ) + T))) ≤
      Filter.liminf (wilsonCubeExpectationReal β L T) atTop := by
  let M := wilsonCubeExpectationReal β L T
  have hbounded : ∀ n : ℕ, M n ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    exact wilsonCubeExpectationReal_mem_Icc
      (lt_of_lt_of_le wilsonBetaThreshold_pos hβ) L T n
  have hupperBounded : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) M := by
    apply Filter.isBoundedUnder_of
    exact ⟨1, fun n => (hbounded n).2⟩
  have hlowerBounded : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) M := by
    apply Filter.isBoundedUnder_of
    exact ⟨0, fun n => (hbounded n).1⟩
  have hliminfCluster : MapClusterPt (Filter.liminf M atTop) atTop M := by
    exact MapClusterPt.liminf (hc := hupperBounded.isCoboundedUnder_flip)
      (hb := hlowerBounded)
  simpa [M] using
    wilsonCubeExpectationReal_cluster_lower hβ hL hT (Filter.liminf M atTop) hliminfCluster

/-- Conditional limit form of FS82 (2.8): any limit of the cube expectations obeys the same
perimeter estimate. The convergence hypothesis is the thermodynamic-limit input from (2.6). -/
theorem wilsonCubeExpectationReal_limit_lower {β : ℝ}
    (hβ : wilsonBetaThreshold ≤ β) {L T : ℕ} (hL : 1 ≤ L) (hT : 1 ≤ T)
    {w : ℝ} (hlim : Tendsto (wilsonCubeExpectationReal β L T) atTop (nhds w)) :
    Real.exp (-(wilsonPerimeterConstant β * ((L : ℝ) + T))) ≤ w := by
  exact wilsonCubeExpectationReal_cluster_lower hβ hL hT w hlim.mapClusterPt

/--
**FS82 (2.8) along cubes, including its conditional thermodynamic-limit form.** There is a
threshold `β₀ > 0` and, for each `β ≥ β₀`, one `dβ ≥ 0` independent of `L,T`, such that the real
cube-expectation sequence lies in `[0,1]`, has a cluster point, every cluster point and its
`liminf` are at least `exp(−dβ (L+T))`, and every existing sequence limit has the same lower
bound.

Existence of the limit is the cited Ginibre input in (2.6).
-/
theorem fs82_wilson_perimeter_cube_limit :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → ∃ d : ℝ, 0 ≤ d ∧
      ∀ L T : ℕ, 1 ≤ L → 1 ≤ T →
        let M := wilsonCubeExpectationReal β L T
        (∀ N, M N ∈ Set.Icc 0 1) ∧
        (∀ N, (primalWilsonExpectation β (cubePrimalSheet L T N)).im = 0) ∧
        (∃ x : ℝ, MapClusterPt x atTop M) ∧
        (∀ x : ℝ, MapClusterPt x atTop M →
          Real.exp (-(d * ((L : ℝ) + T))) ≤ x) ∧
        Real.exp (-(d * ((L : ℝ) + T))) ≤ Filter.liminf M atTop ∧
        (∀ w : ℝ, Tendsto M atTop (nhds w) →
          Real.exp (-(d * ((L : ℝ) + T))) ≤ w) := by
  refine ⟨wilsonBetaThreshold, wilsonBetaThreshold_pos, fun β hβ =>
    ⟨wilsonPerimeterConstant β, wilsonPerimeterConstant_nonneg hβ, ?_⟩⟩
  intro L T hL hT
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N
    exact wilsonCubeExpectationReal_mem_Icc
      (lt_of_lt_of_le wilsonBetaThreshold_pos hβ) L T N
  · intro N
    exact primalWilsonExpectation_cube_im_eq_zero
      (lt_of_lt_of_le wilsonBetaThreshold_pos hβ) L T N
  · exact wilsonCubeExpectationReal_hasClusterPoint
      (lt_of_lt_of_le wilsonBetaThreshold_pos hβ) L T
  · intro x hx
    exact wilsonCubeExpectationReal_cluster_lower hβ hL hT x hx
  · exact wilsonCubeExpectationReal_liminf_lower hβ hL hT
  · intro w hlim
    exact wilsonCubeExpectationReal_limit_lower hβ hL hT hlim

end

end FroehlichSpencer.FS82.Wilson

end
