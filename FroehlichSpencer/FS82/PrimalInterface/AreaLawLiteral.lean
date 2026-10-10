/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.PrimalInterface.PerimeterLiteral
public import FroehlichSpencer.FS82.Wilson.AreaLawPositioned

/-!
# the literal small-β area law on centred cubes and its cube-limit form

Source:
FS82 (2.6), (2.7).
-/

@[expose] public section

namespace FroehlichSpencer.FS82.PrimalInterface

open Filter Topology
open FroehlichSpencer.FS82.Infinite


theorem wilsonLoopExpectation_centredCube_areaLaw (β : ℝ) (hβ : 0 < β) (hsmall : β ≤ 1 / 80)
    (L T : ℕ) (hL : 1 ≤ L) (hT : 1 ≤ T) (N : ℕ) (hN : 0 < N) (hmax : max L T + 1 ≤ N) :
    (Surface.wilsonLoopExpectation (Surface.centredCube N hN) β hβ
        (Surface.rectangularLoop L T)).im = 0 ∧
      0 ≤ (Surface.wilsonLoopExpectation (Surface.centredCube N hN) β hβ
        (Surface.rectangularLoop L T)).re ∧
      (Surface.wilsonLoopExpectation (Surface.centredCube N hN) β hβ
        (Surface.rectangularLoop L T)).re ≤ Real.exp (-(1 / 2 * ((L : ℝ) * T))) := by
  rw [wilsonLoopExpectation_centredCube β hβ L T N hN (by omega) (by omega)]
  have h := Wilson.cubePrimalSheet_smallBeta_areaLaw hmax (by omega) (by omega) β hβ hsmall
  refine ⟨Wilson.primalWilsonExpectation_im_eq_zero β hβ _, h.1, h.2.trans (le_of_eq ?_)⟩
  congr 1
  ring

/-- **The literal small-β area law on centred cubes.** -/
theorem fs82WilsonLoopAreaLawCube :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ →
      ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ (N : ℕ) (hN : 0 < N), max L T + 1 ≤ N →
        (Surface.wilsonLoopExpectation (Surface.centredCube N hN) β hβ
          (Surface.rectangularLoop L T)).im = 0 ∧
        0 ≤ (Surface.wilsonLoopExpectation (Surface.centredCube N hN) β hβ
          (Surface.rectangularLoop L T)).re ∧
        (Surface.wilsonLoopExpectation (Surface.centredCube N hN) β hβ
          (Surface.rectangularLoop L T)).re ≤ Real.exp (-(c * ((L : ℝ) * T))) :=
  ⟨1 / 80, by norm_num, 1 / 2, by norm_num, fun β hβ hsmall L T hL hT N hN hmax =>
    wilsonLoopExpectation_centredCube_areaLaw β hβ hsmall L T hL hT N hN hmax⟩

/-- Along the centred cubes the literal sequence is eventually in `[0, exp(−LT/2)]`. -/
theorem eventually_wilsonCubeSequence_mem (β : ℝ) (hβ : 0 < β) (hsmall : β ≤ 1 / 80)
    (L T : ℕ) (hL : 1 ≤ L) (hT : 1 ≤ T) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ Surface.wilsonCubeSequence β hβ L T n ∧
      Surface.wilsonCubeSequence β hβ L T n ≤ Real.exp (-(1 / 2 * ((L : ℝ) * T))) := by
  filter_upwards [eventually_ge_atTop (max L T)] with n hn
  exact (wilsonLoopExpectation_centredCube_areaLaw β hβ hsmall L T hL hT (n + 1)
    (Nat.succ_pos n) (by omega)).2

/-- Every cluster value of the literal cube sequence obeys the area bound. -/
theorem wilsonCubeSequence_cluster_mem (β : ℝ) (hβ : 0 < β) (hsmall : β ≤ 1 / 80)
    (L T : ℕ) (hL : 1 ≤ L) (hT : 1 ≤ T) (x : ℝ)
    (hx : MapClusterPt x atTop (Surface.wilsonCubeSequence β hβ L T)) :
    0 ≤ x ∧ x ≤ Real.exp (-(1 / 2 * ((L : ℝ) * T))) := by
  rcases mapClusterPt_iff_ultrafilter.mp hx with ⟨U, hU, hM⟩
  have htail := (eventually_wilsonCubeSequence_mem β hβ hsmall L T hL hT).filter_mono hU
  exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hM (htail.mono fun _ h => h.1),
    le_of_tendsto_of_tendsto hM tendsto_const_nhds (htail.mono fun _ h => h.2)⟩

/-- **The literal small-β area law along the centred cubes, in limit form.** -/
theorem fs82WilsonLoopAreaLawCubeLimit :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ →
      ∀ L T : ℕ, 1 ≤ L → 1 ≤ T →
        (∃ x : ℝ, MapClusterPt x atTop (Surface.wilsonCubeSequence β hβ L T)) ∧
        (∀ x : ℝ, MapClusterPt x atTop (Surface.wilsonCubeSequence β hβ L T) →
          0 ≤ x ∧ x ≤ Real.exp (-(c * ((L : ℝ) * T)))) ∧
        Filter.limsup (Surface.wilsonCubeSequence β hβ L T) atTop ≤
          Real.exp (-(c * ((L : ℝ) * T))) ∧
        ∀ w : ℝ, Tendsto (Surface.wilsonCubeSequence β hβ L T) atTop (nhds w) →
          0 ≤ w ∧ w ≤ Real.exp (-(c * ((L : ℝ) * T))) := by
  refine ⟨1 / 80, by norm_num, 1 / 2, by norm_num, fun β hβ hsmall L T hL hT => ?_⟩
  set M := Surface.wilsonCubeSequence β hβ L T with hM
  have hbound : ∀ n : ℕ, M n ∈ Set.Icc (-1 : ℝ) 1 := fun n =>
    abs_le.mp (abs_wilsonCubeSequence_le_one β hβ L T n)
  have hupper : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) M :=
    Filter.isBoundedUnder_of ⟨1, fun n => (hbound n).2⟩
  have hlower : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) M :=
    Filter.isBoundedUnder_of ⟨-1, fun n => (hbound n).1⟩
  have hcluster := wilsonCubeSequence_cluster_mem β hβ hsmall L T hL hT
  refine ⟨?_, hcluster, ?_, fun w hw => hcluster w hw.mapClusterPt⟩
  · obtain ⟨x, _, s, hs, hMs⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc (-1 : ℝ) 1) hbound
    exact ⟨x, MapClusterPt.of_comp hs.tendsto_atTop hMs.mapClusterPt⟩
  · have hlimsup : MapClusterPt (Filter.limsup M atTop) atTop M :=
      MapClusterPt.limsup (hc := hlower.isCoboundedUnder_flip) (hb := hupper)
    exact (hcluster _ hlimsup).2

end FroehlichSpencer.FS82.PrimalInterface

end
