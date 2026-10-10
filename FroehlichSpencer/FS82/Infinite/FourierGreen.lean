/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Infinite.FourierParseval

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory
open scoped Real

@[expose] public section

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

namespace FroehlichSpencer.FS82.Infinite.Fourier

def chordSq (x : ℝ) : ℝ := Complex.normSq (1 - fourier 1 (x : AddCircle (1 : ℝ)))

theorem chordSq_eq (x : ℝ) : chordSq x = 4 * Real.sin (Real.pi * x) ^ 2 := by
  unfold chordSq
  rw [fourier_coe_apply]
  have hexp : Complex.exp (2 * Real.pi * Complex.I * (1 : ℤ) * x / (1 : ℝ)) =
      Complex.exp ((2 * Real.pi * x) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [hexp]
  rw [show (2 * (Real.pi : ℝ) * (x : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im]
  rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring, Real.cos_two_mul]
  rw [Real.sin_two_mul]
  ring_nf
  nlinarith [Real.sin_sq (Real.pi * x), Real.sin_sq_add_cos_sq (Real.pi * x)]

theorem abs_sin_pi_lower_half {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    2 * x ≤ |Real.sin (Real.pi * x)| := by
  have harg : |Real.pi * x| ≤ Real.pi / 2 := by
    rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le hx0)]
    nlinarith [Real.pi_pos]
  have h := Real.mul_abs_le_abs_sin harg
  rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le hx0)] at h
  have hmul : 2 / Real.pi * (Real.pi * x) = 2 * x := by
    field_simp [ne_of_gt Real.pi_pos]
  rw [hmul] at h
  exact h

theorem chordSq_lower_left {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) :
    16 * x ^ 2 ≤ chordSq x := by
  rw [chordSq_eq]
  have hs := abs_sin_pi_lower_half hx0.le hx
  have hsq : (2 * x) ^ 2 ≤ |Real.sin (Real.pi * x)| ^ 2 := by
    nlinarith [sq_nonneg (|Real.sin (Real.pi * x)| - 2 * x)]
  rw [sq_abs] at hsq
  nlinarith

theorem chordSq_lower_right {x : ℝ} (hx : 1 / 2 ≤ x) (hx1 : x < 1) :
    16 * (1 - x) ^ 2 ≤ chordSq x := by
  have hy0 : 0 < 1 - x := by linarith
  have hy : 1 - x ≤ 1 / 2 := by linarith
  rw [chordSq_eq]
  have hs := abs_sin_pi_lower_half hy0.le hy
  have hsin : Real.sin (Real.pi * x) = Real.sin (Real.pi * (1 - x)) := by
    rw [show Real.pi * x = Real.pi - Real.pi * (1 - x) by ring,
      Real.sin_pi_sub]
  rw [← hsin] at hs
  have hsq : (2 * (1 - x)) ^ 2 ≤ |Real.sin (Real.pi * x)| ^ 2 := by
    nlinarith [sq_nonneg (|Real.sin (Real.pi * x)| - 2 * (1 - x))]
  rw [sq_abs] at hsq
  nlinarith

theorem intervalIntegrable_rpow_half :
    IntervalIntegrable (fun x : ℝ => x ^ (-1 / 2 : ℝ)) volume 0 1 := by
  apply intervalIntegral.intervalIntegrable_rpow'
  norm_num

theorem intervalIntegrable_one_sub_rpow_half :
    IntervalIntegrable (fun x : ℝ => (1 - x) ^ (-1 / 2 : ℝ)) volume 0 1 := by
  have h := intervalIntegrable_rpow_half.comp_sub_left 1
  simpa using h.symm

def intervalGreenMajorant (x : ℝ) : ℝ :=
  4 ^ (-1 / 2 : ℝ) * x ^ (-1 / 2 : ℝ) +
    4 ^ (-1 / 2 : ℝ) * (1 - x) ^ (-1 / 2 : ℝ)


def intervalGreenWeight (x : ℝ) : ℝ := chordSq x ^ (-1 / 4 : ℝ)

theorem intervalGreenWeight_le_majorant {x : ℝ} (hx : x ∈ Set.Ioc 0 1) :
    intervalGreenWeight x ≤ intervalGreenMajorant x := by
  have hx0 : 0 < x := hx.1
  have hx1 : x ≤ 1 := hx.2
  by_cases hmid : x ≤ 1 / 2
  · have hlower := chordSq_lower_left hx0 hmid
    have hmono := Real.rpow_le_rpow_of_nonpos
      (show 0 < 16 * x ^ 2 by positivity) hlower (by norm_num : (-1 / 4 : ℝ) ≤ 0)
    have hpow : (16 * x ^ 2) ^ (-1 / 4 : ℝ) =
        4 ^ (-1 / 2 : ℝ) * x ^ (-1 / 2 : ℝ) := by
      calc
        (16 * x ^ 2) ^ (-1 / 4 : ℝ) = ((4 * x) ^ 2) ^ (-1 / 4 : ℝ) := by
          congr 1
          ring
        _ = ((4 * x) ^ (2 : ℝ)) ^ (-1 / 4 : ℝ) := by
          congr 1
          exact (Real.rpow_natCast (4 * x) 2).symm
        _ = (4 * x) ^ ((2 : ℝ) * (-1 / 4 : ℝ)) := by
          exact (Real.rpow_mul (x := 4 * x) (by positivity) 2 (-1 / 4 : ℝ)).symm
        _ = (4 * x) ^ (-1 / 2 : ℝ) := by
          congr 1
          norm_num
        _ = 4 ^ (-1 / 2 : ℝ) * x ^ (-1 / 2 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) hx0.le]
    unfold intervalGreenWeight intervalGreenMajorant
    rw [← hpow]
    have hnonneg : 0 ≤ 4 ^ (-1 / 2 : ℝ) * (1 - x) ^ (-1 / 2 : ℝ) := by
      positivity
    linarith
  · have hmid' : 1 / 2 ≤ x := le_of_not_ge hmid
    by_cases hxend : x = 1
    · subst x
      unfold intervalGreenWeight intervalGreenMajorant
      rw [chordSq_eq]
      norm_num
    · have hx1' : x < 1 := lt_of_le_of_ne hx1 hxend
      have hlower := chordSq_lower_right hmid' hx1'
      have hypos : 0 < 1 - x := by linarith
      have hmono := Real.rpow_le_rpow_of_nonpos
        (show 0 < 16 * (1 - x) ^ 2 by positivity) hlower
        (by norm_num : (-1 / 4 : ℝ) ≤ 0)
      have hpow : (16 * (1 - x) ^ 2) ^ (-1 / 4 : ℝ) =
          4 ^ (-1 / 2 : ℝ) * (1 - x) ^ (-1 / 2 : ℝ) := by
        calc
          (16 * (1 - x) ^ 2) ^ (-1 / 4 : ℝ) = ((4 * (1 - x)) ^ 2) ^ (-1 / 4 : ℝ) := by
            congr 1
            ring
          _ = ((4 * (1 - x)) ^ (2 : ℝ)) ^ (-1 / 4 : ℝ) := by
            congr 1
            exact (Real.rpow_natCast (4 * (1 - x)) 2).symm
          _ = (4 * (1 - x)) ^ ((2 : ℝ) * (-1 / 4 : ℝ)) := by
            exact (Real.rpow_mul (x := 4 * (1 - x)) (by positivity) 2 (-1 / 4 : ℝ)).symm
          _ = (4 * (1 - x)) ^ (-1 / 2 : ℝ) := by
            congr 1
            norm_num
          _ = 4 ^ (-1 / 2 : ℝ) * (1 - x) ^ (-1 / 2 : ℝ) := by
            rw [Real.mul_rpow (by norm_num) (by linarith)]
      unfold intervalGreenWeight intervalGreenMajorant
      rw [← hpow]
      have hnonneg : 0 ≤ 4 ^ (-1 / 2 : ℝ) * x ^ (-1 / 2 : ℝ) := by positivity
      linarith

theorem integrable_intervalGreenWeight :
    Integrable (intervalGreenWeight) (volume.restrict (Set.Ioc 0 1)) := by
  have hpowOn : IntegrableOn (fun x : ℝ => x ^ (-1 / 2 : ℝ)) (Set.Ioo 0 1) volume := by
    apply (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (1 : ℝ) > 0)).2
    norm_num
  have hmirrorOn : IntegrableOn (fun x : ℝ => (1 - x) ^ (-1 / 2 : ℝ))
      (Set.Ioo 0 1) volume := by
    have h := intervalIntegrable_one_sub_rpow_half
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
    exact h
  have hmajorant : IntegrableOn intervalGreenMajorant (Set.Ioo 0 1) volume := by
    unfold intervalGreenMajorant
    exact (hpowOn.const_mul _).add (hmirrorOn.const_mul _)
  have hmajorant' : Integrable intervalGreenMajorant (volume.restrict (Set.Ioo 0 1)) :=
    hmajorant.integrable
  have hcont : ContinuousOn intervalGreenWeight (Set.Ioo 0 1) := by
    apply (by fun_prop [chordSq] : ContinuousOn chordSq (Set.Ioo 0 1)).rpow_const
    intro x hx
    left
    rw [chordSq_eq]
    have harg : Real.pi * x ∈ Set.Ioo 0 Real.pi := by
      constructor <;> nlinarith [Real.pi_pos, hx.1, hx.2]
    have hs : 0 < Real.sin (Real.pi * x) := Real.sin_pos_of_mem_Ioo harg
    exact ne_of_gt (mul_pos (by norm_num) (sq_pos_of_pos hs))
  have hweight' : Integrable intervalGreenWeight (volume.restrict (Set.Ioo 0 1)) := by
    apply hmajorant'.mono'
    · exact hcont.aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hbound := intervalGreenWeight_le_majorant ⟨hx.1, le_of_lt hx.2⟩
      have hnonneg : 0 ≤ intervalGreenWeight x := by
        unfold intervalGreenWeight
        apply Real.rpow_nonneg
        unfold chordSq
        exact Complex.normSq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact hbound
  have hweightOn : IntegrableOn intervalGreenWeight (Set.Ioo 0 1) volume := by
    exact hweight'
  have hweightIoc : IntegrableOn intervalGreenWeight (Set.Ioc 0 1) volume := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hweightOn
  exact hweightIoc.integrable

theorem volume_singleton_zero :
    (volume : Measure (AddCircle (1 : ℝ))) {(0 : AddCircle (1 : ℝ))} = 0 := by
  by_contra hzero
  have hpos : 0 < (volume : Measure (AddCircle (1 : ℝ))) {0} :=
    lt_of_le_of_ne bot_le (Ne.symm hzero)
  have hle : (volume : Measure (AddCircle (1 : ℝ))) {0} ≤ 1 := by
    calc
      _ ≤ volume Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := by simp
  have hrealpos : 0 < ((volume : Measure (AddCircle (1 : ℝ))) {0}).toReal :=
    ENNReal.toReal_pos hzero (by finiteness)
  have hreal_le : ((volume : Measure (AddCircle (1 : ℝ))) {0}).toReal ≤ 1 := by
    have h := ENNReal.toReal_mono (by norm_num : (1 : ENNReal) ≠ ⊤) hle
    simpa using h
  let r := ((volume : Measure (AddCircle (1 : ℝ))) {0}).toReal / 4
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrnonneg : 0 ≤ r := le_of_lt hrpos
  have hrhalf : r < 1 / 2 := by dsimp [r]; linarith
  have hsubset : ({(0 : AddCircle (1 : ℝ))} : Set (AddCircle (1 : ℝ))) ⊆
      Metric.closedBall 0 r := by
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    simp [Metric.mem_closedBall, hrnonneg]
  have hball : (volume : Measure (AddCircle (1 : ℝ))) {0} ≤
      (volume : Measure (AddCircle (1 : ℝ))) (Metric.closedBall 0 r) := measure_mono hsubset
  rw [AddCircle.volume_closedBall (T := (1 : ℝ)) (x := 0) r,
    min_eq_right (by linarith : 2 * r ≤ (1 : ℝ))] at hball
  have hballReal := ENNReal.toReal_mono (by finiteness) hball
  have hcontr : ((volume : Measure (AddCircle (1 : ℝ))) {0}).toReal ≤ 2 * r := by
    have hr : 0 ≤ 2 * r := by positivity
    rw [ENNReal.toReal_ofReal hr] at hballReal
    exact hballReal
  dsimp [r] at hcontr
  linarith

def circleGreenWeight (t : AddCircle (1 : ℝ)) : ℝ :=
  Complex.normSq (1 - fourier 1 t) ^ (-1 / 4 : ℝ)

theorem integrable_circleGreenWeight :
    Integrable circleGreenWeight AddCircle.haarAddCircle := by
  have hbase : Continuous (fun t : AddCircle (1 : ℝ) =>
      Complex.normSq (1 - fourier 1 t)) := by
    fun_prop
  have hcont : ContinuousOn circleGreenWeight ({(0 : AddCircle (1 : ℝ))}ᶜ) := by
    apply hbase.continuousOn.rpow_const
    intro t ht
    left
    have hz : Complex.normSq (1 - fourier 1 t) ≠ 0 := by
      intro hz
      have hsub : (1 : ℂ) - fourier 1 t = 0 := Complex.normSq_eq_zero.mp hz
      have hfourier : fourier 1 t = 1 := (sub_eq_zero.mp hsub).symm
      have hcircleCoe : (AddCircle.toCircle t : ℂ) =
          (AddCircle.toCircle (0 : AddCircle (1 : ℝ)) : ℂ) := by
        simpa [fourier_one] using hfourier
      have hcircle : AddCircle.toCircle t = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) :=
        Circle.coe_inj.mp hcircleCoe
      have ht0 : t = 0 := AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0) hcircle
      exact ht (by simp [ht0])
    exact hz
  have hmeas : Measurable circleGreenWeight :=
    measurable_of_continuousOn_compl_singleton (0 : AddCircle (1 : ℝ)) hcont
  have hmap := AddCircle.measurePreserving_mk (T := (1 : ℝ)) (t := 0)
  have hmapEq : Measure.map ((↑) : ℝ → AddCircle (1 : ℝ))
      (volume.restrict (Set.Ioc 0 1)) = volume := by
    simpa only [zero_add] using hmap.map_eq
  have hcomp : (fun x : ℝ => circleGreenWeight (x : AddCircle (1 : ℝ))) =
      intervalGreenWeight := by
    funext x
    rfl
  have hmeasMap : AEStronglyMeasurable circleGreenWeight
      (Measure.map ((↑) : ℝ → AddCircle (1 : ℝ))
        (volume.restrict (Set.Ioc 0 1))) := by
    rw [hmapEq]
    exact hmeas.aestronglyMeasurable
  have hvol : Integrable circleGreenWeight
      (Measure.map ((↑) : ℝ → AddCircle (1 : ℝ))
        (volume.restrict (Set.Ioc 0 1))) := by
    apply (integrable_map_measure hmeasMap hmap.measurable.aemeasurable).2
    change Integrable (fun x : ℝ => circleGreenWeight (x : AddCircle (1 : ℝ)))
      (volume.restrict (Set.Ioc 0 1))
    rw [hcomp]
    exact integrable_intervalGreenWeight
  have hvol' : Integrable circleGreenWeight (volume : Measure (AddCircle (1 : ℝ))) := by
    simpa [hmapEq] using hvol
  have hmeasure : (volume : Measure (AddCircle (1 : ℝ))) = AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  rw [hmeasure] at hvol'
  exact hvol'

def circleGreenMajorant (t : AddCircle (1 : ℝ)) : ℝ :=
  1 + circleGreenWeight t

theorem integrable_circleGreenMajorant :
    Integrable circleGreenMajorant AddCircle.haarAddCircle := by
  unfold circleGreenMajorant
  exact (integrable_const (1 : ℝ)).add integrable_circleGreenWeight

theorem haar_singleton_zero :
    (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) {0} = 0 := by
  have hvol := volume_singleton_zero
  have hmeasure := AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))
  have h : (volume : Measure (AddCircle (1 : ℝ))) {(0 : AddCircle (1 : ℝ))} =
      (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) {0} := by
    simpa using congrArg (fun μ : Measure (AddCircle (1 : ℝ)) =>
      μ {(0 : AddCircle (1 : ℝ))}) hmeasure
  rw [hvol] at h
  exact h.symm


theorem integrable_circleGreenMajorant_prod3 :
    Integrable
      (fun k : AddCircle (1 : ℝ) × (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) =>
        circleGreenMajorant k.1 *
          (circleGreenMajorant k.2.1 * circleGreenMajorant k.2.2))
      (AddCircle.haarAddCircle.prod
        (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle)) := by
  exact integrable_circleGreenMajorant.mul_prod
    (integrable_circleGreenMajorant.mul_prod integrable_circleGreenMajorant)

theorem integrable_fourierGreenMajorant :
    Integrable
      (fun k : Torus4 => circleGreenMajorant k.1 *
        (circleGreenMajorant k.2.1 *
          (circleGreenMajorant k.2.2.1 * circleGreenMajorant k.2.2.2)))
      torus4Haar := by
  exact integrable_circleGreenMajorant.mul_prod integrable_circleGreenMajorant_prod3

theorem ae_torus4Coord_ne_zero (i : Fin 4) :
    ∀ᵐ k : Torus4 ∂torus4Haar, torus4Coord k i ≠ 0 := by
  fin_cases i
  · change ∀ᵐ k : Torus4 ∂torus4Haar, k.1 ≠ 0
    rw [ae_iff]
    have hs : {k : Torus4 | ¬ k.1 ≠ 0} =
        ({(0 : AddCircle (1 : ℝ))} ×ˢ Set.univ) := by
      ext k
      simp
    rw [hs, torus4Haar, Measure.prod_prod]
    simp [haar_singleton_zero]
  · change ∀ᵐ k : Torus4 ∂torus4Haar, k.2.1 ≠ 0
    rw [ae_iff]
    have hs : {k : Torus4 | ¬ k.2.1 ≠ 0} =
        (Set.univ ×ˢ ({(0 : AddCircle (1 : ℝ))} ×ˢ Set.univ)) := by
      ext k
      simp
    rw [hs, torus4Haar, Measure.prod_prod, Measure.prod_prod]
    simp [haar_singleton_zero]
  · change ∀ᵐ k : Torus4 ∂torus4Haar, k.2.2.1 ≠ 0
    rw [ae_iff]
    have hs : {k : Torus4 | ¬ k.2.2.1 ≠ 0} =
        (Set.univ ×ˢ (Set.univ ×ˢ ({(0 : AddCircle (1 : ℝ))} ×ˢ Set.univ))) := by
      ext k
      simp
    rw [hs, torus4Haar, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
    simp [haar_singleton_zero]
  · simpa [torus4Coord] using (show ∀ᵐ k : Torus4 ∂torus4Haar, k.2.2.2 ≠ 0 from by
      rw [ae_iff]
      have hs : {k : Torus4 | ¬ k.2.2.2 ≠ 0} =
          (Set.univ ×ˢ (Set.univ ×ˢ (Set.univ ×ˢ {(0 : AddCircle (1 : ℝ))}))) := by
        ext k
        simp
      rw [hs, torus4Haar, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
      simp [haar_singleton_zero])

@[fun_prop] private theorem continuous_fourier_char (n : ℤ) :
    Continuous (fun t : AddCircle (1 : ℝ) => fourier n t) := map_continuous (fourier n)


private theorem measurable_torus4Coord (i : Fin 4) :
    Measurable (fun k : Torus4 => torus4Coord k i) := by
  fin_cases i <;> simp [torus4Coord] <;> fun_prop

private theorem measurable_fourier_char (n : ℤ) :
    Measurable (fun t : AddCircle (1 : ℝ) => fourier n t) :=
  (continuous_fourier_char n).measurable


private theorem measurable_latticeCharacter (x : LatticePoint) :
    Measurable (latticeCharacter x) := by
  unfold latticeCharacter
  have h0 : Measurable (fun k : Torus4 => fourier (-x.1) k.1) := by
    exact (measurable_fourier_char _).comp measurable_fst
  have h1 : Measurable (fun k : Torus4 => fourier (-x.2.1) k.2.1) := by
    exact (measurable_fourier_char _).comp (measurable_fst.comp measurable_snd)
  have h2 : Measurable (fun k : Torus4 => fourier (-x.2.2.1) k.2.2.1) := by
    exact (measurable_fourier_char _).comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have h3 : Measurable (fun k : Torus4 => fourier (-x.2.2.2) k.2.2.2) := by
    exact (measurable_fourier_char _).comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
  exact h0.mul (h1.mul (h2.mul h3))

private theorem measurable_globalLinkFourierComponent
    (μ : GlobalLinkField) (i : Fin 4) :
    Measurable (globalLinkFourierComponent μ i) := by
  classical
  unfold globalLinkFourierComponent
  apply Finset.measurable_sum
  intro c hc
  exact measurable_const.mul (measurable_latticeCharacter (latticeCellPoint c))

private theorem measurable_fourierLaplacianSymbol :
    Measurable fourierLaplacianSymbol := by
  unfold fourierLaplacianSymbol
  apply Finset.measurable_sum
  intro i hi
  have hc : Measurable (fun k : Torus4 =>
      fourier 1 (torus4Coord k i)) :=
    (measurable_fourier_char 1).comp (measurable_torus4Coord i)
  have hsub : Measurable (fun k : Torus4 =>
      (1 : ℂ) - fourier 1 (torus4Coord k i)) := measurable_const.sub hc
  simpa [Complex.normSq_eq_norm_sq] using hsub.norm.pow_const 2

private theorem fourier_one_sub_ne_zero {t : AddCircle (1 : ℝ)} (ht : t ≠ 0) :
    (1 : ℂ) - fourier 1 t ≠ 0 := by
  intro hz
  have hfourier : fourier 1 t = 1 := (sub_eq_zero.mp hz).symm
  have hcircleCoe : (AddCircle.toCircle t : ℂ) =
      (AddCircle.toCircle (0 : AddCircle (1 : ℝ)) : ℂ) := by
    simpa [fourier_one] using hfourier
  have hcircle : AddCircle.toCircle t = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) :=
    Circle.coe_inj.mp hcircleCoe
  have ht0 : t = 0 := AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0) hcircle
  exact ht ht0

private theorem four_positive_rpow_inverse_bound {a₀ a₁ a₂ a₃ : ℝ}
    (h₀ : 0 < a₀) (h₁ : 0 < a₁) (h₂ : 0 < a₂) (h₃ : 0 < a₃) :
    (a₀ + a₁ + a₂ + a₃)⁻¹ ≤
      a₀ ^ (-1 / 4 : ℝ) * a₁ ^ (-1 / 4 : ℝ) *
        a₂ ^ (-1 / 4 : ℝ) * a₃ ^ (-1 / 4 : ℝ) := by
  let r₀ := a₀ ^ (1 / 4 : ℝ)
  let r₁ := a₁ ^ (1 / 4 : ℝ)
  let r₂ := a₂ ^ (1 / 4 : ℝ)
  let r₃ := a₃ ^ (1 / 4 : ℝ)
  have hr₀ : 0 < r₀ := by dsimp [r₀]; positivity
  have hr₁ : 0 < r₁ := by dsimp [r₁]; positivity
  have hr₂ : 0 < r₂ := by dsimp [r₂]; positivity
  have hr₃ : 0 < r₃ := by dsimp [r₃]; positivity
  have hamg := Real.geom_mean_le_arith_mean4_weighted
    (by norm_num : 0 ≤ (1 / 4 : ℝ)) (by norm_num : 0 ≤ (1 / 4 : ℝ))
    (by norm_num : 0 ≤ (1 / 4 : ℝ)) (by norm_num : 0 ≤ (1 / 4 : ℝ))
    h₀.le h₁.le h₂.le h₃.le
    (by norm_num : (1 / 4 : ℝ) + 1 / 4 + 1 / 4 + 1 / 4 = 1)
  have hamg' : r₀ * r₁ * r₂ * r₃ ≤ (a₀ + a₁ + a₂ + a₃) / 4 := by
    calc
      _ ≤ 1 / 4 * a₀ + 1 / 4 * a₁ + 1 / 4 * a₂ + 1 / 4 * a₃ := by
        simpa [r₀, r₁, r₂, r₃] using hamg
      _ = (a₀ + a₁ + a₂ + a₃) / 4 := by ring
  have hprod : 0 < r₀ * r₁ * r₂ * r₃ := by positivity
  have hsum : 0 < a₀ + a₁ + a₂ + a₃ := by positivity
  have hscale : 4 * (r₀ * r₁ * r₂ * r₃) ≤ a₀ + a₁ + a₂ + a₃ := by
    nlinarith
  have hinv₁ : (a₀ + a₁ + a₂ + a₃)⁻¹ ≤ (4 * (r₀ * r₁ * r₂ * r₃))⁻¹ := by
    exact (inv_le_inv₀ hsum (by positivity)).2 hscale
  have hinv₂ : (4 * (r₀ * r₁ * r₂ * r₃))⁻¹ ≤
      (r₀ * r₁ * r₂ * r₃)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hprod
      (show r₀ * r₁ * r₂ * r₃ ≤ 4 * (r₀ * r₁ * r₂ * r₃) by nlinarith)
  have hweights :
      a₀ ^ (-1 / 4 : ℝ) * a₁ ^ (-1 / 4 : ℝ) *
        a₂ ^ (-1 / 4 : ℝ) * a₃ ^ (-1 / 4 : ℝ) =
        (r₀ * r₁ * r₂ * r₃)⁻¹ := by
    simp only [r₀, r₁, r₂, r₃]
    rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring]
    rw [Real.rpow_neg h₀.le, Real.rpow_neg h₁.le,
      Real.rpow_neg h₂.le, Real.rpow_neg h₃.le]
    field_simp [ne_of_gt hr₀, ne_of_gt hr₁, ne_of_gt hr₂, ne_of_gt hr₃]
  rw [hweights]
  exact hinv₁.trans hinv₂

private theorem exists_oneComponentFourier_bound (μ : GlobalLinkField) (i : Fin 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, ‖globalLinkFourierComponent μ i k‖ ≤ C := by
  let f : Torus4 → ℝ := fun k => ‖globalLinkFourierComponent μ i k‖
  have hf : Continuous f := by
    dsimp [f, globalLinkFourierComponent]
    fun_prop [latticeCharacter]
  have hcompact : IsCompact (Set.range f) := by
    simpa using isCompact_univ.image hf
  rcases hcompact.bddAbove with ⟨C, hC⟩
  change ∀ b ∈ Set.range f, b ≤ C at hC
  refine ⟨C, ?_, ?_⟩
  · have hmem : f 0 ∈ Set.range f := ⟨0, rfl⟩
    exact (norm_nonneg _).trans (hC _ hmem)
  · intro k
    exact hC _ ⟨k, rfl⟩

private theorem exists_globalLinkFourier_bound (μ : GlobalLinkField) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i k, ‖globalLinkFourierComponent μ i k‖ ≤ C := by
  classical
  let b : Fin 4 → ℝ := fun i => Classical.choose (exists_oneComponentFourier_bound μ i)
  have hbnonneg (i : Fin 4) : 0 ≤ b i := (Classical.choose_spec
    (exists_oneComponentFourier_bound μ i)).1
  have hb (i : Fin 4) (k : Torus4) :
      ‖globalLinkFourierComponent μ i k‖ ≤ b i := (Classical.choose_spec
        (exists_oneComponentFourier_bound μ i)).2 k
  refine ⟨∑ i : Fin 4, b i, Finset.sum_nonneg (fun i hi => hbnonneg i), ?_⟩
  intro i k
  exact (hb i k).trans (Finset.single_le_sum (fun j hj => hbnonneg j) (Finset.mem_univ i))

private theorem fourierGreenDensity_le_prod_majorant (μ : GlobalLinkField) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : Torus4,
      (∀ i : Fin 4, torus4Coord k i ≠ 0) →
      fourierGreenDensity μ k ≤
        C * (circleGreenMajorant k.1 *
          (circleGreenMajorant k.2.1 *
            (circleGreenMajorant k.2.2.1 * circleGreenMajorant k.2.2.2))) := by
  obtain ⟨B, hBnonneg, hB⟩ := exists_globalLinkFourier_bound μ
  refine ⟨4 * B ^ 2, by positivity, ?_⟩
  intro k hcoord
  let a₀ : ℝ := Complex.normSq (1 - fourier 1 k.1)
  let a₁ : ℝ := Complex.normSq (1 - fourier 1 k.2.1)
  let a₂ : ℝ := Complex.normSq (1 - fourier 1 k.2.2.1)
  let a₃ : ℝ := Complex.normSq (1 - fourier 1 k.2.2.2)
  have ha₀ : 0 < a₀ := by
    dsimp [a₀]
    exact Complex.normSq_pos.mpr (fourier_one_sub_ne_zero (hcoord 0))
  have ha₁ : 0 < a₁ := by
    dsimp [a₁]
    exact Complex.normSq_pos.mpr (fourier_one_sub_ne_zero (hcoord 1))
  have ha₂ : 0 < a₂ := by
    dsimp [a₂]
    exact Complex.normSq_pos.mpr (fourier_one_sub_ne_zero (hcoord 2))
  have ha₃ : 0 < a₃ := by
    dsimp [a₃]
    exact Complex.normSq_pos.mpr (fourier_one_sub_ne_zero (hcoord 3))
  have hsymbol : fourierLaplacianSymbol k = a₀ + a₁ + a₂ + a₃ := by
    simp [fourierLaplacianSymbol, a₀, a₁, a₂, a₃, torus4Coord,
      Complex.sq_norm, Fin.sum_univ_succ]
    ring
  have hsymbolpos : 0 < fourierLaplacianSymbol k := by
    rw [hsymbol]
    positivity
  have hinv := four_positive_rpow_inverse_bound ha₀ ha₁ ha₂ ha₃
  have hw₀ : circleGreenWeight k.1 = a₀ ^ (-1 / 4 : ℝ) := rfl
  have hw₁ : circleGreenWeight k.2.1 = a₁ ^ (-1 / 4 : ℝ) := rfl
  have hw₂ : circleGreenWeight k.2.2.1 = a₂ ^ (-1 / 4 : ℝ) := rfl
  have hw₃ : circleGreenWeight k.2.2.2 = a₃ ^ (-1 / 4 : ℝ) := rfl
  have hinv' : (fourierLaplacianSymbol k)⁻¹ ≤
      circleGreenWeight k.1 * (circleGreenWeight k.2.1 *
        (circleGreenWeight k.2.2.1 * circleGreenWeight k.2.2.2)) := by
    rw [hsymbol, hw₀, hw₁, hw₂, hw₃]
    simpa only [mul_assoc] using hinv
  have hw₀nonneg : 0 ≤ circleGreenWeight k.1 := by
    unfold circleGreenWeight
    exact Real.rpow_nonneg (Complex.normSq_nonneg _) _
  have hw₁nonneg : 0 ≤ circleGreenWeight k.2.1 := by
    unfold circleGreenWeight
    exact Real.rpow_nonneg (Complex.normSq_nonneg _) _
  have hw₂nonneg : 0 ≤ circleGreenWeight k.2.2.1 := by
    unfold circleGreenWeight
    exact Real.rpow_nonneg (Complex.normSq_nonneg _) _
  have hw₃nonneg : 0 ≤ circleGreenWeight k.2.2.2 := by
    unfold circleGreenWeight
    exact Real.rpow_nonneg (Complex.normSq_nonneg _) _
  have hmaj : circleGreenWeight k.1 * (circleGreenWeight k.2.1 *
      (circleGreenWeight k.2.2.1 * circleGreenWeight k.2.2.2)) ≤
      circleGreenMajorant k.1 * (circleGreenMajorant k.2.1 *
        (circleGreenMajorant k.2.2.1 * circleGreenMajorant k.2.2.2)) := by
    unfold circleGreenMajorant
    gcongr <;> linarith
  have hnum (i : Fin 4) :
      ‖globalLinkFourierComponent μ i k‖ ^ 2 ≤ B ^ 2 := by
    have hb := hB i k
    have hn : 0 ≤ ‖globalLinkFourierComponent μ i k‖ := norm_nonneg _
    have hplus : 0 ≤ B + ‖globalLinkFourierComponent μ i k‖ := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) hplus]
  have hterm (i : Fin 4) :
      ‖globalLinkFourierComponent μ i k‖ ^ 2 /
          fourierLaplacianSymbol k ≤ B ^ 2 * (fourierLaplacianSymbol k)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hnum i) (inv_nonneg.mpr hsymbolpos.le)
  have hsum : fourierGreenDensity μ k ≤ 4 * B ^ 2 *
      (fourierLaplacianSymbol k)⁻¹ := by
    unfold fourierGreenDensity
    calc
      _ ≤ ∑ i : Fin 4, B ^ 2 * (fourierLaplacianSymbol k)⁻¹ :=
        Finset.sum_le_sum fun i hi => hterm i
      _ = 4 * B ^ 2 * (fourierLaplacianSymbol k)⁻¹ := by simp [Finset.sum_const, mul_assoc]
  calc
    fourierGreenDensity μ k ≤ 4 * B ^ 2 * (fourierLaplacianSymbol k)⁻¹ := hsum
    _ ≤ 4 * B ^ 2 *
        (circleGreenWeight k.1 * (circleGreenWeight k.2.1 *
          (circleGreenWeight k.2.2.1 * circleGreenWeight k.2.2.2))) := by
      gcongr
    _ ≤ 4 * B ^ 2 *
        (circleGreenMajorant k.1 * (circleGreenMajorant k.2.1 *
          (circleGreenMajorant k.2.2.1 * circleGreenMajorant k.2.2.2))) := by
      gcongr

theorem integrable_fourierGreenDensity (μ : GlobalLinkField) :
    Integrable (fourierGreenDensity μ) torus4Haar := by
  obtain ⟨C, hC, hbound⟩ := fourierGreenDensity_le_prod_majorant μ
  have hmajorant : Integrable
      (fun k : Torus4 => C * (circleGreenMajorant k.1 *
        (circleGreenMajorant k.2.1 *
          (circleGreenMajorant k.2.2.1 * circleGreenMajorant k.2.2.2))))
      torus4Haar := (integrable_fourierGreenMajorant.const_mul C)
  have hmeas : AEStronglyMeasurable (fourierGreenDensity μ) torus4Haar := by
    have hs : Measurable fourierLaplacianSymbol := measurable_fourierLaplacianSymbol
    have hterm (i : Fin 4) : Measurable (fun k : Torus4 =>
        ‖globalLinkFourierComponent μ i k‖ ^ 2 /
          fourierLaplacianSymbol k) := by
      exact ((measurable_globalLinkFourierComponent μ i).norm.pow_const 2).div hs
    unfold fourierGreenDensity
    exact (Finset.measurable_sum Finset.univ (fun i hi => hterm i)).aestronglyMeasurable
  apply hmajorant.mono' hmeas
  filter_upwards [ae_torus4Coord_ne_zero 0, ae_torus4Coord_ne_zero 1,
    ae_torus4Coord_ne_zero 2, ae_torus4Coord_ne_zero 3] with k hk₀ hk₁ hk₂ hk₃
  have h := hbound k (by intro i; fin_cases i <;> assumption)
  have hnonneg : 0 ≤ fourierGreenDensity μ k := fourierGreenDensity_nonneg μ k
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact h

end FroehlichSpencer.FS82.Infinite.Fourier
