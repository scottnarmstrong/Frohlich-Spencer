/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Stieltjes.Basic
import Mathlib.Analysis.Analytic.Within
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Basic properties of the Stieltjes transform

For a finite measure `μ` on `ℝ`: integrability of `t ↦ (t - z)⁻¹` for `Im z > 0`, the bound
`‖S_μ z‖ ≤ μ(ℝ) / Im z`, analyticity and continuity on the upper half-plane, a Lipschitz-type
bound, the Poisson identity for `Im S_μ`, linearity in `μ`, and the transform of finite sums of
Dirac masses.
-/

@[expose] public section

open MeasureTheory Complex Set

namespace FroehlichSpencer.Infra

private theorem im_le_norm_ofReal_sub {z : ℂ} (t : ℝ) : |z.im| ≤ ‖(t : ℂ) - z‖ := by
  have := Complex.abs_im_le_norm ((t : ℂ) - z)
  simpa using this

private theorem norm_inv_ofReal_sub_le {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    ‖((t : ℂ) - z)⁻¹‖ ≤ 1 / z.im := by
  rw [norm_inv, one_div]
  apply inv_anti₀ hz
  have := im_le_norm_ofReal_sub (z := z) t
  rwa [abs_of_pos hz] at this

theorem integrable_inv_ofReal_sub (μ : Measure ℝ) [IsFiniteMeasure μ] {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun t : ℝ => ((t : ℂ) - z)⁻¹) μ := by
  refine ⟨(Complex.measurable_ofReal.sub_const z).inv.aestronglyMeasurable, ?_⟩
  exact HasFiniteIntegral.of_bounded (C := 1 / z.im)
    (Filter.Eventually.of_forall (norm_inv_ofReal_sub_le hz))

theorem norm_stieltjes_le (μ : Measure ℝ) [IsFiniteMeasure μ] {z : ℂ} (hz : 0 < z.im) :
    ‖stieltjes μ z‖ ≤ μ.real univ / z.im := by
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun t : ℝ => ((t : ℂ) - z)⁻¹) (C := 1 / z.im)
    (Filter.Eventually.of_forall (norm_inv_ofReal_sub_le hz))
  rw [stieltjes_def]
  calc _ ≤ 1 / z.im * μ.real univ := h
    _ = _ := by ring

theorem analyticOnNhd_stieltjes (μ : Measure ℝ) [IsFiniteMeasure μ] :
    AnalyticOnNhd ℂ (stieltjes μ) {z | 0 < z.im} := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hfun : stieltjes μ = resolventTransform μ :=
    funext (stieltjes_eq_resolventTransform μ)
  rw [← hopen.analyticOn_iff_analyticOnNhd, hfun]
  refine (analyticOn_resolventTransform (μ := μ)).mono ?_
  rintro z hz ⟨x, -, rfl⟩
  have : (0 : ℝ) < ((algebraMap ℝ ℂ) x).im := hz
  simp at this

theorem continuousOn_stieltjes (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ContinuousOn (stieltjes μ) {z | 0 < z.im} :=
  (analyticOnNhd_stieltjes μ).continuousOn

theorem norm_stieltjes_sub_le (μ : Measure ℝ) [IsFiniteMeasure μ] {z w : ℂ} (hz : 0 < z.im)
    (hw : 0 < w.im) :
    ‖stieltjes μ z - stieltjes μ w‖ ≤ μ.real univ * ‖z - w‖ / (z.im * w.im) := by
  have hi := integrable_inv_ofReal_sub μ hz
  have hj := integrable_inv_ofReal_sub μ hw
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun t : ℝ => ((t : ℂ) - z)⁻¹ - ((t : ℂ) - w)⁻¹)
    (C := ‖z - w‖ / (z.im * w.im)) (Filter.Eventually.of_forall fun t => by
      have hz0 : ((t : ℂ) - z) ≠ 0 := fun h => by
        have := congrArg Complex.im h; simp at this; linarith
      have hw0 : ((t : ℂ) - w) ≠ 0 := fun h => by
        have := congrArg Complex.im h; simp at this; linarith
      have e : ((t : ℂ) - z)⁻¹ - ((t : ℂ) - w)⁻¹ =
          (z - w) * (((t : ℂ) - z)⁻¹ * ((t : ℂ) - w)⁻¹) := by
        field_simp
        ring
      rw [e, norm_mul, norm_mul, div_eq_mul_inv]
      gcongr
      have a := norm_inv_ofReal_sub_le hz t
      have b := norm_inv_ofReal_sub_le hw t
      rw [one_div] at a b
      rw [mul_inv]
      exact mul_le_mul a b (norm_nonneg _) (inv_nonneg.2 hz.le))
  rw [stieltjes_def, stieltjes_def, ← integral_sub hi hj]
  calc _ ≤ ‖z - w‖ / (z.im * w.im) * μ.real univ := h
    _ = _ := by ring

theorem im_stieltjes (μ : Measure ℝ) [IsFiniteMeasure μ] (E : ℝ) {η : ℝ} (hη : 0 < η) :
    (stieltjes μ (E + η * I)).im = ∫ t, η / ((t - E) ^ 2 + η ^ 2) ∂μ := by
  have hi := integrable_inv_ofReal_sub μ (z := (E : ℂ) + η * I) (by simpa using hη)
  have h := integral_im (𝕜 := ℂ) hi
  simp only [RCLike.im_to_complex] at h
  rw [stieltjes_def, ← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => im_inv_ofReal_sub t E η)

theorem stieltjes_add (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {z : ℂ}
    (hz : 0 < z.im) : stieltjes (μ + ν) z = stieltjes μ z + stieltjes ν z := by
  simp only [stieltjes_def]
  exact integral_add_measure (integrable_inv_ofReal_sub μ hz) (integrable_inv_ofReal_sub ν hz)

theorem stieltjes_smul (μ : Measure ℝ) (c : NNReal) (z : ℂ) :
    stieltjes (c • μ) z = (c : ℂ) * stieltjes μ z := by
  simp only [stieltjes_def]
  have : c • μ = (c : ENNReal) • μ := rfl
  rw [this, integral_smul_measure]
  simp

theorem stieltjes_dirac (x : ℝ) (z : ℂ) : stieltjes (Measure.dirac x) z = ((x : ℂ) - z)⁻¹ := by
  simp [stieltjes_def, integral_dirac]

theorem stieltjes_sum_dirac {ι : Type*} (s : Finset ι) (x : ι → ℝ) (z : ℂ) :
    stieltjes (∑ i ∈ s, Measure.dirac (x i)) z = ∑ i ∈ s, ((x i : ℂ) - z)⁻¹ := by
  simp only [stieltjes_def]
  rw [integral_finsetSum_measure]
  · simp [integral_dirac]
  · intro i _
    exact integrable_dirac (by simp)

end FroehlichSpencer.Infra
