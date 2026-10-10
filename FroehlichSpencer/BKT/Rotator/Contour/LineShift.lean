/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Order.Compact

/-!
# Shifting a horizontal line of integration

If `f` is complex differentiable on the closed strip `|Im z| ≤ |t|` and its restrictions to the
horizontal lines `Im z = y`, `|y| ≤ |t|`, are dominated by one integrable function `B` of the real
part that tends to zero at infinity, then `∫ f(x) dx = ∫ f(x + it) dx`. The proof applies Cauchy's
theorem on the rectangles `[-T, T] × [0, t]`; the vertical sides are at most `|t| B(±T) → 0`.
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Contour

open Complex MeasureTheory Filter Topology Set
open scoped Interval

lemma abs_im_ofReal_add_mul_I_eq (x y : ℝ) : |((x : ℂ) + y * I).im| = |y| := by simp

/-- Each horizontal line inside the strip is integrable. -/
theorem integrable_comp_add_mul_I {f : ℂ → ℂ} {t y : ℝ} {B : ℝ → ℝ}
    (hf : ∀ z : ℂ, |z.im| ≤ |t| → DifferentiableAt ℂ f z) (hB : Integrable B)
    (hdom : ∀ x y : ℝ, |y| ≤ |t| → ‖f (x + y * I)‖ ≤ B x) (hy : |y| ≤ |t|) :
    Integrable fun x : ℝ => f (x + y * I) := by
  have hcont : Continuous fun x : ℝ => f (x + y * I) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have hd := hf ((x : ℂ) + y * I) (by rw [abs_im_ofReal_add_mul_I_eq]; exact hy)
    have hc : Continuous fun x : ℝ => (x : ℂ) + y * I :=
      Complex.continuous_ofReal.add continuous_const
    exact ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + y * I) hd.continuousAt hc.continuousAt
  exact hB.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun x => hdom x y hy)

lemma norm_verticalIntegral_le {f : ℂ → ℂ} {t : ℝ} {B : ℝ → ℝ}
    (hdom : ∀ x y : ℝ, |y| ≤ |t| → ‖f (x + y * I)‖ ≤ B x) (T : ℝ) :
    ‖∫ y : ℝ in (0 : ℝ)..t, f (T + y * I)‖ ≤ B T * |t - 0| := by
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => hdom T y ?_
  rcases le_total 0 t with h | h
  · rw [uIoc_of_le h] at hy
    rw [abs_of_pos hy.1, abs_of_nonneg h]; exact hy.2
  · rw [uIoc_of_ge h] at hy
    rw [abs_of_nonpos hy.2, abs_of_nonpos h]; linarith [hy.1]

lemma tendsto_verticalIntegral {f : ℂ → ℂ} {t : ℝ} {B : ℝ → ℝ}
    (hBlim : Tendsto B (cocompact ℝ) (𝓝 0))
    (hdom : ∀ x y : ℝ, |y| ≤ |t| → ‖f (x + y * I)‖ ≤ B x) {g : ℝ → ℝ}
    (hg : Tendsto g atTop (cocompact ℝ)) :
    Tendsto (fun T : ℝ => ∫ y : ℝ in (0 : ℝ)..t, f (g T + y * I)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hB : Tendsto (fun T => B (g T) * |t - 0|) atTop (𝓝 0) := by
    simpa using (hBlim.comp hg).mul_const |t - 0|
  refine squeeze_zero (fun _ => norm_nonneg _) (fun T => ?_) hB
  exact norm_verticalIntegral_le hdom (g T)

/-- Shifting a horizontal line of integration across a strip of holomorphy, under an integrable
majorant in the real part that vanishes at infinity. -/
theorem integral_eq_integral_add_mul_I {f : ℂ → ℂ} {t : ℝ} {B : ℝ → ℝ}
    (hf : ∀ z : ℂ, |z.im| ≤ |t| → DifferentiableAt ℂ f z)
    (hB : MeasureTheory.Integrable B) (hBlim : Filter.Tendsto B (Filter.cocompact ℝ) (nhds 0))
    (hdom : ∀ x y : ℝ, |y| ≤ |t| → ‖f (x + y * Complex.I)‖ ≤ B x) :
    ∫ x : ℝ, f x = ∫ x : ℝ, f (x + t * Complex.I) := by
  have hi0 : Integrable fun x : ℝ => f (x + (0 : ℝ) * I) :=
    integrable_comp_add_mul_I hf hB hdom (by simp)
  have hit : Integrable fun x : ℝ => f (x + t * I) :=
    integrable_comp_add_mul_I hf hB hdom le_rfl
  have hrect : ∀ T : ℝ,
      (∫ x : ℝ in (-T)..T, f (x + t * I)) =
        (∫ x : ℝ in (-T)..T, f x) + I * (∫ y : ℝ in (0 : ℝ)..t, f (T + y * I)) -
          I * (∫ y : ℝ in (0 : ℝ)..t, f (-T + y * I)) := by
    intro T
    have hD : DifferentiableOn ℂ f ([[(-T : ℂ).re, ((T : ℂ) + t * I).re]] ×ℂ
        [[(-T : ℂ).im, ((T : ℂ) + t * I).im]]) := by
      intro z hz
      refine (hf z ?_).differentiableWithinAt
      have him : z.im ∈ [[(0 : ℝ), t]] := by
        have := hz.2
        simpa using this
      rcases le_total 0 t with h | h
      · rw [uIcc_of_le h] at him
        rw [abs_of_nonneg him.1, abs_of_nonneg h]; exact him.2
      · rw [uIcc_of_ge h] at him
        rw [abs_of_nonpos him.2, abs_of_nonpos h]; linarith [him.1]
    have h := integral_boundary_rect_eq_zero_of_differentiableOn f (-T : ℂ) ((T : ℂ) + t * I) hD
    simp only [neg_re, ofReal_re, neg_im, ofReal_im, neg_zero, add_re, mul_re, I_re, mul_zero,
      I_im, mul_one, sub_zero, add_zero, add_im, mul_im, zero_add, ofReal_zero, zero_mul,
      smul_eq_mul, ofReal_neg] at h
    linear_combination -h
  have hlimL : Tendsto (fun T : ℝ => ∫ x : ℝ in (-T)..T, f (x + t * I)) atTop
      (𝓝 (∫ x : ℝ, f (x + t * I))) :=
    intervalIntegral_tendsto_integral hit tendsto_neg_atTop_atBot tendsto_id
  have hi0' : Integrable fun x : ℝ => f x := by simpa using hi0
  have hlim0 : Tendsto (fun T : ℝ => ∫ x : ℝ in (-T)..T, f x) atTop (𝓝 (∫ x : ℝ, f x)) :=
    intervalIntegral_tendsto_integral hi0' tendsto_neg_atTop_atBot tendsto_id
  have hV1 := tendsto_verticalIntegral hBlim hdom (g := id) (tendsto_id.mono_right atTop_le_cocompact)
  have hV2 := tendsto_verticalIntegral hBlim hdom (g := fun T => -T)
    (tendsto_neg_atTop_atBot.mono_right atBot_le_cocompact)
  have hlimR : Tendsto (fun T : ℝ => (∫ x : ℝ in (-T)..T, f x) +
      I * (∫ y : ℝ in (0 : ℝ)..t, f (T + y * I)) - I * (∫ y : ℝ in (0 : ℝ)..t, f (-T + y * I)))
      atTop (𝓝 ((∫ x : ℝ, f x) + I * 0 - I * 0)) := by
    have h1 := hV1
    have h2 := hV2
    simp only [id, ofReal_neg] at h1 h2
    exact (hlim0.add (h1.const_mul I)).sub (h2.const_mul I)
  simp only [mul_zero, add_zero, sub_zero] at hlimR
  rw [funext hrect] at hlimL
  exact (tendsto_nhds_unique hlimR hlimL)
end FroehlichSpencer.BKT.Rotator.Contour
