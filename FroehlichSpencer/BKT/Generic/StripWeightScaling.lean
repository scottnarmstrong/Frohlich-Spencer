/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.StripWeight
public import FroehlichSpencer.BKT.Generic.GaussianInstance
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Rescaled strip weights and the Gaussian strip weight (generic core)

* `IsStripWeight.comp_div`: rescaling the argument by a period `p > 0`.

This is the charge-scale
  adapter of the FS81 §6 rotator (`ψ = 2π h`, J p. 576): the integer dual heights of FS81 (6.5)
  become fields of period `2π`, and the Appendix B weight `I_β(h)` becomes `I_β(ψ / 2π)`, with
  strip width `2π W` and cost `c(u / 2π)`.
* `isStripWeight_gaussianWeight`: the KP Gaussian bond weight `w(z) = e^{-βz²/2}`
  (`Generic/GaussianInstance.lean`) is a strip weight of every width, with cost `βu²/2`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex Filter Topology

/-- The point `(t + iu)/p` of the rescaled strip, written in real coordinates. -/
lemma add_mul_I_div_ofReal (t u p : ℝ) :
    ((t : ℂ) + (u : ℂ) * I) / (p : ℂ) = ((t / p : ℝ) : ℂ) + ((u / p : ℝ) : ℂ) * I := by
  push_cast
  ring

/-- Rescaling by the period (`ψ = 2π h`): a strip weight composed with `z ↦ z / p`. -/
theorem IsStripWeight.comp_div {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ} (hw : IsStripWeight w W c)
    {p : ℝ} (hp : 0 < p) :
    IsStripWeight (fun z => w (z / p)) (p * W) (fun u => c (u / p)) := by
  have hp0 : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hstrip : ∀ z : ℂ, |z.im| ≤ p * W → |(z / (p : ℂ)).im| ≤ W := by
    intro z hz
    rw [Complex.div_ofReal_im, abs_div, abs_of_pos hp, div_le_iff₀ hp, mul_comm]
    exact hz
  have hreal : ∀ u : ℝ, |u| ≤ p * W → |u / p| ≤ W := by
    intro u hu
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp, mul_comm]
    exact hu
  have hofReal : ∀ x : ℝ, (x : ℂ) / (p : ℂ) = ((x / p : ℝ) : ℂ) := fun x => by push_cast; rfl
  obtain ⟨M, hM⟩ := hw.bounded
  obtain ⟨B, hBint, hBlim, hB⟩ := hw.majorant
  refine
    { width_nonneg := mul_nonneg hp.le hw.width_nonneg
      ofReal_im := fun x => by
        rw [hofReal]
        exact hw.ofReal_im _
      ofReal_re_pos := fun x => by
        rw [hofReal]
        exact hw.ofReal_re_pos _
      analyticAt := fun z hz => by
        have hf : AnalyticAt ℂ (fun z : ℂ => z / (p : ℂ)) z :=
          analyticAt_id.div_const
        exact AnalyticAt.comp (g := w) (f := fun z : ℂ => z / (p : ℂ))
          (hw.analyticAt (z / (p : ℂ)) (hstrip z hz)) hf
      even := fun z hz => by
        rw [neg_div]
        exact hw.even _ (hstrip z hz)
      conj := fun z hz => by
        rw [hw.conj _ (hstrip z hz), map_div₀, Complex.conj_ofReal]
      ratio_le := fun t u hu => by
        rw [add_mul_I_div_ofReal, hofReal]
        exact hw.ratio_le _ _ (hreal u hu)
      bounded := ⟨M, fun t u hu => by
        rw [add_mul_I_div_ofReal]
        exact hM _ _ (hreal u hu)⟩
      majorant := ⟨fun t => B (t / p), hBint.comp_div hp.ne', ?_, fun t u hu => by
        rw [add_mul_I_div_ofReal]
        exact hB _ _ (hreal u hu)⟩
      cost_even := fun u => by
        rw [neg_div]
        exact hw.cost_even _
      cost_zero := by
        rw [zero_div]
        exact hw.cost_zero }
  have hcomp : Tendsto (fun t : ℝ => t * p⁻¹) (cocompact ℝ) (cocompact ℝ) :=
    (Homeomorph.mulRight₀ p⁻¹ (inv_ne_zero hp.ne')).isClosedEmbedding.tendsto_cocompact
  have := hBlim.comp hcomp
  simpa only [Function.comp_def, div_eq_mul_inv] using this

/-- The exponent of the Gaussian weight at `t + iu`, in real coordinates. -/
lemma gaussian_exponent (β t u : ℝ) :
    -((β / 2 : ℝ) : ℂ) * ((t : ℂ) + (u : ℂ) * I) ^ 2 =
      ((-(β / 2) * (t ^ 2 - u ^ 2) : ℝ) : ℂ) + ((-(β * t * u) : ℝ) : ℂ) * I := by
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `|e^{-β(t+iu)²/2}| = e^{-β(t² - u²)/2}`. -/
lemma norm_gaussianWeight (β t u : ℝ) :
    ‖gaussianWeight β ((t : ℂ) + (u : ℂ) * I)‖ = Real.exp (-(β / 2) * (t ^ 2 - u ^ 2)) := by
  unfold gaussianWeight
  rw [gaussian_exponent, Complex.norm_exp]
  congr 1
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

/-- On the real axis the Gaussian weight is the real number `e^{-βx²/2}`. -/
theorem gaussianWeight_ofReal (β x : ℝ) :
    gaussianWeight β x = ((Real.exp (-(β / 2) * x ^ 2) : ℝ) : ℂ) := by
  unfold gaussianWeight
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The Gaussian weight is a strip weight of every width, with cost `βu²/2`. -/
theorem isStripWeight_gaussianWeight {β : ℝ} (hβ : 0 < β) {W : ℝ} (hW : 0 ≤ W) :
    IsStripWeight (gaussianWeight β) W (fun u => β / 2 * u ^ 2) := by
  have hreal := gaussianWeight_ofReal β
  have hdiff : Differentiable ℂ (gaussianWeight β) := by
    unfold gaussianWeight
    fun_prop
  have hsq : ∀ u : ℝ, |u| ≤ W → u ^ 2 ≤ W ^ 2 := fun u hu => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg u) hu 2
  have hb : 0 < β / 2 := half_pos hβ
  refine
    { width_nonneg := hW
      ofReal_im := fun x => by rw [hreal, Complex.ofReal_im]
      ofReal_re_pos := fun x => by rw [hreal, Complex.ofReal_re]; exact Real.exp_pos _
      analyticAt := fun z _ => hdiff.analyticAt z
      even := fun z _ => by unfold gaussianWeight; rw [neg_sq]
      conj := fun z _ => by
        unfold gaussianWeight
        rw [← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal, map_pow]
      ratio_le := fun t u _ => by
        rw [norm_div, norm_gaussianWeight, show ((t : ℝ) : ℂ) = (t : ℂ) + ((0 : ℝ) : ℂ) * I by
          simp, norm_gaussianWeight, ← Real.exp_sub]
        exact le_of_eq (congrArg Real.exp (by ring))
      bounded := ⟨Real.exp (β / 2 * W ^ 2), fun t u hu => by
        rw [norm_gaussianWeight]
        refine Real.exp_le_exp.mpr ?_
        have := hsq u hu
        nlinarith [sq_nonneg t]⟩
      majorant := ⟨fun t => Real.exp (β / 2 * W ^ 2) * Real.exp (-(β / 2) * t ^ 2),
        (integrable_exp_neg_mul_sq hb).const_mul _, ?_, fun t u hu => by
          show _ ≤ Real.exp _ * Real.exp _
          rw [norm_gaussianWeight, ← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          have := hsq u hu
          nlinarith⟩
      cost_even := fun u => by rw [neg_sq]
      cost_zero := by ring }
  have hsqlim : Tendsto (fun t : ℝ => t ^ 2) (cocompact ℝ) atTop := by
    have h := (tendsto_pow_atTop (two_ne_zero (α := ℕ))).comp
      (tendsto_norm_cocompact_atTop (E := ℝ))
    refine h.congr fun t => ?_
    simp [Real.norm_eq_abs, sq_abs]
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(β / 2) * t ^ 2)) (cocompact ℝ) (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (hsqlim.const_mul_atTop hb))
    refine h.congr fun t => ?_
    simp [Function.comp_def, neg_mul]
  have := hexp.const_mul (Real.exp (β / 2 * W ^ 2))
  rwa [mul_zero] at this

end FroehlichSpencer.BKT.Generic

end
