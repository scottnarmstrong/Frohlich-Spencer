/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.BesselInterp.Properties
import FroehlichSpencer.BKT.Rotator.BesselInterp.Vertical

/-!
# Uniform bounds for the Bessel interpolation on the strip

For `β ≥ 1`, on the closed strip `|Im z| ≤ β/2` the interpolation `I_β` of FS81 Appendix B obeys a
vertical comparison `‖I_β(x + is)‖ ≤ R ‖I_β(x)‖` with a constant `R` depending only on `β`, and
`I_β` decays like `e^{-|x|}` on the real axis. Together these give the uniform strip bound
`‖I_β(x + is)‖ ≤ C e^{-|x|}`, which makes the contour ends vanish and dominates shifted integrands.
These are consequences of the explicit logarithm `ℓ_β + S_β` of `I_β` (property (c) is the
large-`β` refinement with an explicit envelope).
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Contour

open Complex Metric
open scoped Real
open FroehlichSpencer.BKT.Rotator.BesselInterp

/-- `I_β` is complex differentiable on the strip `|Im z| < β`. -/
theorem differentiableAt_besselInterp {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : |z.im| < β) :
    DifferentiableAt ℂ (besselInterp β) z :=
  (hasDerivAt_besselInterp hβ hz).differentiableAt

lemma abs_im_ofReal_add_mul_I (x s : ℝ) : |((x : ℂ) + s * I).im| = |s| := by simp

/-- Real-axis decay `‖I_β(x)‖ ≤ K e^{-|x|}`. -/
theorem exists_norm_besselInterp_ofReal_le {β : ℝ} (hβ : 0 < β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, ‖besselInterp β x‖ ≤ K * Real.exp (-|x|) := by
  obtain ⟨M, -, hM⟩ := exists_abs_logDefect_le hβ
  obtain ⟨K, hK⟩ := exists_debyeRe_le_exp_neg_abs hβ
  have hK0 : 0 ≤ K := by
    have := (debyeRe_pos hβ 0).le.trans (hK 0)
    simpa using this
  refine ⟨K * Real.exp (M * 2 * (3 * latticeSum)), by positivity, fun x => ?_⟩
  have hx : |((x : ℂ)).im| < β := by simpa using hβ
  rw [besselInterp_eq_exp_interpLog hβ hx]
  unfold interpLog
  rw [Complex.exp_add, ← debye_eq_exp_debyeLog hβ hx, norm_mul, debye_ofReal hβ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (debyeRe_pos hβ x), Complex.norm_exp]
  have hS : (defectSeries β x).re ≤ M * 2 * (3 * latticeSum) := by
    have := norm_defectSeries_le hM (x : ℂ)
    simp only [ofReal_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at this
    exact (re_le_norm _).trans this
  calc debyeRe β x * Real.exp (defectSeries β x).re
      ≤ (K * Real.exp (-|x|)) * Real.exp (M * 2 * (3 * latticeSum)) :=
        mul_le_mul (hK x) (Real.exp_le_exp.mpr hS) (Real.exp_pos _).le
          (mul_nonneg hK0 (Real.exp_pos _).le)
    _ = K * Real.exp (M * 2 * (3 * latticeSum)) * Real.exp (-|x|) := by ring

/-- Vertical comparison on the closed strip: `‖I_β(x + is)‖ ≤ R ‖I_β(x)‖` for `|s| ≤ β/2`, with
`R` depending only on `β ≥ 1`. -/
theorem exists_norm_besselInterp_add_le {β : ℝ} (hβ : 1 ≤ β) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x s : ℝ, |s| ≤ β / 2 →
      ‖besselInterp β ((x : ℂ) + s * I)‖ ≤ R * ‖besselInterp β x‖ := by
  have hβ0 : 0 < β := by linarith
  obtain ⟨M, hM0, hM⟩ := exists_abs_logDefect_le hβ0
  set L := latticeSum
  have hL := latticeSum_nonneg
  refine ⟨Real.exp (5 * β + M * 2 * (3 * L) * (Real.exp (π * β) + 1)), (Real.exp_pos _).le,
    fun x s hs => ?_⟩
  have hz1 : |((x : ℂ) + s * I).im| < β := by
    rw [abs_im_ofReal_add_mul_I]; linarith
  have hz0 : |((x : ℂ)).im| < β := by simpa using hβ0
  rw [besselInterp_eq_exp_interpLog hβ0 hz1, besselInterp_eq_exp_interpLog hβ0 hz0,
    Complex.norm_exp, Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hball : ∀ z ∈ closedBall (x : ℂ) |s|, |z.im| ≤ β / 2 := fun z hz => by
    have h := abs_im_le_norm (z - x)
    rw [sub_im, ofReal_im, sub_zero] at h
    exact h.trans ((by rwa [mem_closedBall, dist_eq_norm] at hz : ‖z - x‖ ≤ |s|).trans hs)
  have hstrip : ∀ z ∈ closedBall (x : ℂ) |s|, |z.im| < β :=
    fun z hz => lt_of_le_of_lt (hball z hz) (by linarith)
  have hℓ : (debyeLog β (x + s * I) - debyeLog β x).re ≤ 20 / β * s ^ 2 :=
    re_sub_le_of_hasDerivAt (fun z hz => hasDerivAt_debyeLog hβ0 (hstrip z hz))
      (fun z hz => hasDerivAt_debyeLogDeriv hβ0 (hstrip z hz))
      (fun z hz => norm_debyeLogDeriv2_le hβ (hball z hz)) (debyeLogDeriv_ofReal_im hβ0 x)
  have hs2 : 20 / β * s ^ 2 ≤ 5 * β := by
    have : s ^ 2 ≤ (β / 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg s) hs 2
    rw [div_mul_eq_mul_div, div_le_iff₀ hβ0]
    nlinarith
  have hS1 := norm_defectSeries_le hM ((x : ℂ) + s * I)
  have hS0 := norm_defectSeries_le hM (x : ℂ)
  rw [abs_im_ofReal_add_mul_I] at hS1
  simp only [ofReal_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at hS0
  have hE : Real.exp (2 * π * |s|) ≤ Real.exp (π * β) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hS : (defectSeries β (x + s * I) - defectSeries β x).re ≤
      M * 2 * (3 * L) * (Real.exp (π * β) + 1) := by
    refine (re_le_norm _).trans ((norm_sub_le _ _).trans ?_)
    have h1 : M * 2 * Real.exp (2 * π * |s|) * (3 * L) ≤ M * 2 * Real.exp (π * β) * (3 * L) := by
      gcongr
    nlinarith
  have hsplit : (interpLog β (x + s * I)).re =
      (interpLog β x).re + (debyeLog β (x + s * I) - debyeLog β x).re +
        (defectSeries β (x + s * I) - defectSeries β x).re := by
    unfold interpLog; simp only [add_re, sub_re]; ring
  rw [hsplit]
  linarith

/-- Uniform strip bound `‖I_β(x + is)‖ ≤ C e^{-|x|}` for `|s| ≤ β/2`, `β ≥ 1`. -/
theorem exists_norm_besselInterp_strip_le {β : ℝ} (hβ : 1 ≤ β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x s : ℝ, |s| ≤ β / 2 →
      ‖besselInterp β ((x : ℂ) + s * I)‖ ≤ C * Real.exp (-|x|) := by
  obtain ⟨R, hR0, hR⟩ := exists_norm_besselInterp_add_le hβ
  obtain ⟨K, hK0, hK⟩ := exists_norm_besselInterp_ofReal_le (by linarith : (0 : ℝ) < β)
  refine ⟨R * K, mul_nonneg hR0 hK0, fun x s hs => ?_⟩
  calc ‖besselInterp β ((x : ℂ) + s * I)‖ ≤ R * ‖besselInterp β x‖ := hR x s hs
    _ ≤ R * (K * Real.exp (-|x|)) := mul_le_mul_of_nonneg_left (hK x) hR0
    _ = R * K * Real.exp (-|x|) := by ring

end FroehlichSpencer.BKT.Rotator.Contour
