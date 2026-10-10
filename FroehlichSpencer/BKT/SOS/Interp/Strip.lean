/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Interp.Basic
public import Mathlib.Analysis.Calculus.LogDeriv
import FroehlichSpencer.BKT.Rotator.BesselInterp.Vertical
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Appendix C on the strip: the explicit logarithm and its derivatives

With `b = β^{2/3}` and `s(z) = (1 + b z²)^{1/2}` (principal branch), the Appendix C interpolation is
`I_β = exp Φ` with the explicit logarithm `Φ(z) = -b s(z) - S_β(z)`, where `S_β` is the exponent
series of `E_β`. On the strip `β^{1/3}|Im z| < 1` (half-width `β^{-1/3}`, containing FS81's closed
strip `|Im φ| ≤ ½β^{-1/3}`), `s` is holomorphic and `S_β` is entire, so `I_β` is holomorphic there
and has no zeros at all. The derivatives are `Φ' = -b² z/s - S_β'` and `Φ'' = -b²/s³ - S_β''`; on
the closed half-strip `|b² / s³| ≤ 8 β^{4/3}` and `|S_β^{(m)}| ≤ β^{2/3} A_m e^{2π|Im z|} 3 Σ_k(1+k²)⁻¹`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Interp

open Complex Metric Filter Topology
open scoped Real
open FroehlichSpencer.BKT.Rotator.BesselInterp

/-- `b = β^{2/3}` as a complex number. -/
def sosB (β : ℝ) : ℂ := ((β ^ (2 / 3 : ℝ) : ℝ) : ℂ)

/-- `s(z) = (1 + β^{2/3} z²)^{1/2}`. -/
def sosRoot (β : ℝ) (z : ℂ) : ℂ := (1 + sosB β * z ^ 2) ^ (1 / 2 : ℂ)

/-- The explicit logarithm `Φ = -β^{2/3} s - S_β` of the Appendix C interpolation. -/
def sosLog (β : ℝ) (z : ℂ) : ℂ := -sosB β * sosRoot β z - sosSeries β z

/-- First derivative of the defect series. -/
def sosSeriesDeriv (β : ℝ) (z : ℂ) : ℂ := ∑' n : ℤ, (sosDefect β n : ℂ) * deriv sincSq (z - n)

/-- Second derivative of the defect series. -/
def sosSeriesDeriv2 (β : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℤ, (sosDefect β n : ℂ) * deriv (deriv sincSq) (z - n)

/-- `Φ' = -b² z / s - S'`. -/
def sosLogDeriv (β : ℝ) (z : ℂ) : ℂ := -(sosB β ^ 2 * z / sosRoot β z) - sosSeriesDeriv β z

/-- `Φ'' = -b² / s³ - S''`. -/
def sosLogDeriv2 (β : ℝ) (z : ℂ) : ℂ := -(sosB β ^ 2 / sosRoot β z ^ 3) - sosSeriesDeriv2 β z

theorem sosInterp_eq_exp_sosLog (β : ℝ) (z : ℂ) : sosInterp β z = Complex.exp (sosLog β z) := by
  unfold sosInterp sosDebye sosFactor sosLog sosRoot sosB
  rw [← Complex.exp_add]; congr 1

theorem sosInterp_ne_zero (β : ℝ) (z : ℂ) : sosInterp β z ≠ 0 := by
  rw [sosInterp_eq_exp_sosLog]; exact Complex.exp_ne_zero _

/-! ### The square root on the strip -/

lemma sosB_mul_sq {β : ℝ} (hβ : 0 ≤ β) (z : ℂ) :
    sosB β * z ^ 2 = (((β ^ (1 / 3 : ℝ) : ℝ) : ℂ) * z) ^ 2 := by
  unfold sosB
  rw [mul_pow, ← Complex.ofReal_pow, rpow_one_third_sq hβ]

lemma im_scaled {β : ℝ} (hβ : 0 ≤ β) (z : ℂ) :
    |((((β ^ (1 / 3 : ℝ) : ℝ) : ℂ) * z)).im| = β ^ (1 / 3 : ℝ) * |z.im| := by
  rw [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hβ _)]

lemma one_add_sosB_mem_slitPlane {β : ℝ} (hβ : 0 ≤ β) {z : ℂ}
    (hz : β ^ (1 / 3 : ℝ) * |z.im| < 1) : 1 + sosB β * z ^ 2 ∈ slitPlane := by
  rw [sosB_mul_sq hβ]
  exact one_add_sq_mem_slitPlane (by rw [im_scaled hβ]; exact hz)

lemma sosRoot_sq (β : ℝ) (z : ℂ) : sosRoot β z ^ 2 = 1 + sosB β * z ^ 2 := half_cpow_sq _

lemma sosRoot_ne_zero {β : ℝ} (hβ : 0 ≤ β) {z : ℂ} (hz : β ^ (1 / 3 : ℝ) * |z.im| < 1) :
    sosRoot β z ≠ 0 := by
  intro h
  have := half_cpow_re_pos (one_add_sosB_mem_slitPlane hβ hz)
  unfold sosRoot at h
  rw [h, zero_re] at this
  exact lt_irrefl _ this

theorem hasDerivAt_sosRoot {β : ℝ} (hβ : 0 ≤ β) {z : ℂ} (hz : β ^ (1 / 3 : ℝ) * |z.im| < 1) :
    HasDerivAt (sosRoot β) (sosB β * z / sosRoot β z) z := by
  have hs0 := sosRoot_ne_zero hβ hz
  have hf : HasDerivAt (fun z : ℂ => 1 + sosB β * z ^ 2) (sosB β * (2 * z)) z := by
    have := ((hasDerivAt_pow 2 z).const_mul (sosB β)).const_add 1
    convert this using 1; push_cast; ring
  have h := hf.cpow_const (c := (1 / 2 : ℂ)) (one_add_sosB_mem_slitPlane hβ hz)
  unfold sosRoot
  convert h using 1
  have hu0 : 1 + sosB β * z ^ 2 ≠ 0 := slitPlane_ne_zero (one_add_sosB_mem_slitPlane hβ hz)
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by norm_num, Complex.cpow_neg]
  have hs : sosRoot β z = (1 + sosB β * z ^ 2) ^ (1 / 2 : ℂ) := rfl
  rw [← hs]
  field_simp

theorem hasDerivAt_sosRoot_quot {β : ℝ} (hβ : 0 ≤ β) {z : ℂ}
    (hz : β ^ (1 / 3 : ℝ) * |z.im| < 1) :
    HasDerivAt (fun z => sosB β ^ 2 * z / sosRoot β z) (sosB β ^ 2 / sosRoot β z ^ 3) z := by
  have hs0 := sosRoot_ne_zero hβ hz
  have h := ((hasDerivAt_id' z).const_mul (sosB β ^ 2)).div (hasDerivAt_sosRoot hβ hz) hs0
  convert h using 1
  have hsq := sosRoot_sq β z
  field_simp
  linear_combination (-(sosB β ^ 2)) * hsq

/-! ### The defect series -/

lemma norm_sosDefect_le {β : ℝ} (hβ : 0 ≤ β) (n : ℤ) :
    ‖(sosDefect β n : ℂ)‖ ≤ β ^ (2 / 3 : ℝ) := by
  rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_sosDefect_le hβ n

theorem hasDerivAt_sosSeries {β : ℝ} (hβ : 0 ≤ β) (z : ℂ) :
    HasDerivAt (sosSeries β) (sosSeriesDeriv β z) z := by
  have hd := differentiable_tsum_shift differentiable_sincSq norm_sincSq_le_majorant
    (norm_sosDefect_le hβ)
  have h := (hd z).hasDerivAt
  rw [deriv_tsum_shift differentiable_sincSq norm_sincSq_le_majorant (norm_sosDefect_le hβ)] at h
  exact h

theorem hasDerivAt_sosSeriesDeriv {β : ℝ} (hβ : 0 ≤ β) (z : ℂ) :
    HasDerivAt (sosSeriesDeriv β) (sosSeriesDeriv2 β z) z := by
  have hd := differentiable_tsum_shift differentiable_deriv_sincSq norm_deriv_sincSq_le_majorant
    (norm_sosDefect_le hβ)
  have h := (hd z).hasDerivAt
  rw [deriv_tsum_shift differentiable_deriv_sincSq norm_deriv_sincSq_le_majorant
    (norm_sosDefect_le hβ)] at h
  exact h

theorem norm_sosSeries_le {β : ℝ} (hβ : 0 ≤ β) (z : ℂ) :
    ‖sosSeries β z‖ ≤ β ^ (2 / 3 : ℝ) * 2 * Real.exp (2 * π * |z.im|) * (3 * latticeSum) :=
  norm_tsum_shift_le norm_sincSq_le_majorant (norm_sosDefect_le hβ) z

theorem norm_sosSeriesDeriv_le {β : ℝ} (hβ : 0 ≤ β) (z : ℂ) :
    ‖sosSeriesDeriv β z‖ ≤
      β ^ (2 / 3 : ℝ) * kernelConst1 * Real.exp (2 * π * |z.im|) * (3 * latticeSum) :=
  norm_tsum_shift_le norm_deriv_sincSq_le_majorant (norm_sosDefect_le hβ) z

theorem norm_sosSeriesDeriv2_le {β : ℝ} (hβ : 0 ≤ β) (z : ℂ) :
    ‖sosSeriesDeriv2 β z‖ ≤
      β ^ (2 / 3 : ℝ) * kernelConst2 * Real.exp (2 * π * |z.im|) * (3 * latticeSum) :=
  norm_tsum_shift_le norm_deriv_deriv_sincSq_le_majorant (norm_sosDefect_le hβ) z

/-! ### The logarithm -/

theorem hasDerivAt_sosLog {β : ℝ} (hβ : 0 ≤ β) {z : ℂ} (hz : β ^ (1 / 3 : ℝ) * |z.im| < 1) :
    HasDerivAt (sosLog β) (sosLogDeriv β z) z := by
  have h := ((hasDerivAt_sosRoot hβ hz).const_mul (-sosB β)).sub (hasDerivAt_sosSeries hβ z)
  unfold sosLog sosLogDeriv
  convert h using 1
  ring

theorem hasDerivAt_sosLogDeriv {β : ℝ} (hβ : 0 ≤ β) {z : ℂ}
    (hz : β ^ (1 / 3 : ℝ) * |z.im| < 1) :
    HasDerivAt (sosLogDeriv β) (sosLogDeriv2 β z) z := by
  have h := (hasDerivAt_sosRoot_quot hβ hz).neg.sub (hasDerivAt_sosSeriesDeriv hβ z)
  unfold sosLogDeriv sosLogDeriv2
  exact h

lemma isOpen_sosStrip (β : ℝ) : IsOpen {z : ℂ | β ^ (1 / 3 : ℝ) * |z.im| < 1} :=
  isOpen_lt (continuous_const.mul (continuous_abs.comp continuous_im)) continuous_const

theorem hasDerivAt_sosInterp {β : ℝ} (hβ : 0 ≤ β) {z : ℂ} (hz : β ^ (1 / 3 : ℝ) * |z.im| < 1) :
    HasDerivAt (sosInterp β) (Complex.exp (sosLog β z) * sosLogDeriv β z) z := by
  have h := (hasDerivAt_sosLog hβ hz).cexp
  have heq : sosInterp β = fun w => Complex.exp (sosLog β w) :=
    funext fun w => sosInterp_eq_exp_sosLog β w
  rw [heq]; exact h

/-- `I_β` is holomorphic at every point of FS81's closed strip `|Im φ| ≤ ½β^{-1/3}`. -/
theorem analyticAt_sosInterp {β : ℝ} (hβ : 0 ≤ β) {z : ℂ}
    (hz : β ^ (1 / 3 : ℝ) * |z.im| ≤ 1 / 2) : AnalyticAt ℂ (sosInterp β) z :=
  DifferentiableOn.analyticAt (s := {w : ℂ | β ^ (1 / 3 : ℝ) * |w.im| < 1})
    (fun _ hw => (hasDerivAt_sosInterp hβ hw).differentiableAt.differentiableWithinAt)
    ((isOpen_sosStrip β).mem_nhds (show β ^ (1 / 3 : ℝ) * |z.im| < 1 by linarith))

theorem logDeriv_sosInterp {β : ℝ} (hβ : 0 ≤ β) {z : ℂ} (hz : β ^ (1 / 3 : ℝ) * |z.im| < 1) :
    logDeriv (sosInterp β) z = sosLogDeriv β z := by
  rw [logDeriv_apply, (hasDerivAt_sosInterp hβ hz).deriv, sosInterp_eq_exp_sosLog]
  field_simp [Complex.exp_ne_zero]

theorem deriv_logDeriv_sosInterp {β : ℝ} (hβ : 0 ≤ β) {z : ℂ}
    (hz : β ^ (1 / 3 : ℝ) * |z.im| < 1) :
    deriv (logDeriv (sosInterp β)) z = sosLogDeriv2 β z := by
  have heq : logDeriv (sosInterp β) =ᶠ[𝓝 z] sosLogDeriv β :=
    Filter.eventually_of_mem ((isOpen_sosStrip β).mem_nhds hz) fun _ hw =>
      logDeriv_sosInterp hβ hw
  rw [heq.deriv_eq]
  exact (hasDerivAt_sosLogDeriv hβ hz).deriv

/-! ### Bounds on the half strip -/

lemma norm_sosRoot_ge {β : ℝ} (hβ : 0 ≤ β) {z : ℂ} (hz : β ^ (1 / 3 : ℝ) * |z.im| ≤ 1 / 2) :
    1 / 2 ≤ ‖sosRoot β z‖ := by
  have h1 : 1 / 4 ≤ ‖1 + sosB β * z ^ 2‖ := by
    rw [sosB_mul_sq hβ]
    exact quarter_le_norm_one_add_sq (by rw [im_scaled hβ]; exact hz)
  have h2 : ‖sosRoot β z‖ ^ 2 = ‖1 + sosB β * z ^ 2‖ := by
    rw [← norm_pow, sosRoot_sq]
  nlinarith [norm_nonneg (sosRoot β z)]

lemma norm_sosB (β : ℝ) (hβ : 0 ≤ β) : ‖sosB β‖ = β ^ (2 / 3 : ℝ) := by
  unfold sosB; rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hβ _)]

/-- `|b²/s³| ≤ 8 β^{4/3}` on the half strip. -/
lemma norm_sosB_sq_div_sosRoot_cube_le {β : ℝ} (hβ : 0 ≤ β) {z : ℂ}
    (hz : β ^ (1 / 3 : ℝ) * |z.im| ≤ 1 / 2) :
    ‖sosB β ^ 2 / sosRoot β z ^ 3‖ ≤ 8 * (β ^ (2 / 3 : ℝ)) ^ 2 := by
  have hs := norm_sosRoot_ge hβ hz
  rw [norm_div, norm_pow, norm_pow, norm_sosB β hβ, div_le_iff₀ (by positivity)]
  have h3 : (1 / 2 : ℝ) ^ 3 ≤ ‖sosRoot β z‖ ^ 3 := pow_le_pow_left₀ (by norm_num) hs 3
  have hb := sq_nonneg (β ^ (2 / 3 : ℝ))
  nlinarith

/-- The real-axis realness of `Φ'` (FS81 (b) for the logarithmic derivative). -/
theorem sosLogDeriv_ofReal_im {β : ℝ} (hβ : 0 ≤ β) (x : ℝ) : (sosLogDeriv β x).im = 0 := by
  have hx : β ^ (1 / 3 : ℝ) * |((x : ℂ)).im| < 1 := by simp
  have hS : (sosSeriesDeriv β x).im = 0 :=
    im_eq_zero_of_hasDerivAt_of_real (hasDerivAt_sosSeries hβ x)
      fun t => by rw [sosSeries_ofReal, ofReal_im]
  have hroot : sosRoot β x = ((Real.sqrt (1 + β ^ (2 / 3 : ℝ) * x ^ 2) : ℝ) : ℂ) := by
    unfold sosRoot sosB
    have h1 : (0 : ℝ) ≤ 1 + β ^ (2 / 3 : ℝ) * x ^ 2 := by
      have := Real.rpow_nonneg hβ (2 / 3 : ℝ); positivity
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow h1]; push_cast; ring_nf
  have hL : (sosB β ^ 2 * (x : ℂ) / sosRoot β x).im = 0 := by
    rw [hroot]; unfold sosB
    rw [show ((β ^ (2 / 3 : ℝ) : ℝ) : ℂ) ^ 2 * (x : ℂ) /
        ((Real.sqrt (1 + β ^ (2 / 3 : ℝ) * x ^ 2) : ℝ) : ℂ) =
      (((β ^ (2 / 3 : ℝ)) ^ 2 * x / Real.sqrt (1 + β ^ (2 / 3 : ℝ) * x ^ 2) : ℝ) : ℂ) by
        push_cast; ring]
    exact ofReal_im _
  unfold sosLogDeriv
  rw [sub_im, neg_im, hL, hS]; simp

end FroehlichSpencer.BKT.SOS.Interp
