/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Star.ActivityRate
public import FroehlichSpencer.BKT.Generic.Instances.SOS
public import FroehlichSpencer.BKT.SOS.Tilt.Translate
import Mathlib.Analysis.Calculus.Deriv.CompMul

/-!
# The SOS weight in the angle variable (the dipole tilt construction)

The generic core works in the angle variable `ψ = 2πh`, with the weight `w_β(z) = I_β(z/2π)`
(`sosWeightψ`), the strip `|Im z| ≤ πβ^{−1/3}` (`sosWidthψ`) and the cost
`β^{2/3} g_C(u/2π)` (`sosCostψ`), as for the plane rotator (`Rotator.TheoremC.besselWeightψ`).

For `0 < β ≤ 1`:

* `sosWeightψ_isStripWeight`, `sosCostψ_isCostEnvelope`, `sosWeightψ_ne_zero` ;
* `exists_sosWeightψ_logDeriv`: the logarithmic-derivative bounds `C β^{2/3} e^{|u|}`;
* `exists_sosWeightψ_curvature`: the curvature bound `C β^{2/3}`;
* `sosWeightψ_hasExpMajorant`: `|w_β(t + iu)| ≤ K e^{−β|t|/2π}` on the strip.

On the real axis
  `L_β(t) ≤ e^{−β|t|}` and the exponent of `E_β` is bounded; the translation ratio is bounded on
  the strip.

This is the exponential decay that makes the tilt `e^{ε(φ(0) − φ(x))}` integrable
  for `|ε| ≤ β/2`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Roughening

open Complex
open scoped Real
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.SOS.Interp
open FroehlichSpencer.BKT.SOS.Star
open FroehlichSpencer.BKT.SOS.Tilt
open FroehlichSpencer.BKT.Rotator.Contour (cEnvelope cEnvelope_neg)
open FroehlichSpencer.BKT.Rotator.BesselInterp (latticeSum)

/-- The SOS weight in the angle variable: `w_β(z) = I_β(z/2π)`. -/
def sosWeightψ (β : ℝ) (z : ℂ) : ℂ := sosInterp β (z / ((2 * π : ℝ) : ℂ))

/-- Its strip half-width `2π · ½β^{−1/3}`. -/
def sosWidthψ (β : ℝ) : ℝ := 2 * π * ((1 / 2 : ℝ) * β ^ (-(1 / 3 : ℝ)))

/-- Its cost `β^{2/3} g_C(u/2π)`. -/
def sosCostψ (β u : ℝ) : ℝ := β ^ (2 / 3 : ℝ) * cEnvelope interpolationCostConstant (u / (2 * π))

private theorem two_pi_pos' : (0 : ℝ) < 2 * π := by positivity

private theorem two_pi_inv_le_one : (2 * π)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by linarith [Real.two_le_pi])

private abbrev Pψ : ℂ := ((2 * π : ℝ) : ℂ)

private theorem Pψ_ne_zero : Pψ ≠ 0 := ofReal_ne_zero.mpr two_pi_pos'.ne'

private theorem norm_Pψ_inv : ‖Pψ⁻¹‖ = (2 * π)⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos two_pi_pos']

private theorem ofReal_div_Pψ (t : ℝ) : (t : ℂ) / Pψ = ((t / (2 * π) : ℝ) : ℂ) := by
  push_cast; rfl

theorem sosWeightψ_isStripWeight {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    IsStripWeight (sosWeightψ β) (sosWidthψ β) (sosCostψ β) :=
  sosScaled_isStripWeight hβ hβ1

theorem sosCostψ_isCostEnvelope {β : ℝ} (hβ : 0 ≤ β) (W : ℝ) :
    IsCostEnvelope (sosCostψ β) (interpolationCostConstant * β ^ (2 / 3 : ℝ))
      (interpolationCostConstant * β ^ (2 / 3 : ℝ)) W :=
  sosScaled_costEnvelope hβ W

theorem sosWeightψ_ne_zero (β : ℝ) (z : ℂ) : sosWeightψ β z ≠ 0 := sosInterp_ne_zero β _

/-- On the strip of `w_β`, the unscaled point lies in FS81's strip. -/
theorem abs_div_two_pi_le {β u : ℝ} (hu : |u| ≤ sosWidthψ β) :
    |u / (2 * π)| ≤ (1 / 2 : ℝ) * β ^ (-(1 / 3 : ℝ)) := by
  rw [abs_div, abs_of_pos two_pi_pos', div_le_iff₀ two_pi_pos', mul_comm]
  exact hu

/-! ## The logarithmic derivative -/

private theorem sosWeightψ_eq_comp (β : ℝ) :
    sosWeightψ β = fun y => sosInterp β (Pψ⁻¹ * y) := by
  funext y
  unfold sosWeightψ
  rw [div_eq_inv_mul]

theorem logDeriv_sosWeightψ (β : ℝ) :
    logDeriv (sosWeightψ β) = fun z =>
      (((2 * π : ℝ) : ℂ))⁻¹ * logDeriv (sosInterp β) (z / ((2 * π : ℝ) : ℂ)) := by
  funext z
  rw [sosWeightψ_eq_comp, logDeriv_apply]
  have h := deriv_comp_mul_left (Pψ⁻¹) (sosInterp β) z
  simp only [smul_eq_mul] at h
  rw [h, logDeriv_apply, div_eq_inv_mul z, mul_div_assoc]

theorem deriv_logDeriv_sosWeightψ (β : ℝ) (z : ℂ) :
    deriv (logDeriv (sosWeightψ β)) z =
      (((2 * π : ℝ) : ℂ))⁻¹ * ((((2 * π : ℝ) : ℂ))⁻¹ *
        deriv (logDeriv (sosInterp β)) (z / ((2 * π : ℝ) : ℂ))) := by
  rw [logDeriv_sosWeightψ]
  simp_rw [div_eq_inv_mul]
  rw [deriv_const_mul_field]
  have h := deriv_comp_mul_left (Pψ⁻¹) (logDeriv (sosInterp β)) z
  simp only [smul_eq_mul] at h
  rw [h]

/-- **The logarithmic-derivative bounds of `w_β`**: `M(u) = C β^{2/3} e^{|u|}`. -/
theorem exists_sosWeightψ_logDeriv :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, 0 < β → β ≤ 1 →
      HasLogDerivBounds (sosWeightψ β) (sosWidthψ β)
        (fun u => C * β ^ (2 / 3 : ℝ) * Real.exp |u|) := by
  obtain ⟨C, hC, hL⟩ := exists_hasLogDerivBounds_sosInterp
  refine ⟨C, hC, fun β hβ hβ1 => ?_⟩
  have hLβ := hL β hβ hβ1
  have hp := two_pi_pos'
  have hexp : ∀ u : ℝ, (2 * π)⁻¹ * (C * β ^ (2 / 3 : ℝ) * Real.exp (2 * π * |u / (2 * π)|)) ≤
      C * β ^ (2 / 3 : ℝ) * Real.exp |u| := by
    intro u
    have hrw : 2 * π * |u / (2 * π)| = |u| := by
      rw [abs_div, abs_of_pos hp]
      field_simp
    rw [hrw]
    have h2 : 0 ≤ C * β ^ (2 / 3 : ℝ) * Real.exp |u| := by positivity
    calc (2 * π)⁻¹ * (C * β ^ (2 / 3 : ℝ) * Real.exp |u|)
        ≤ 1 * (C * β ^ (2 / 3 : ℝ) * Real.exp |u|) :=
          mul_le_mul_of_nonneg_right two_pi_inv_le_one h2
      _ = C * β ^ (2 / 3 : ℝ) * Real.exp |u| := one_mul _
  refine ⟨fun t u hu => ?_, fun t u hu => ?_⟩
  · rw [logDeriv_sosWeightψ]
    simp only
    rw [← mul_sub, norm_mul, norm_Pψ_inv, Generic.add_mul_I_div_ofReal, ofReal_div_Pψ]
    refine le_trans ?_ (hexp u)
    exact mul_le_mul_of_nonneg_left (hLβ.logDeriv_sub_le _ _ (abs_div_two_pi_le hu))
      (inv_nonneg.mpr hp.le)
  · rw [deriv_logDeriv_sosWeightψ, deriv_logDeriv_sosWeightψ, ← mul_sub, ← mul_sub,
      norm_mul, norm_mul, norm_Pψ_inv, Generic.add_mul_I_div_ofReal, ofReal_div_Pψ]
    refine le_trans ?_ (hexp u)
    have hb := hLβ.deriv_logDeriv_sub_le (t / (2 * π)) (u / (2 * π)) (abs_div_two_pi_le hu)
    have hinv0 : 0 ≤ (2 * π)⁻¹ := inv_nonneg.mpr hp.le
    calc (2 * π)⁻¹ * ((2 * π)⁻¹ *
          ‖deriv (logDeriv (sosInterp β)) (((t / (2 * π) : ℝ) : ℂ) +
            ((u / (2 * π) : ℝ) : ℂ) * I) -
            deriv (logDeriv (sosInterp β)) ((t / (2 * π) : ℝ) : ℂ)‖)
        ≤ (2 * π)⁻¹ * (1 * ‖deriv (logDeriv (sosInterp β)) (((t / (2 * π) : ℝ) : ℂ) +
            ((u / (2 * π) : ℝ) : ℂ) * I) -
            deriv (logDeriv (sosInterp β)) ((t / (2 * π) : ℝ) : ℂ)‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right two_pi_inv_le_one (norm_nonneg _)) hinv0
      _ ≤ (2 * π)⁻¹ * (C * β ^ (2 / 3 : ℝ) * Real.exp (2 * π * |u / (2 * π)|)) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left hb hinv0

/-- **The curvature bound of `w_β`**: `κ = C β^{2/3}`. -/
theorem exists_sosWeightψ_curvature :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, 0 < β → β ≤ 1 →
      HasCurvatureBound (sosWeightψ β) (C * β ^ (2 / 3 : ℝ)) := by
  obtain ⟨C, hC, hK⟩ := exists_hasCurvatureBound_sosInterp
  refine ⟨C, hC, fun β hβ hβ1 => ?_⟩
  intro t s
  have hp := two_pi_pos'
  have hKβ := hK β hβ hβ1 (t / (2 * π)) (s / (2 * π))
  have hval : ∀ r : ℝ, sosWeightψ β (r : ℂ) = sosInterp β ((r / (2 * π) : ℝ) : ℂ) :=
    fun r => by unfold sosWeightψ; rw [ofReal_div_Pψ]
  have hld : (logDeriv (sosWeightψ β) (t : ℂ)).re =
      (2 * π)⁻¹ * (logDeriv (sosInterp β) ((t / (2 * π) : ℝ) : ℂ)).re := by
    rw [logDeriv_sosWeightψ]
    simp only
    rw [ofReal_div_Pψ, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  rw [hval, hval, hld]
  have hts : (t + s) / (2 * π) = t / (2 * π) + s / (2 * π) := add_div t s (2 * π)
  rw [hts]
  refine le_trans ?_ hKβ
  have hb : 0 ≤ C * β ^ (2 / 3 : ℝ) := mul_nonneg hC (Real.rpow_nonneg hβ.le _)
  have hcurv : C * β ^ (2 / 3 : ℝ) * (s / (2 * π)) ^ 2 ≤ C * β ^ (2 / 3 : ℝ) * s ^ 2 := by
    have hsq : (s / (2 * π)) ^ 2 ≤ s ^ 2 := by
      rw [div_pow]
      refine div_le_self (sq_nonneg s) ?_
      nlinarith [Real.two_le_pi]
    exact mul_le_mul_of_nonneg_left hsq hb
  have hlin : (2 * π)⁻¹ * (logDeriv (sosInterp β) ((t / (2 * π) : ℝ) : ℂ)).re * s =
      (logDeriv (sosInterp β) ((t / (2 * π) : ℝ) : ℂ)).re * (s / (2 * π)) := by
    field_simp
  rw [hlin]
  linarith

/-! ## Exponential decay on the strip -/

private lemma cEnvelope_le_of_width {C W u : ℝ} (hC : 0 ≤ C) (hW : 0 ≤ W) (hu : |u| ≤ W) :
    cEnvelope C u ≤ C * Real.exp (2 * π * W) := by
  unfold cEnvelope
  split_ifs with hsmall
  · have hu2 : u ^ 2 ≤ 1 := by
      rw [← sq_abs u]
      simpa using pow_le_pow_left₀ (abs_nonneg u) hsmall 2
    have hexp : 1 ≤ Real.exp (2 * π * W) := Real.one_le_exp (by positivity)
    calc C * u ^ 2 ≤ C * 1 := mul_le_mul_of_nonneg_left hu2 hC
      _ ≤ C * Real.exp (2 * π * W) := mul_le_mul_of_nonneg_left hexp hC
  · apply mul_le_mul_of_nonneg_left _ hC
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]

/-- `|I_β(t)| ≤ e^{6β^{2/3}Σ} e^{−β|t|}` on the real axis. -/
theorem norm_sosInterp_ofReal_le_exp {β : ℝ} (hβ : 0 ≤ β) (t : ℝ) :
    ‖sosInterp β t‖ ≤ Real.exp (β ^ (2 / 3 : ℝ) * 2 * (3 * latticeSum)) *
      Real.exp (-(β * |t|)) := by
  rw [sosInterp_ofReal hβ, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
  have hS : -∑' n : ℤ, sosDefect β n * Real.sinc (π * (t - n)) ^ 2 ≤
      β ^ (2 / 3 : ℝ) * 2 * (3 * latticeSum) := by
    have h := norm_sosSeries_ofReal_le hβ t
    rw [sosSeries_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
    exact (neg_le_abs _).trans h
  rw [mul_comm]
  exact mul_le_mul (Real.exp_le_exp.mpr hS) (exp_sosDebyeExponent_le hβ t)
    (Real.exp_pos _).le (Real.exp_pos _).le

/-- **The exponential majorant of `I_β` on FS81's strip**:
`|I_β(t + iu)| ≤ K e^{−β|t|}` for `|u| ≤ ½β^{−1/3}`. -/
theorem exists_norm_sosInterp_strip_le_exp {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t u : ℝ, |u| ≤ (1 / 2 : ℝ) * β ^ (-(1 / 3 : ℝ)) →
      ‖sosInterp β ((t : ℂ) + (u : ℂ) * I)‖ ≤ K * Real.exp (-(β * |t|)) := by
  have hw := interpolationCostConstant_spec.2 β hβ hβ1
  have hC := interpolationCostConstant_spec.1
  set W₀ := (1 / 2 : ℝ) * β ^ (-(1 / 3 : ℝ))
  have hW₀ : 0 ≤ W₀ := by positivity
  set b := β ^ (2 / 3 : ℝ)
  have hb : 0 ≤ b := Real.rpow_nonneg hβ.le _
  refine ⟨Real.exp (b * (interpolationCostConstant * Real.exp (2 * π * W₀))) *
    Real.exp (b * 2 * (3 * latticeSum)), by positivity, fun t u hu => ?_⟩
  have hratio : ‖sosInterp β ((t : ℂ) + (u : ℂ) * I)‖ =
      ‖sosInterp β ((t : ℂ) + (u : ℂ) * I) / sosInterp β t‖ * ‖sosInterp β t‖ := by
    rw [norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (sosInterp_ne_zero β t))]
  have hr := hw.ratio_le t u hu
  have hcost : b * cEnvelope interpolationCostConstant u ≤
      b * (interpolationCostConstant * Real.exp (2 * π * W₀)) :=
    mul_le_mul_of_nonneg_left (cEnvelope_le_of_width hC hW₀ hu) hb
  rw [hratio]
  calc ‖sosInterp β ((t : ℂ) + (u : ℂ) * I) / sosInterp β t‖ * ‖sosInterp β t‖
      ≤ Real.exp (b * (interpolationCostConstant * Real.exp (2 * π * W₀))) *
          (Real.exp (b * 2 * (3 * latticeSum)) * Real.exp (-(β * |t|))) :=
        mul_le_mul (hr.trans (Real.exp_le_exp.mpr hcost)) (norm_sosInterp_ofReal_le_exp hβ.le t)
          (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

/-- **The exponential majorant of `w_β`**: rate `β/2π` on the strip `|Im z| ≤ πβ^{−1/3}`. -/
theorem exists_sosWeightψ_hasExpMajorant {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ K : ℝ, HasExpMajorant (sosWeightψ β) (sosWidthψ β) (β / (2 * π)) K := by
  obtain ⟨K, -, hK⟩ := exists_norm_sosInterp_strip_le_exp hβ hβ1
  refine ⟨K, fun t u hu => ?_⟩
  unfold sosWeightψ
  rw [Generic.add_mul_I_div_ofReal]
  refine (hK (t / (2 * π)) (u / (2 * π)) (abs_div_two_pi_le hu)).trans (le_of_eq ?_)
  congr 2
  rw [abs_div, abs_of_pos two_pi_pos']
  ring

end FroehlichSpencer.BKT.SOS.Roughening

end
