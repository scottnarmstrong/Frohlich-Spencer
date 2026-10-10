/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Interp.Defect
public import FroehlichSpencer.BKT.Rotator.BesselInterp.Properties
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Appendix C: integer values and the real axis

For every `β > 0` the Appendix C interpolation `I_β = L_β E_β` takes the values `e^{-β|m|}` at the
integers (FS81 §7.2 (a)), and on the real axis it is real, positive and even (§7.2 (b)), and
integrable. On the real axis `L_β(x) ≤ e^{-β|x|}` because `β^{2/3}(1 + β^{2/3}x²)^{1/2} ≥ β|x|`,
and the exponent of `E_β` is bounded by `β^{2/3}` times a uniform lattice sum, since every
coefficient is at most `β^{2/3}` in absolute value.
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Interp

open Complex MeasureTheory
open scoped Real
open FroehlichSpencer.BKT.Rotator.BesselInterp

/-- `L_β` on the real axis. -/
lemma sosDebye_ofReal {β : ℝ} (hβ : 0 ≤ β) (x : ℝ) :
    sosDebye β x = ((Real.exp (-(β ^ (2 / 3 : ℝ)) *
      Real.sqrt (1 + β ^ (2 / 3 : ℝ) * x ^ 2)) : ℝ) : ℂ) := by
  unfold sosDebye
  have h1 : (0 : ℝ) ≤ 1 + β ^ (2 / 3 : ℝ) * x ^ 2 := by
    have := Real.rpow_nonneg hβ (2 / 3 : ℝ); positivity
  have hs : ((1 : ℂ) + ((β ^ (2 / 3 : ℝ) : ℝ) : ℂ) * (x : ℂ) ^ 2) ^ (1 / 2 : ℂ) =
      ((Real.sqrt (1 + β ^ (2 / 3 : ℝ) * x ^ 2) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow h1]
    push_cast; ring_nf
  rw [hs, ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp]

/-- The exponent of `E_β` on the real axis. -/
lemma sosSeries_ofReal (β t : ℝ) :
    sosSeries β t = ((∑' n : ℤ, sosDefect β n * Real.sinc (π * (t - n)) ^ 2 : ℝ) : ℂ) := by
  unfold sosSeries
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  have : ((t : ℂ) - n) = ((t - n : ℝ) : ℂ) := by push_cast; ring
  rw [this, sincSq_ofReal]
  push_cast; ring

/-- FS81 §7.2 (a): `I_β(m) = e^{-β|m|}` at every integer `m`. -/
theorem sosInterp_intCast {β : ℝ} (hβ : 0 ≤ β) (m : ℤ) :
    sosInterp β m = ((Real.exp (-(β * |(m : ℝ)|)) : ℝ) : ℂ) := by
  unfold sosInterp sosFactor sosSeries
  have hsum : ∑' n : ℤ, (sosDefect β n : ℂ) * sincSq ((m : ℂ) - n) = sosDefect β m := by
    rw [tsum_eq_single m]
    · simp [sincSq_zero]
    · intro n hn
      have : ((m : ℂ) - n) = ((m - n : ℤ) : ℂ) := by push_cast; ring
      rw [this, sincSq_intCast, ite_eq_right (sub_ne_zero.mpr (Ne.symm hn)), mul_zero]
  have hm : ((m : ℂ)) = ((m : ℝ) : ℂ) := by push_cast; rfl
  rw [hsum, hm, sosDebye_ofReal hβ, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
    ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  unfold sosDefect
  ring

/-- `I_β` on the real axis, as a real number. -/
lemma sosInterp_ofReal {β : ℝ} (hβ : 0 ≤ β) (x : ℝ) :
    sosInterp β x = ((Real.exp (-(β ^ (2 / 3 : ℝ)) * Real.sqrt (1 + β ^ (2 / 3 : ℝ) * x ^ 2)) *
      Real.exp (-∑' n : ℤ, sosDefect β n * Real.sinc (π * (x - n)) ^ 2) : ℝ) : ℂ) := by
  unfold sosInterp sosFactor
  rw [sosDebye_ofReal hβ, sosSeries_ofReal, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
    ← Complex.ofReal_mul]

/-- FS81 §7.2 (b): `I_β` is real and positive on the real axis. -/
theorem sosInterp_ofReal_im_eq_zero_and_re_pos {β : ℝ} (hβ : 0 ≤ β) (x : ℝ) :
    (sosInterp β x).im = 0 ∧ 0 < (sosInterp β x).re := by
  rw [sosInterp_ofReal hβ, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨rfl, mul_pos (Real.exp_pos _) (Real.exp_pos _)⟩

/-- FS81 §7.2 (b): `I_β` is even on the real axis. -/
lemma tsum_sosDefect_sinc_neg (β x : ℝ) :
    ∑' n : ℤ, sosDefect β n * Real.sinc (π * (-x - n)) ^ 2 =
      ∑' n : ℤ, sosDefect β n * Real.sinc (π * (x - n)) ^ 2 := by
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [Equiv.neg_apply, sosDefect_neg, Int.cast_neg]
  congr 1
  rw [show π * (-x - -(n : ℝ)) = -(π * (x - n)) by ring, Real.sinc_neg]

theorem sosInterp_neg_ofReal {β : ℝ} (hβ : 0 ≤ β) (x : ℝ) :
    sosInterp β (-x : ℝ) = sosInterp β x := by
  rw [sosInterp_ofReal hβ, sosInterp_ofReal hβ, neg_sq, tsum_sosDefect_sinc_neg]

/-- The exponent of `E_β` is bounded on the real axis. -/
lemma norm_sosSeries_ofReal_le {β : ℝ} (hβ : 0 ≤ β) (x : ℝ) :
    ‖sosSeries β x‖ ≤ β ^ (2 / 3 : ℝ) * 2 * (3 * latticeSum) := by
  have h := norm_tsum_shift_le (k := sincSq) (c := fun n => (sosDefect β n : ℂ))
    norm_sincSq_le_majorant (fun n => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_sosDefect_le hβ n) (x : ℂ)
  simp only [ofReal_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at h
  exact h

/-- `L_β(x) ≤ e^{-β|x|}` on the real axis. -/
lemma exp_sosDebyeExponent_le {β : ℝ} (hβ : 0 ≤ β) (x : ℝ) :
    Real.exp (-(β ^ (2 / 3 : ℝ)) * Real.sqrt (1 + β ^ (2 / 3 : ℝ) * x ^ 2)) ≤
      Real.exp (-(β * |x|)) := by
  apply Real.exp_le_exp.mpr
  set u := β ^ (1 / 3 : ℝ)
  have hu0 : 0 ≤ u := Real.rpow_nonneg hβ _
  have h23 : β ^ (2 / 3 : ℝ) = u ^ 2 := (rpow_one_third_sq hβ).symm
  have h3 : β = u ^ 3 := (rpow_one_third_cube hβ).symm
  have hS : u * |x| ≤ Real.sqrt (1 + u ^ 2 * x ^ 2) :=
    calc u * |x| = Real.sqrt ((u * |x|) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (1 + u ^ 2 * x ^ 2) :=
        Real.sqrt_le_sqrt (by rw [mul_pow, sq_abs]; linarith)
  rw [h23, h3]
  nlinarith [mul_le_mul_of_nonneg_left hS (sq_nonneg u)]

/-- FS81 §7.2 (b): `I_β` is integrable on the real axis, for every `β > 0`. -/
theorem integrable_sosInterp {β : ℝ} (hβ : 0 < β) : Integrable fun x : ℝ => sosInterp β x := by
  set B := Real.exp (β ^ (2 / 3 : ℝ) * 2 * (3 * latticeSum))
  have hbound : ∀ x : ℝ, ‖sosInterp β x‖ ≤ 2 * B * (1 + (β * x) ^ 2)⁻¹ := by
    intro x
    rw [sosInterp_ofReal hβ.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
    have hS : -∑' n : ℤ, sosDefect β n * Real.sinc (π * (x - n)) ^ 2 ≤
        β ^ (2 / 3 : ℝ) * 2 * (3 * latticeSum) := by
      have h := norm_sosSeries_ofReal_le hβ.le x
      rw [sosSeries_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
      exact (neg_le_abs _).trans h
    have he := exp_neg_abs_le (β * x)
    rw [abs_mul, abs_of_pos hβ] at he
    calc Real.exp (-(β ^ (2 / 3 : ℝ)) * Real.sqrt (1 + β ^ (2 / 3 : ℝ) * x ^ 2)) *
          Real.exp (-∑' n : ℤ, sosDefect β n * Real.sinc (π * (x - n)) ^ 2)
        ≤ Real.exp (-(β * |x|)) * B :=
          mul_le_mul (exp_sosDebyeExponent_le hβ.le x) (Real.exp_le_exp.mpr hS)
            (Real.exp_pos _).le (Real.exp_pos _).le
      _ ≤ 2 * (1 + (β * x) ^ 2)⁻¹ * B := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
      _ = 2 * B * (1 + (β * x) ^ 2)⁻¹ := by ring
  have hint : Integrable fun x : ℝ => 2 * B * (1 + (β * x) ^ 2)⁻¹ :=
    (integrable_inv_one_add_sq.comp_mul_left' hβ.ne').const_mul _
  have hcont : Continuous fun x : ℝ => sosInterp β x := by
    have : (fun x : ℝ => sosInterp β x) = fun x : ℝ =>
        ((Real.exp (-(β ^ (2 / 3 : ℝ)) * Real.sqrt (1 + β ^ (2 / 3 : ℝ) * x ^ 2)) *
          Real.exp (-∑' n : ℤ, sosDefect β n * Real.sinc (π * (x - n)) ^ 2) : ℝ) : ℂ) :=
      funext fun x => sosInterp_ofReal hβ.le x
    rw [this]
    have hS : Continuous fun x : ℝ => sosSeries β x :=
      (differentiable_tsum_shift differentiable_sincSq norm_sincSq_le_majorant
        (c := fun n => (sosDefect β n : ℂ)) (M := β ^ (2 / 3 : ℝ)) (fun n => by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_sosDefect_le hβ.le n)).continuous.comp
        Complex.continuous_ofReal
    have hS' : Continuous fun x : ℝ => ∑' n : ℤ, sosDefect β n * Real.sinc (π * (x - n)) ^ 2 := by
      have := Complex.continuous_re.comp hS
      refine this.congr fun x => ?_
      simp only [Function.comp_apply, sosSeries_ofReal, Complex.ofReal_re]
    exact Complex.continuous_ofReal.comp (by fun_prop)
  exact hint.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

end FroehlichSpencer.BKT.SOS.Interp
