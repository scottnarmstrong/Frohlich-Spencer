/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.TheoremC.Defs
public import FroehlichSpencer.BKT.Generic.Instances.Bessel
public import FroehlichSpencer.BKT.Generic.StripWeightScaling
public import FroehlichSpencer.BKT.Generic.Energy.CostEnvelope
import Mathlib.Analysis.Calculus.Deriv.CompMul

/-!
# The plane-rotator dual weight in the angle variable

FS81 Appendix B (J p. 599) interpolates the Bessel weights `I_β(n)` by `I_β(φ) = L_β(φ) E_β(φ)`
(`BesselInterp.besselInterp`).

There the
weight is `w_β(z) = I_β(z / 2π)` (`besselWeightψ`), the strip is `|Im z| ≤ πβ`, and the cost is
`g_C(u / 2π) / β` (`besselCostψ`).

* `I_β` has no zeros in `|Im z| < β` (`BesselInterp.besselInterp_ne_zero`, with the
  Appendix B interpolation), so `w_β` has none on the closed strip `|Im z| ≤ πβ`.
* `exists_besselWeightψ`: for all large `β`, `w_β` is a strip weight of width `πβ` with cost
  `g_C(u/2π)/β`, has no zeros on the closed strip, has logarithmic-derivative bounds
  `(C/β) e^{|u|}`, curvature `C/β`, and its cost is a `(C/β, C/β)` cost envelope up to `πβ`.

These come from the Appendix B estimates of `Generic/Instances/Bessel.lean` by the rescaling
  `z ↦ z / 2π` (`IsStripWeight.comp_div` and the chain rule for `logDeriv`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.TheoremC

open Complex
open scoped Real
open FroehlichSpencer.BKT.Rotator.BesselInterp

/-! ## The rescaled weight -/

/-- The period `2π` as a complex number. -/
private abbrev Pψ : ℂ := ((2 * π : ℝ) : ℂ)

private theorem two_pi_pos' : (0 : ℝ) < 2 * π := by positivity

private theorem Pψ_ne_zero : Pψ ≠ 0 := ofReal_ne_zero.mpr two_pi_pos'.ne'

theorem besselWeightψ_apply (β : ℝ) (z : ℂ) :
    besselWeightψ β z = besselInterp β (z / ((2 * π : ℝ) : ℂ)) := by
  unfold besselWeightψ
  push_cast
  rfl

private theorem besselWeightψ_eq_comp (β : ℝ) :
    besselWeightψ β = fun y => besselInterp β (Pψ⁻¹ * y) := by
  funext y
  rw [besselWeightψ_apply, div_eq_inv_mul]

theorem logDeriv_besselWeightψ (β : ℝ) :
    logDeriv (besselWeightψ β) = fun z =>
      (((2 * π : ℝ) : ℂ))⁻¹ * logDeriv (besselInterp β) (z / ((2 * π : ℝ) : ℂ)) := by
  funext z
  rw [besselWeightψ_eq_comp, logDeriv_apply]
  have h := deriv_comp_mul_left (Pψ⁻¹) (besselInterp β) z
  simp only [smul_eq_mul] at h
  rw [h, logDeriv_apply, div_eq_inv_mul z, mul_div_assoc]

theorem deriv_logDeriv_besselWeightψ (β : ℝ) (z : ℂ) :
    deriv (logDeriv (besselWeightψ β)) z =
      (((2 * π : ℝ) : ℂ))⁻¹ * ((((2 * π : ℝ) : ℂ))⁻¹ *
        deriv (logDeriv (besselInterp β)) (z / ((2 * π : ℝ) : ℂ))) := by
  rw [logDeriv_besselWeightψ]
  simp_rw [div_eq_inv_mul]
  rw [deriv_const_mul_field]
  have h := deriv_comp_mul_left (Pψ⁻¹) (logDeriv (besselInterp β)) z
  simp only [smul_eq_mul] at h
  rw [h]

private theorem norm_Pψ_inv : ‖Pψ⁻¹‖ = (2 * π)⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos two_pi_pos']

private theorem two_pi_inv_le_one : (2 * π)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by linarith [Real.two_le_pi])

private theorem ofReal_div_Pψ (t : ℝ) : (t : ℂ) / Pψ = ((t / (2 * π) : ℝ) : ℂ) := by
  push_cast; rfl

/-! ## Monotonicity in the constants -/

private theorem isStripWeight_mono_cost {w : ℂ → ℂ} {W : ℝ} {c c' : ℝ → ℝ}
    (hw : Generic.IsStripWeight w W c) (hle : ∀ u, c u ≤ c' u) (heven : ∀ u, c' (-u) = c' u)
    (hzero : c' 0 = 0) : Generic.IsStripWeight w W c' :=
  { hw with
    ratio_le := fun t u hu => (hw.ratio_le t u hu).trans (Real.exp_le_exp.mpr (hle u))
    cost_even := heven
    cost_zero := hzero }

private theorem cEnvelope_mono {C₁ C : ℝ} (hC : C₁ ≤ C) (a : ℝ) :
    Contour.cEnvelope C₁ a ≤ Contour.cEnvelope C a := by
  unfold Contour.cEnvelope
  split_ifs
  · exact mul_le_mul_of_nonneg_right hC (sq_nonneg a)
  · exact mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le

/-! ## The cost envelope in the angle variable -/

private theorem besselCostψ_isCostEnvelope {C β : ℝ} (hC : 0 ≤ C) (hβ : 0 < β) (W : ℝ) :
    Generic.IsCostEnvelope (besselCostψ C β) (C / β) (C / β) W where
  even u := by
    unfold besselCostψ
    rw [neg_div, Contour.cEnvelope_neg]
  zero := by simp [besselCostψ, Contour.cEnvelope]
  nonneg_κ := div_nonneg hC hβ.le
  nonneg_κ' := div_nonneg hC hβ.le
  quad u hu := by
    have hp := two_pi_pos'
    have hdiv : |u / (2 * π)| ≤ 1 := by
      rw [abs_div, abs_of_pos hp, div_le_one hp]
      linarith [Real.two_le_pi]
    unfold besselCostψ Contour.cEnvelope
    rw [ite_eq_left hdiv]
    have hsq : (u / (2 * π)) ^ 2 ≤ u ^ 2 := by
      rw [div_pow]
      refine div_le_self (sq_nonneg u) ?_
      nlinarith [Real.two_le_pi]
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hC) hβ.le
  expo u hu _ := by
    have hp := two_pi_pos'
    unfold besselCostψ Contour.cEnvelope
    have hCβ : 0 ≤ C / β := div_nonneg hC hβ.le
    split_ifs with h
    · have hsq : (u / (2 * π)) ^ 2 ≤ 1 := by
        rw [← sq_abs]
        exact pow_le_one₀ (abs_nonneg _) h
      have he : 1 ≤ Real.exp (2 * π * |u|) := Real.one_le_exp (by positivity)
      calc C * (u / (2 * π)) ^ 2 / β = C / β * (u / (2 * π)) ^ 2 := by ring
        _ ≤ C / β * 1 := mul_le_mul_of_nonneg_left hsq hCβ
        _ ≤ C / β * Real.exp (2 * π * |u|) := mul_le_mul_of_nonneg_left he hCβ
    · have hrw : 2 * π * |u / (2 * π)| = |u| := by
        rw [abs_div, abs_of_pos hp]
        field_simp
      rw [hrw]
      have he : Real.exp |u| ≤ Real.exp (2 * π * |u|) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [abs_nonneg u, Real.two_le_pi]
      calc C * Real.exp |u| / β = C / β * Real.exp |u| := by ring
        _ ≤ C / β * Real.exp (2 * π * |u|) := mul_le_mul_of_nonneg_left he hCβ

/-! ## The main theorem -/

/-- The plane-rotator dual weight in the angle variable satisfies every generic-core hypothesis. -/
theorem exists_besselWeightψ :
    ∃ β₀ C : ℝ, 1 ≤ β₀ ∧ 0 < C ∧ ∀ β : ℝ, β₀ ≤ β →
      Generic.IsStripWeight (besselWeightψ β) (Real.pi * β) (besselCostψ C β) ∧
      (∀ z : ℂ, |z.im| ≤ Real.pi * β → besselWeightψ β z ≠ 0) ∧
      Generic.HasLogDerivBounds (besselWeightψ β) (Real.pi * β) (fun u => C / β * Real.exp |u|) ∧
      Generic.HasCurvatureBound (besselWeightψ β) (C / β) ∧
      Generic.IsCostEnvelope (besselCostψ C β) (C / β) (C / β) (Real.pi * β) := by
  obtain ⟨β₁, C₁, -, hC₁, hS⟩ := Generic.exists_isStripWeight_besselInterp
  obtain ⟨β₂, C₂, -, hC₂, hL⟩ := Generic.exists_hasLogDerivBounds_besselInterp
  obtain ⟨β₃, C₃, -, hC₃, hK⟩ := Generic.exists_hasCurvatureBound_besselInterp
  set C := max (max C₁ C₂) (max C₃ 1) with hCdef
  have hC1 : C₁ ≤ C := le_max_of_le_left (le_max_left _ _)
  have hC2 : C₂ ≤ C := le_max_of_le_left (le_max_right _ _)
  have hC3 : C₃ ≤ C := le_max_of_le_right (le_max_left _ _)
  have hCone : 1 ≤ C := le_max_of_le_right (le_max_right _ _)
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hCone
  refine ⟨max (max β₁ β₂) (max β₃ 1), C, le_max_of_le_right (le_max_right _ _), hCpos,
    fun β hβ => ?_⟩
  have hβ1 : β₁ ≤ β := le_trans (le_max_of_le_left (le_max_left _ _)) hβ
  have hβ2 : β₂ ≤ β := le_trans (le_max_of_le_left (le_max_right _ _)) hβ
  have hβ3 : β₃ ≤ β := le_trans (le_max_of_le_right (le_max_left _ _)) hβ
  have hβone : 1 ≤ β := le_trans (le_max_of_le_right (le_max_right _ _)) hβ
  have hβpos : 0 < β := lt_of_lt_of_le one_pos hβone
  have hp := two_pi_pos'
  have hpi := Real.two_le_pi
  -- the strip condition after rescaling
  have hstrip : ∀ u : ℝ, |u| ≤ π * β → |u / (2 * π)| ≤ β / 2 := by
    intro u hu
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, besselCostψ_isCostEnvelope hCpos.le hβpos _⟩
  · -- the strip weight
    have hw := isStripWeight_mono_cost (hS β hβ1) (c' := fun u => Contour.cEnvelope C u / β)
      (fun u => div_le_div_of_nonneg_right (cEnvelope_mono hC1 u) hβpos.le)
      (fun u => by simp only [Contour.cEnvelope_neg]) (by simp [Contour.cEnvelope])
    have h := hw.comp_div hp
    rw [show 2 * π * (β / 2) = π * β by ring] at h
    have hfun : (fun z => besselInterp β (z / ((2 * π : ℝ) : ℂ))) = besselWeightψ β :=
      funext fun z => (besselWeightψ_apply β z).symm
    rw [hfun] at h
    exact h
  · -- no zeros
    intro z hz
    rw [besselWeightψ_apply]
    refine BesselInterp.besselInterp_ne_zero hβpos ?_
    rw [Complex.div_ofReal_im]
    have := hstrip z.im hz
    linarith [abs_nonneg (z.im / (2 * π))]
  · -- the logarithmic-derivative bounds
    have hLβ := hL β hβ2
    have hexp : ∀ u : ℝ, (2 * π)⁻¹ * (C₂ / β * Real.exp (2 * π * |u / (2 * π)|)) ≤
        C / β * Real.exp |u| := by
      intro u
      have hrw : 2 * π * |u / (2 * π)| = |u| := by
        rw [abs_div, abs_of_pos hp]
        field_simp
      rw [hrw]
      have h1 : C₂ / β ≤ C / β := div_le_div_of_nonneg_right hC2 hβpos.le
      have h2 : 0 ≤ C₂ / β * Real.exp |u| := by positivity
      calc (2 * π)⁻¹ * (C₂ / β * Real.exp |u|) ≤ 1 * (C₂ / β * Real.exp |u|) :=
            mul_le_mul_of_nonneg_right two_pi_inv_le_one h2
        _ ≤ C / β * Real.exp |u| := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    refine ⟨fun t u hu => ?_, fun t u hu => ?_⟩
    · rw [logDeriv_besselWeightψ]
      simp only
      rw [← mul_sub, norm_mul, norm_Pψ_inv, Generic.add_mul_I_div_ofReal, ofReal_div_Pψ]
      refine le_trans ?_ (hexp u)
      exact mul_le_mul_of_nonneg_left (hLβ.logDeriv_sub_le _ _ (hstrip u hu))
        (inv_nonneg.mpr hp.le)
    · rw [deriv_logDeriv_besselWeightψ, deriv_logDeriv_besselWeightψ, ← mul_sub, ← mul_sub,
        norm_mul, norm_mul, norm_Pψ_inv, Generic.add_mul_I_div_ofReal, ofReal_div_Pψ]
      refine le_trans ?_ (hexp u)
      have hb := hLβ.deriv_logDeriv_sub_le (t / (2 * π)) (u / (2 * π)) (hstrip u hu)
      have hinv := two_pi_inv_le_one
      have hinv0 : 0 ≤ (2 * π)⁻¹ := inv_nonneg.mpr hp.le
      calc (2 * π)⁻¹ * ((2 * π)⁻¹ *
            ‖deriv (logDeriv (besselInterp β)) (((t / (2 * π) : ℝ) : ℂ) +
              ((u / (2 * π) : ℝ) : ℂ) * I) -
              deriv (logDeriv (besselInterp β)) ((t / (2 * π) : ℝ) : ℂ)‖)
          ≤ (2 * π)⁻¹ * (1 * ‖deriv (logDeriv (besselInterp β)) (((t / (2 * π) : ℝ) : ℂ) +
              ((u / (2 * π) : ℝ) : ℂ) * I) -
              deriv (logDeriv (besselInterp β)) ((t / (2 * π) : ℝ) : ℂ)‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hinv (norm_nonneg _)) hinv0
        _ ≤ (2 * π)⁻¹ * (C₂ / β * Real.exp (2 * π * |u / (2 * π)|)) := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_left hb hinv0
  · -- the curvature bound
    intro t s
    have hKβ := hK β hβ3 (t / (2 * π)) (s / (2 * π))
    have hval : ∀ r : ℝ, besselWeightψ β (r : ℂ) = besselInterp β ((r / (2 * π) : ℝ) : ℂ) :=
      fun r => by rw [besselWeightψ_apply, ofReal_div_Pψ]
    have hld : (logDeriv (besselWeightψ β) (t : ℂ)).re =
        (2 * π)⁻¹ * (logDeriv (besselInterp β) ((t / (2 * π) : ℝ) : ℂ)).re := by
      rw [logDeriv_besselWeightψ]
      simp only
      rw [ofReal_div_Pψ, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
    rw [hval, hval, hld]
    have hts : (t + s) / (2 * π) = t / (2 * π) + s / (2 * π) := add_div t s (2 * π)
    rw [hts]
    refine le_trans ?_ hKβ
    have hcurv : C₃ / β * (s / (2 * π)) ^ 2 ≤ C / β * s ^ 2 := by
      have hsq : (s / (2 * π)) ^ 2 ≤ s ^ 2 := by
        rw [div_pow]
        refine div_le_self (sq_nonneg s) ?_
        nlinarith
      exact mul_le_mul (div_le_div_of_nonneg_right hC3 hβpos.le) hsq (sq_nonneg _)
        (div_nonneg hCpos.le hβpos.le)
    have hlin : (2 * π)⁻¹ * (logDeriv (besselInterp β) ((t / (2 * π) : ℝ) : ℂ)).re * s =
        (logDeriv (besselInterp β) ((t / (2 * π) : ℝ) : ℂ)).re * (s / (2 * π)) := by
      field_simp
    rw [hlin]
    linarith

end FroehlichSpencer.BKT.Rotator.TheoremC

end
