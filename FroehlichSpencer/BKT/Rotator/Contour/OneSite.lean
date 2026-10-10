/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Contour.Factor
public import FroehlichSpencer.BKT.Rotator.Contour.LineShift
import FroehlichSpencer.BKT.Rotator.Contour.StripBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral

/-!
# The one-site contour step for the Bessel-interpolation edge weights

The integrand in the remaining variable `z`
is a character `e^{iqz}` times the incident edge weights `I_β(σ_e z + c_e)`, with orientation signs
`|σ_e| ≤ 1` and real offsets `c_e` (FS81 (4.15), J p.554, with the Gaussian replaced by the
interpolation `I_β` of Appendix B, as in §6).

If some incident edge has `σ_{e₀} ≠ 0`, the integrand
is holomorphic on the strip and dominated on every horizontal line `|Im z| ≤ |t| ≤ β/2` by
`e^{|q||t|} C^{|S|} e^{-|σ_{e₀}x + c_{e₀}|}`.

Hence the contour may be shifted from `ℝ` to
`ℝ + it`:

`∫ e^{iqx} ∏ I_β(σ_e x + c_e) dx = ∫ e^{iq(x+it)} ∏ I_β(σ_e(x+it) + c_e) dx`.

Reweighting by the normalized factors `i_β(σ_e t; ·)` of FS81 (6.19) then gives the
non-Gaussian form of FS81 (4.15):
`∫ e^{iqx} ∏ I_β(σ_e x + c_e) dx = e^{-qt} e^{Σ g(σ_e t)/β} ∫ e^{iqx} ∏ i_β(σ_e t; σ_e x + c_e)
I_β(σ_e x + c_e) dx`.
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Contour

open Complex MeasureTheory Filter Topology
open scoped Real
open FroehlichSpencer.BKT.Rotator.BesselInterp

/-- One-site integrand: a character times the incident edge weights `I_β(σ_e z + c_e)`. -/
@[expose] def siteIntegrand (β q : ℝ) {ι : Type*} (S : Finset ι) (σ c : ι → ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * q * z) * ∏ e ∈ S, besselInterp β (σ e * z + c e)

lemma integrable_exp_neg_abs : Integrable fun x : ℝ => Real.exp (-|x|) := by
  refine (integrable_inv_one_add_sq.const_mul 2).mono'
    (by fun_prop : Continuous fun x : ℝ => Real.exp (-|x|)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_neg_abs_le x

lemma integrable_exp_neg_abs_affine {σ c : ℝ} (hσ : σ ≠ 0) :
    Integrable fun x : ℝ => Real.exp (-|σ * x + c|) :=
  (integrable_exp_neg_abs.comp_add_right c).comp_mul_left' hσ

lemma tendsto_exp_neg_abs_affine {σ c : ℝ} (hσ : σ ≠ 0) :
    Tendsto (fun x : ℝ => Real.exp (-|σ * x + c|)) (cocompact ℝ) (𝓝 0) := by
  have hnorm : Tendsto (fun x : ℝ => |x|) (cocompact ℝ) atTop := by
    have h : Tendsto (norm : ℝ → ℝ) (cocompact ℝ) atTop := tendsto_norm_cocompact_atTop
    exact h.congr fun x => Real.norm_eq_abs x
  have hlow : Tendsto (fun x : ℝ => |σ| * |x| - |c|) (cocompact ℝ) atTop :=
    tendsto_atTop_add_const_right _ _ (hnorm.const_mul_atTop (abs_pos.mpr hσ))
  have habs : Tendsto (fun x : ℝ => |σ * x + c|) (cocompact ℝ) atTop := by
    refine tendsto_atTop_mono (fun x => ?_) hlow
    have h1 := abs_add_le (σ * x + c) (-c)
    rw [add_neg_cancel_right, abs_neg, abs_mul] at h1
    linarith
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp habs)

lemma affine_add_mul_I (σ c x y : ℝ) :
    (σ : ℂ) * ((x : ℂ) + y * I) + c = ((σ * x + c : ℝ) : ℂ) + ((σ * y : ℝ) : ℂ) * I := by
  push_cast; ring

lemma norm_cexp_I_mul_le (q t x y : ℝ) (hy : |y| ≤ |t|) :
    ‖Complex.exp (I * q * ((x : ℂ) + y * I))‖ ≤ Real.exp (|q| * |t|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have : (I * q * ((x : ℂ) + y * I)).re = -(q * y) := by simp
  rw [this]
  calc -(q * y) ≤ |q * y| := neg_le_abs _
    _ = |q| * |y| := abs_mul q y
    _ ≤ |q| * |t| := mul_le_mul_of_nonneg_left hy (abs_nonneg q)

/-- The domination of the one-site integrand on the horizontal lines `|Im z| ≤ |t|`. -/
theorem exists_siteIntegrand_majorant {β : ℝ} (hβ : 1 ≤ β) (q : ℝ) {ι : Type*}
    (S : Finset ι) (σ c : ι → ℝ) (hσ : ∀ e ∈ S, |σ e| ≤ 1) {e₀ : ι} (he₀ : e₀ ∈ S)
    (hσ₀ : σ e₀ ≠ 0) {t : ℝ} (ht : |t| ≤ β / 2) :
    ∃ B : ℝ → ℝ, Integrable B ∧ Tendsto B (cocompact ℝ) (𝓝 0) ∧
      ∀ x y : ℝ, |y| ≤ |t| → ‖siteIntegrand β q S σ c (x + y * I)‖ ≤ B x := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_norm_besselInterp_strip_le hβ
  set K := Real.exp (|q| * |t|) * C ^ S.card
  refine ⟨fun x => K * Real.exp (-|σ e₀ * x + c e₀|),
    (integrable_exp_neg_abs_affine hσ₀).const_mul K, ?_, fun x y hy => ?_⟩
  · simpa using (tendsto_exp_neg_abs_affine (c := c e₀) hσ₀).const_mul K
  unfold siteIntegrand
  rw [norm_mul, norm_prod]
  have hfac : ∀ e ∈ S, ‖besselInterp β (σ e * ((x : ℂ) + y * I) + c e)‖ ≤
      C * Real.exp (-|σ e * x + c e|) := by
    intro e he
    rw [affine_add_mul_I]
    refine hC _ _ ?_
    rw [abs_mul]
    calc |σ e| * |y| ≤ 1 * |t| := mul_le_mul (hσ e he) hy (abs_nonneg _) zero_le_one
      _ = |t| := one_mul _
      _ ≤ β / 2 := ht
  have hprod : ∏ e ∈ S, ‖besselInterp β (σ e * ((x : ℂ) + y * I) + c e)‖ ≤
      C ^ S.card * Real.exp (-|σ e₀ * x + c e₀|) := by
    calc ∏ e ∈ S, ‖besselInterp β (σ e * ((x : ℂ) + y * I) + c e)‖
        ≤ ∏ e ∈ S, C * Real.exp (-|σ e * x + c e|) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hfac
      _ = C ^ S.card * ∏ e ∈ S, Real.exp (-|σ e * x + c e|) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ C ^ S.card * Real.exp (-|σ e₀ * x + c e₀|) := by
          gcongr
          rw [← Finset.mul_prod_erase S _ he₀]
          refine mul_le_of_le_one_right (Real.exp_pos _).le ?_
          exact Finset.prod_le_one₀ (fun _ _ => (Real.exp_pos _).le)
            fun _ _ => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
  calc ‖Complex.exp (I * q * ((x : ℂ) + y * I))‖ *
        ∏ e ∈ S, ‖besselInterp β (σ e * ((x : ℂ) + y * I) + c e)‖
      ≤ Real.exp (|q| * |t|) * (C ^ S.card * Real.exp (-|σ e₀ * x + c e₀|)) :=
        mul_le_mul (norm_cexp_I_mul_le q t x y hy) hprod (by positivity) (Real.exp_pos _).le
    _ = K * Real.exp (-|σ e₀ * x + c e₀|) := by ring

theorem differentiableAt_siteIntegrand {β : ℝ} (hβ : 1 ≤ β) (q : ℝ) {ι : Type*}
    (S : Finset ι) (σ c : ι → ℝ) (hσ : ∀ e ∈ S, |σ e| ≤ 1) {t : ℝ} (ht : |t| ≤ β / 2)
    {z : ℂ} (hz : |z.im| ≤ |t|) : DifferentiableAt ℂ (siteIntegrand β q S σ c) z := by
  have hβ0 : 0 < β := by linarith
  unfold siteIntegrand
  refine ((differentiableAt_id.const_mul _).cexp).mul (DifferentiableAt.fun_finsetProd ?_)
  intro e he
  have hzim : |((σ e : ℂ) * z + c e).im| < β := by
    have : ((σ e : ℂ) * z + c e).im = σ e * z.im := by simp
    rw [this, abs_mul]
    calc |σ e| * |z.im| ≤ 1 * |t| := mul_le_mul (hσ e he) hz (abs_nonneg _) zero_le_one
      _ = |t| := one_mul _
      _ < β := by linarith
  exact (differentiableAt_besselInterp hβ0 hzim).comp z
    ((differentiableAt_id.const_mul _).add_const _)

theorem integrable_siteIntegrand_add_mul_I {β : ℝ} (hβ : 1 ≤ β) (q : ℝ) {ι : Type*}
    (S : Finset ι) (σ c : ι → ℝ) (hσ : ∀ e ∈ S, |σ e| ≤ 1) {e₀ : ι} (he₀ : e₀ ∈ S)
    (hσ₀ : σ e₀ ≠ 0) {t : ℝ} (ht : |t| ≤ β / 2) :
    MeasureTheory.Integrable fun x : ℝ => siteIntegrand β q S σ c (x + t * Complex.I) := by
  obtain ⟨B, hB, -, hdom⟩ := exists_siteIntegrand_majorant hβ q S σ c hσ he₀ hσ₀ ht
  exact integrable_comp_add_mul_I (fun z hz => differentiableAt_siteIntegrand hβ q S σ c hσ ht hz)
    hB hdom le_rfl

/-- The one-site contour identity: the real line may be replaced by `ℝ + it`, `|t| ≤ β/2`. -/
theorem integral_siteIntegrand_shift {β : ℝ} (hβ : 1 ≤ β) (q : ℝ) {ι : Type*}
    (S : Finset ι) (σ c : ι → ℝ) (hσ : ∀ e ∈ S, |σ e| ≤ 1) {e₀ : ι} (he₀ : e₀ ∈ S)
    (hσ₀ : σ e₀ ≠ 0) {t : ℝ} (ht : |t| ≤ β / 2) :
    ∫ x : ℝ, siteIntegrand β q S σ c x = ∫ x : ℝ, siteIntegrand β q S σ c (x + t * Complex.I) := by
  obtain ⟨B, hB, hBlim, hdom⟩ := exists_siteIntegrand_majorant hβ q S σ c hσ he₀ hσ₀ ht
  exact integral_eq_integral_add_mul_I
    (fun z hz => differentiableAt_siteIntegrand hβ q S σ c hσ ht hz) hB hBlim hdom

/-- The shifted integrand, written with the character gain, the envelope cost and the normalized
factors. -/
theorem siteIntegrand_add_mul_I_eq {β C : ℝ} (hβ : 0 < β) (q : ℝ) {ι : Type*}
    (S : Finset ι) (σ c : ι → ℝ) (t x : ℝ) :
    siteIntegrand β q S σ c (x + t * I) =
      (Complex.exp (-((q * t : ℝ) : ℂ)) *
        Complex.exp (((∑ e ∈ S, cEnvelope C (σ e * t) / β : ℝ)) : ℂ)) *
        (Complex.exp (I * q * x) *
          (∏ e ∈ S, normalizedFactor β C (σ e * t) (σ e * x + c e)) *
          ∏ e ∈ S, besselInterp β (σ e * x + c e)) := by
  unfold siteIntegrand
  rw [character_shift]
  have hne : ∀ e ∈ S, besselInterp β ((σ e : ℂ) * x + c e) ≠ 0 := fun e _ =>
    besselInterp_ne_zero hβ (by simpa using hβ)
  have hprod := prod_besselInterp_add_mul_I_eq S (β := β) (C := C) (fun e => σ e * t)
    (fun e => (σ e : ℂ) * x + c e) hne
  have hl : ∏ e ∈ S, besselInterp β (σ e * ((x : ℂ) + t * I) + c e) =
      ∏ e ∈ S, besselInterp β (((σ e : ℂ) * x + c e) + ((σ e * t : ℝ) : ℂ) * I) :=
    Finset.prod_congr rfl fun e _ => by congr 1; push_cast; ring
  rw [hl, hprod]
  ring

/-- FS81 (4.15) for the non-Gaussian weight: the one-site contour step in normalized form. -/
theorem integral_siteIntegrand_eq_normalized {β C : ℝ} (hβ : 1 ≤ β) (q : ℝ) {ι : Type*}
    (S : Finset ι) (σ c : ι → ℝ) (hσ : ∀ e ∈ S, |σ e| ≤ 1) {e₀ : ι} (he₀ : e₀ ∈ S)
    (hσ₀ : σ e₀ ≠ 0) {t : ℝ} (ht : |t| ≤ β / 2) :
    ∫ x : ℝ, siteIntegrand β q S σ c x =
      Complex.exp (-((q * t : ℝ) : ℂ)) *
        Complex.exp (((∑ e ∈ S, cEnvelope C (σ e * t) / β : ℝ)) : ℂ) *
        ∫ x : ℝ, Complex.exp (Complex.I * q * x) *
          (∏ e ∈ S, normalizedFactor β C (σ e * t) (σ e * x + c e)) *
          ∏ e ∈ S, besselInterp β (σ e * x + c e) := by
  rw [integral_siteIntegrand_shift hβ q S σ c hσ he₀ hσ₀ ht, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun x =>
    siteIntegrand_add_mul_I_eq (C := C) (by linarith) q S σ c t x)

lemma norm_cexp_I_mul_ofReal (q x : ℝ) : ‖Complex.exp (I * q * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- The one-site contour bound: given the envelope bound (c) for the shifted incident edges, the
one-site integral is at most `e^{-qt} e^{Σ g(σ_e t)/β} ∫ ∏ |I_β(σ_e x + c_e)| dx`. -/
theorem norm_integral_siteIntegrand_le {β C : ℝ} (hβ : 1 ≤ β) (q : ℝ) {ι : Type*}
    (S : Finset ι) (σ c : ι → ℝ) (hσ : ∀ e ∈ S, |σ e| ≤ 1) {e₀ : ι} (he₀ : e₀ ∈ S)
    (hσ₀ : σ e₀ ≠ 0) {t : ℝ} (ht : |t| ≤ β / 2)
    (hc : ∀ e ∈ S, ∀ u : ℝ, ‖besselInterp β ((u : ℂ) + ((σ e * t : ℝ) : ℂ) * I) /
      besselInterp β u‖ ≤ Real.exp (cEnvelope C (σ e * t) / β)) :
    ‖∫ x : ℝ, siteIntegrand β q S σ c x‖ ≤
      Real.exp (-(q * t)) * Real.exp (∑ e ∈ S, cEnvelope C (σ e * t) / β) *
        ∫ x : ℝ, ∏ e ∈ S, ‖besselInterp β (σ e * x + c e)‖ := by
  rw [integral_siteIntegrand_eq_normalized (C := C) hβ q S σ c hσ he₀ hσ₀ ht, norm_mul, norm_mul,
    Complex.norm_exp, Complex.norm_exp]
  simp only [neg_re, ofReal_re]
  have h0 : |(0 : ℝ)| ≤ β / 2 := by rw [abs_zero]; linarith
  have hI := (integrable_siteIntegrand_add_mul_I hβ q S σ c hσ he₀ hσ₀ h0).norm
  have hg : Integrable fun x : ℝ => ∏ e ∈ S, ‖besselInterp β (σ e * x + c e)‖ := by
    refine hI.congr (Eventually.of_forall fun x => ?_)
    simp only [siteIntegrand, ofReal_zero, zero_mul, add_zero, norm_mul, norm_prod,
      norm_cexp_I_mul_ofReal, one_mul]
  gcongr
  refine norm_integral_le_of_norm_le hg (Eventually.of_forall fun x => ?_)
  have h1 := norm_prod_normalizedFactor_le_one S (β := β) (C := C) (fun e => σ e * t)
    (fun e => σ e * x + c e) (fun e he => hc e he _)
  push_cast at h1
  rw [norm_mul, norm_mul, norm_cexp_I_mul_ofReal, one_mul]
  calc ‖∏ e ∈ S, normalizedFactor β C (σ e * t) (σ e * x + c e)‖ *
        ‖∏ e ∈ S, besselInterp β (σ e * x + c e)‖
      ≤ 1 * ‖∏ e ∈ S, besselInterp β (σ e * x + c e)‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ∏ e ∈ S, ‖besselInterp β (σ e * x + c e)‖ := by rw [one_mul, norm_prod]

end FroehlichSpencer.BKT.Rotator.Contour
