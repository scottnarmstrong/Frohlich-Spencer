/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.BesselInterp.Properties

/-!
# The normalized edge factor `i_β(a; φ)` of FS81 (6.19)

Property (c) of the interpolation (J p.576, proved as `norm_besselInterp_translate_div_le`) bounds
the translation ratio `I_β(φ + ia)/I_β(φ)` by `e^{g(a)/β}` with the envelope
`g(a) = C a²` for `|a| ≤ 1` and `g(a) = C e^{2π|a|}` for `|a| > 1` (`cEnvelope`). The normalized
factor `i_β(a; φ) = I_β(φ + ia) I_β(φ)⁻¹ e^{-g(a)/β}` of (6.19) then has modulus at most one
(FS81 (6.21)), and a finite product of translated weights factors as
`∏ I_β(x_e + i a_e) = e^{Σ g(a_e)/β} ∏ i_β(a_e; x_e) ∏ I_β(x_e)`. A one-site imaginary translation
of a character contributes `e^{-qt}` (FS81 (4.15)).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Contour

open Complex
open scoped Real
open FroehlichSpencer.BKT.Rotator.BesselInterp

/-- The envelope `g(a)` of property (c): `C a²` for `|a| ≤ 1`, `C e^{2π|a|}` otherwise. -/
def cEnvelope (C a : ℝ) : ℝ := if |a| ≤ 1 then C * a ^ 2 else C * Real.exp (2 * π * |a|)

/-- FS81 (6.19): `i_β(a; z) = I_β(z + ia) I_β(z)⁻¹ e^{-g(a)/β}`. -/
def normalizedFactor (β C a : ℝ) (z : ℂ) : ℂ :=
  besselInterp β (z + a * I) / besselInterp β z * Complex.exp (-((cEnvelope C a / β : ℝ) : ℂ))

lemma cEnvelope_nonneg {C : ℝ} (hC : 0 ≤ C) (a : ℝ) : 0 ≤ cEnvelope C a := by
  unfold cEnvelope; split_ifs <;> positivity

lemma cEnvelope_neg (C a : ℝ) : cEnvelope C (-a) = cEnvelope C a := by
  unfold cEnvelope; rw [abs_neg, neg_sq]

/-- Property (c) in the envelope form: constants `β₀`, `C` such that
`‖I_β(φ + ia)/I_β(φ)‖ ≤ e^{g(a)/β}` for `β ≥ β₀`, real `φ`, `|a| ≤ β/2`. -/
theorem exists_translation_envelope :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 ≤ C ∧ ∀ β : ℝ, β₀ ≤ β → ∀ φ a : ℝ, |a| ≤ β / 2 →
      ‖besselInterp β (φ + a * I) / besselInterp β φ‖ ≤ Real.exp (cEnvelope C a / β) := by
  obtain ⟨β₀, C, hβ₀, hC, h⟩ := norm_besselInterp_translate_div_le
  exact ⟨β₀, C, hβ₀, hC, fun β hβ φ a ha => by unfold cEnvelope; exact h β hβ φ a ha⟩

lemma norm_cexp_neg_ofReal (r : ℝ) : ‖Complex.exp (-((r : ℝ) : ℂ))‖ = Real.exp (-r) := by
  rw [Complex.norm_exp]; simp

/-- FS81 (6.21): `‖i_β(a; x)‖ ≤ 1`, given the envelope bound (c) at `(x, a)`. -/
theorem norm_normalizedFactor_le_one {β C a x : ℝ}
    (hc : ‖besselInterp β (x + a * I) / besselInterp β x‖ ≤ Real.exp (cEnvelope C a / β)) :
    ‖normalizedFactor β C a x‖ ≤ 1 := by
  unfold normalizedFactor
  rw [norm_mul, norm_cexp_neg_ofReal]
  calc ‖besselInterp β (x + a * I) / besselInterp β x‖ * Real.exp (-(cEnvelope C a / β))
      ≤ Real.exp (cEnvelope C a / β) * Real.exp (-(cEnvelope C a / β)) :=
        mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- The translated weight is the envelope factor times the normalized factor times the weight. -/
theorem besselInterp_add_mul_I_eq {β C a : ℝ} {z : ℂ} (hz : besselInterp β z ≠ 0) :
    besselInterp β (z + a * I) =
      Complex.exp ((cEnvelope C a / β : ℝ) : ℂ) * normalizedFactor β C a z * besselInterp β z := by
  unfold normalizedFactor
  have h1 : Complex.exp ((cEnvelope C a / β : ℝ) : ℂ) *
      Complex.exp (-((cEnvelope C a / β : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  calc besselInterp β (z + a * I)
      = besselInterp β (z + a * I) / besselInterp β z * besselInterp β z *
          (Complex.exp ((cEnvelope C a / β : ℝ) : ℂ) *
            Complex.exp (-((cEnvelope C a / β : ℝ) : ℂ))) := by
        rw [h1, mul_one, div_mul_cancel₀ _ hz]
    _ = _ := by ring

/-- The finite-product reweighting identity behind the contour steps:
`∏ I_β(x_e + i a_e) = e^{Σ g(a_e)/β} ∏ i_β(a_e; x_e) ∏ I_β(x_e)`. -/
theorem prod_besselInterp_add_mul_I_eq {ι : Type*} (S : Finset ι) {β C : ℝ} (a : ι → ℝ)
    (z : ι → ℂ) (hz : ∀ e ∈ S, besselInterp β (z e) ≠ 0) :
    ∏ e ∈ S, besselInterp β (z e + a e * I) =
      Complex.exp (((∑ e ∈ S, cEnvelope C (a e) / β : ℝ)) : ℂ) *
        (∏ e ∈ S, normalizedFactor β C (a e) (z e)) * ∏ e ∈ S, besselInterp β (z e) := by
  rw [Finset.prod_congr rfl fun e he => besselInterp_add_mul_I_eq (C := C) (a := a e) (hz e he),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib, Complex.ofReal_sum, Complex.exp_sum]

/-- The product of edge ratios is bounded by the exponential of the summed envelope costs. -/
theorem norm_prod_ratio_le {ι : Type*} (S : Finset ι) {β C : ℝ} (a x : ι → ℝ)
    (hc : ∀ e ∈ S, ‖besselInterp β (x e + a e * I) / besselInterp β (x e)‖ ≤
      Real.exp (cEnvelope C (a e) / β)) :
    ‖∏ e ∈ S, besselInterp β (x e + a e * I) / besselInterp β (x e)‖ ≤
      Real.exp (∑ e ∈ S, cEnvelope C (a e) / β) := by
  rw [norm_prod, Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hc

/-- A product of normalized factors has modulus at most one. -/
theorem norm_prod_normalizedFactor_le_one {ι : Type*} (S : Finset ι) {β C : ℝ} (a x : ι → ℝ)
    (hc : ∀ e ∈ S, ‖besselInterp β (x e + a e * I) / besselInterp β (x e)‖ ≤
      Real.exp (cEnvelope C (a e) / β)) :
    ‖∏ e ∈ S, normalizedFactor β C (a e) (x e)‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    fun e he => norm_normalizedFactor_le_one (hc e he)

/-- FS81 (4.15), the character factor: `e^{iq(x + it)} = e^{-qt} e^{iqx}`. -/
theorem character_shift (q t : ℝ) (z : ℂ) :
    Complex.exp (I * q * (z + t * I)) = Complex.exp (-((q * t : ℝ) : ℂ)) * Complex.exp (I * q * z) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

end FroehlichSpencer.BKT.Rotator.Contour
