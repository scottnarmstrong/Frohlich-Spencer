/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Contour.LocalFactor

/-!
# The local functionals `F₁`, `F₂` of FS81 (6.18) and their derivative bounds

FS81 (6.18), J p.579: `i^{n-2} 2 F_n = ∏ i_β(∂a; ∂φ) + (-1)^n ∏ i_β(-∂a; ∂φ)`, a combination of two
finite products of normalized edge factors (6.19). Along a line `∇φ + λθ` each product is
`exp (Σ_e ψ_e)` on the strip, so its first and second `λ`-derivatives are
`(Σ_e θ_e L'_e) P` and `((Σ_e θ_e L'_e)² + Σ_e θ_e² L''_e) P`, where `L'_e`, `L''_e` are the
logarithmic-derivative differences of (6.22). With `‖i_β‖ ≤ 1` (6.21) and property (d), this
gives Theorem 6.1 (3) and (4) for the local functionals (J pp.579–581): `‖F_n‖ ≤ 1`,
`‖∂_λ F_n‖ ≤ N M T` and `‖∂²_λ F_n‖ ≤ 2 N² M T²` with `N` the number of factors, `T` the size of
`θ` and `M = C_d β⁻¹ e^{2πA} ≤ 1` (FS81 (6.25)).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Contour

open Complex
open scoped Real
open FroehlichSpencer.BKT.Rotator.BesselInterp

section Defs

variable {ι : Type*}

/-- `λ ↦ ∏_e i_β(a_e; x_e + λθ_e)`. -/
def edgeProduct (β C : ℝ) (S : Finset ι) (a x θ : ι → ℝ) (μ : ℝ) : ℂ :=
  ∏ e ∈ S, normalizedFactor β C (a e) (x e + μ * θ e)

/-- `Σ_e θ_e L'_e(x_e + λθ_e)`, the logarithmic derivative of `edgeProduct`. -/
def edgeLogDeriv (β : ℝ) (S : Finset ι) (a x θ : ι → ℝ) (μ : ℝ) : ℂ :=
  ∑ e ∈ S, (θ e : ℂ) * ratioLogDeriv β (a e) (x e + μ * θ e)

/-- `Σ_e θ_e² L''_e(x_e + λθ_e)`. -/
def edgeLogDeriv2 (β : ℝ) (S : Finset ι) (a x θ : ι → ℝ) (μ : ℝ) : ℂ :=
  ∑ e ∈ S, (θ e : ℂ) ^ 2 * ratioLogDeriv2 β (a e) (x e + μ * θ e)

/-- FS81 (6.18) with `n = 1`: `i⁻¹ · 2 F₁ = P₊ − P₋`, i.e. `F₁ = i (P₊ − P₋)/2`. -/
def localF₁ (β C : ℝ) (S : Finset ι) (a x θ : ι → ℝ) (μ : ℝ) : ℂ :=
  Complex.I * (edgeProduct β C S a x θ μ - edgeProduct β C S (-a) x θ μ) / 2

/-- FS81 (6.18) with `n = 2`: `2 F₂ = P₊ + P₋`. -/
def localF₂ (β C : ℝ) (S : Finset ι) (a x θ : ι → ℝ) (μ : ℝ) : ℂ :=
  (edgeProduct β C S a x θ μ + edgeProduct β C S (-a) x θ μ) / 2

end Defs

section Calculus

variable {ι : Type*} {β C : ℝ} (S : Finset ι) (a x θ : ι → ℝ)

theorem edgeProduct_eq_exp (hβ : 0 < β) (ha : ∀ e ∈ S, |a e| ≤ β / 2) (μ : ℝ) :
    edgeProduct β C S a x θ μ =
      Complex.exp (∑ e ∈ S, factorLog β C (a e) (x e + μ * θ e)) := by
  unfold edgeProduct
  rw [Complex.exp_sum]
  exact Finset.prod_congr rfl fun e he =>
    normalizedFactor_eq_exp hβ (ha e he) (abs_im_line_lt hβ _ _ _)

theorem hasDerivAt_edgeProduct (hβ : 0 < β) (ha : ∀ e ∈ S, |a e| ≤ β / 2) (μ₀ : ℝ) :
    HasDerivAt (edgeProduct β C S a x θ)
      (edgeLogDeriv β S a x θ μ₀ * edgeProduct β C S a x θ μ₀) μ₀ := by
  have hQ : HasDerivAt (fun μ : ℝ => ∑ e ∈ S, factorLog β C (a e) (x e + μ * θ e))
      (edgeLogDeriv β S a x θ μ₀) μ₀ := by
    unfold edgeLogDeriv
    exact HasDerivAt.fun_sum fun e he =>
      hasDerivAt_line (hasDerivAt_factorLog hβ (ha e he) (abs_im_line_lt hβ _ _ _))
  have hfun : edgeProduct β C S a x θ =
      fun μ : ℝ => Complex.exp (∑ e ∈ S, factorLog β C (a e) (x e + μ * θ e)) :=
    funext (edgeProduct_eq_exp S a x θ hβ ha)
  have h := hQ.cexp
  rw [← hfun, ← edgeProduct_eq_exp S a x θ hβ ha μ₀, mul_comm] at h
  exact h

theorem hasDerivAt_edgeLogDeriv (hβ : 0 < β) (ha : ∀ e ∈ S, |a e| ≤ β / 2) (μ₀ : ℝ) :
    HasDerivAt (edgeLogDeriv β S a x θ) (edgeLogDeriv2 β S a x θ μ₀) μ₀ := by
  unfold edgeLogDeriv edgeLogDeriv2
  refine HasDerivAt.fun_sum fun e he => ?_
  have h := (hasDerivAt_ratioLogDeriv_line hβ (ha e he) (x e) (θ e) μ₀).const_mul (θ e : ℂ)
  convert h using 1
  ring

theorem deriv_edgeProduct (hβ : 0 < β) (ha : ∀ e ∈ S, |a e| ≤ β / 2) :
    deriv (edgeProduct β C S a x θ) =
      fun μ : ℝ => edgeLogDeriv β S a x θ μ * edgeProduct β C S a x θ μ :=
  funext fun μ => (hasDerivAt_edgeProduct S a x θ hβ ha μ).deriv

theorem hasDerivAt_deriv_edgeProduct (hβ : 0 < β) (ha : ∀ e ∈ S, |a e| ≤ β / 2) (μ₀ : ℝ) :
    HasDerivAt (deriv (edgeProduct β C S a x θ))
      ((edgeLogDeriv β S a x θ μ₀ ^ 2 + edgeLogDeriv2 β S a x θ μ₀) *
        edgeProduct β C S a x θ μ₀) μ₀ := by
  rw [deriv_edgeProduct S a x θ hβ ha]
  have h := (hasDerivAt_edgeLogDeriv S a x θ hβ ha μ₀).mul
    (hasDerivAt_edgeProduct (C := C) S a x θ hβ ha μ₀)
  convert h using 1
  ring

end Calculus

section Bounds

variable {ι : Type*} {β C : ℝ} (S : Finset ι) (a x θ : ι → ℝ)

lemma line_coe (x θ μ : ℝ) : ((x + μ * θ : ℝ) : ℂ) = (x : ℂ) + μ * θ := by push_cast; ring

theorem norm_edgeProduct_le_one (μ : ℝ)
    (hc : ∀ e ∈ S, ‖besselInterp β ((x e + μ * θ e : ℝ) + a e * Complex.I) /
      besselInterp β ((x e + μ * θ e : ℝ) : ℂ)‖ ≤ Real.exp (cEnvelope C (a e) / β)) :
    ‖edgeProduct β C S a x θ μ‖ ≤ 1 := by
  have h := norm_prod_normalizedFactor_le_one S a (fun e => x e + μ * θ e) hc
  unfold edgeProduct
  simpa only [line_coe] using h

theorem norm_edgeLogDeriv_le {M T : ℝ} (μ : ℝ)
    (hd : ∀ e ∈ S, ‖ratioLogDeriv β (a e) (x e + μ * θ e)‖ ≤ M)
    (hθ : ∀ e ∈ S, |θ e| ≤ T) :
    ‖edgeLogDeriv β S a x θ μ‖ ≤ S.card * M * T := by
  unfold edgeLogDeriv
  refine (norm_sum_le _ _).trans ?_
  calc ∑ e ∈ S, ‖(θ e : ℂ) * ratioLogDeriv β (a e) (x e + μ * θ e)‖
      ≤ ∑ _e ∈ S, M * T := Finset.sum_le_sum fun e he => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul (hd e he) (hθ e he) (abs_nonneg _) ((norm_nonneg _).trans (hd e he))
    _ = S.card * M * T := by rw [Finset.sum_const, nsmul_eq_mul]; ring

theorem norm_edgeLogDeriv2_le {M T : ℝ} (μ : ℝ)
    (hd : ∀ e ∈ S, ‖ratioLogDeriv2 β (a e) (x e + μ * θ e)‖ ≤ M)
    (hθ : ∀ e ∈ S, |θ e| ≤ T) :
    ‖edgeLogDeriv2 β S a x θ μ‖ ≤ S.card * M * T ^ 2 := by
  unfold edgeLogDeriv2
  refine (norm_sum_le _ _).trans ?_
  calc ∑ e ∈ S, ‖(θ e : ℂ) ^ 2 * ratioLogDeriv2 β (a e) (x e + μ * θ e)‖
      ≤ ∑ _e ∈ S, M * T ^ 2 := Finset.sum_le_sum fun e he => by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_comm]
        have hT : θ e ^ 2 ≤ T ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hθ e he) 2
        exact mul_le_mul (hd e he) hT (sq_nonneg _) ((norm_nonneg _).trans (hd e he))
    _ = S.card * M * T ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- One product: `‖P‖ ≤ 1`, `‖P'‖ ≤ N M T`, `‖P''‖ ≤ 2 N² M T²` when `0 ≤ M ≤ 1`. -/
theorem edgeProduct_bounds {M T : ℝ} (hβ : 0 < β) (ha : ∀ e ∈ S, |a e| ≤ β / 2)
    (hM0 : 0 ≤ M) (hM1 : M ≤ 1) (μ : ℝ)
    (hc : ∀ e ∈ S, ‖besselInterp β ((x e + μ * θ e : ℝ) + a e * Complex.I) /
      besselInterp β ((x e + μ * θ e : ℝ) : ℂ)‖ ≤ Real.exp (cEnvelope C (a e) / β))
    (hd : ∀ e ∈ S, ‖ratioLogDeriv β (a e) (x e + μ * θ e)‖ ≤ M)
    (hd2 : ∀ e ∈ S, ‖ratioLogDeriv2 β (a e) (x e + μ * θ e)‖ ≤ M)
    (hθ : ∀ e ∈ S, |θ e| ≤ T) :
    ‖edgeProduct β C S a x θ μ‖ ≤ 1 ∧
      ‖deriv (edgeProduct β C S a x θ) μ‖ ≤ S.card * M * T ∧
      ‖deriv (deriv (edgeProduct β C S a x θ)) μ‖ ≤ 2 * S.card ^ 2 * M * T ^ 2 := by
  have hP := norm_edgeProduct_le_one S a x θ μ hc
  have hQ := norm_edgeLogDeriv_le S a x θ μ hd hθ
  have hQ2 := norm_edgeLogDeriv2_le S a x θ μ hd2 hθ
  have hN : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  refine ⟨hP, ?_, ?_⟩
  · rw [(hasDerivAt_edgeProduct (C := C) S a x θ hβ ha μ).deriv, norm_mul]
    calc ‖edgeLogDeriv β S a x θ μ‖ * ‖edgeProduct β C S a x θ μ‖ ≤ (S.card * M * T) * 1 :=
          mul_le_mul hQ hP (norm_nonneg _) ((norm_nonneg _).trans hQ)
      _ = S.card * M * T := mul_one _
  · rw [(hasDerivAt_deriv_edgeProduct (C := C) S a x θ hβ ha μ).deriv, norm_mul]
    have hsq : ‖edgeLogDeriv β S a x θ μ‖ ^ 2 ≤ (S.card * M * T) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hQ 2
    have hMM : M ^ 2 ≤ M := by nlinarith
    have hNN : (S.card : ℝ) ≤ S.card ^ 2 := by
      rcases Nat.eq_zero_or_pos S.card with h0 | hpos
      · rw [h0]; norm_num
      · have : (1 : ℝ) ≤ S.card := by exact_mod_cast hpos
        nlinarith
    have hT2 : 0 ≤ T ^ 2 := sq_nonneg T
    have key : (S.card * M * T) ^ 2 + S.card * M * T ^ 2 ≤ 2 * S.card ^ 2 * M * T ^ 2 := by
      have h1 : (S.card * M * T) ^ 2 = S.card ^ 2 * T ^ 2 * M ^ 2 := by ring
      have h2 : S.card ^ 2 * T ^ 2 * M ^ 2 ≤ S.card ^ 2 * T ^ 2 * M :=
        mul_le_mul_of_nonneg_left hMM (by positivity)
      have h3 : (S.card : ℝ) * M * T ^ 2 ≤ S.card ^ 2 * M * T ^ 2 := by
        have := mul_le_mul_of_nonneg_right hNN (mul_nonneg hM0 hT2)
        linarith [this]
      nlinarith
    calc ‖edgeLogDeriv β S a x θ μ ^ 2 + edgeLogDeriv2 β S a x θ μ‖ *
          ‖edgeProduct β C S a x θ μ‖
        ≤ ((S.card * M * T) ^ 2 + S.card * M * T ^ 2) * 1 := by
          refine mul_le_mul ?_ hP (norm_nonneg _) (by positivity)
          refine (norm_add_le _ _).trans ?_
          rw [norm_pow]
          exact add_le_add hsq hQ2
      _ ≤ 2 * S.card ^ 2 * M * T ^ 2 := by rw [mul_one]; exact key

end Bounds

section LocalF

variable {ι : Type*} {β C : ℝ} (S : Finset ι) (a x θ : ι → ℝ)

lemma abs_neg_le {A : ℝ} (haA : ∀ e ∈ S, |a e| ≤ A) : ∀ e ∈ S, |(-a) e| ≤ A := fun e he => by
  rw [Pi.neg_apply, abs_neg]; exact haA e he

theorem hasDerivAt_localF₁ (hβ : 0 < β) (ha : ∀ e ∈ S, |a e| ≤ β / 2) (μ₀ : ℝ) :
    HasDerivAt (localF₁ β C S a x θ)
      (Complex.I * (deriv (edgeProduct β C S a x θ) μ₀ -
        deriv (edgeProduct β C S (-a) x θ) μ₀) / 2) μ₀ := by
  have hp := (hasDerivAt_edgeProduct (C := C) S a x θ hβ ha μ₀)
  have hm := (hasDerivAt_edgeProduct (C := C) S (-a) x θ hβ (abs_neg_le S a ha) μ₀)
  rw [hp.deriv, hm.deriv]
  exact ((hp.sub hm).const_mul Complex.I).div_const 2

theorem hasDerivAt_localF₂ (hβ : 0 < β) (ha : ∀ e ∈ S, |a e| ≤ β / 2) (μ₀ : ℝ) :
    HasDerivAt (localF₂ β C S a x θ)
      ((deriv (edgeProduct β C S a x θ) μ₀ + deriv (edgeProduct β C S (-a) x θ) μ₀) / 2) μ₀ := by
  have hp := (hasDerivAt_edgeProduct (C := C) S a x θ hβ ha μ₀)
  have hm := (hasDerivAt_edgeProduct (C := C) S (-a) x θ hβ (abs_neg_le S a ha) μ₀)
  rw [hp.deriv, hm.deriv]
  exact (hp.add hm).div_const 2

theorem deriv_localF₁ (hβ : 0 < β) (ha : ∀ e ∈ S, |a e| ≤ β / 2) :
    deriv (localF₁ β C S a x θ) = fun μ : ℝ =>
      Complex.I * (deriv (edgeProduct β C S a x θ) μ -
        deriv (edgeProduct β C S (-a) x θ) μ) / 2 :=
  funext fun μ => (hasDerivAt_localF₁ S a x θ hβ ha μ).deriv

theorem deriv_localF₂ (hβ : 0 < β) (ha : ∀ e ∈ S, |a e| ≤ β / 2) :
    deriv (localF₂ β C S a x θ) = fun μ : ℝ =>
      (deriv (edgeProduct β C S a x θ) μ + deriv (edgeProduct β C S (-a) x θ) μ) / 2 :=
  funext fun μ => (hasDerivAt_localF₂ S a x θ hβ ha μ).deriv

theorem deriv_deriv_localF₁ (hβ : 0 < β) (ha : ∀ e ∈ S, |a e| ≤ β / 2) (μ₀ : ℝ) :
    deriv (deriv (localF₁ β C S a x θ)) μ₀ =
      Complex.I * (deriv (deriv (edgeProduct β C S a x θ)) μ₀ -
        deriv (deriv (edgeProduct β C S (-a) x θ)) μ₀) / 2 := by
  rw [deriv_localF₁ S a x θ hβ ha]
  have hp := hasDerivAt_deriv_edgeProduct (C := C) S a x θ hβ ha μ₀
  have hm := hasDerivAt_deriv_edgeProduct (C := C) S (-a) x θ hβ (abs_neg_le S a ha) μ₀
  rw [hp.deriv, hm.deriv]
  exact (((hp.sub hm).const_mul Complex.I).div_const 2).deriv

theorem deriv_deriv_localF₂ (hβ : 0 < β) (ha : ∀ e ∈ S, |a e| ≤ β / 2) (μ₀ : ℝ) :
    deriv (deriv (localF₂ β C S a x θ)) μ₀ =
      (deriv (deriv (edgeProduct β C S a x θ)) μ₀ +
        deriv (deriv (edgeProduct β C S (-a) x θ)) μ₀) / 2 := by
  rw [deriv_localF₂ S a x θ hβ ha]
  have hp := hasDerivAt_deriv_edgeProduct (C := C) S a x θ hβ ha μ₀
  have hm := hasDerivAt_deriv_edgeProduct (C := C) S (-a) x θ hβ (abs_neg_le S a ha) μ₀
  rw [hp.deriv, hm.deriv]
  exact ((hp.add hm).div_const 2).deriv

lemma norm_I_mul_sub_div_two_le {B : ℝ} {u v : ℂ} (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B) :
    ‖Complex.I * (u - v) / 2‖ ≤ B := by
  rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_two]
  have := norm_sub_le u v
  linarith

lemma norm_add_div_two_le {B : ℝ} {u v : ℂ} (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B) :
    ‖(u + v) / 2‖ ≤ B := by
  rw [norm_div, Complex.norm_two]
  have := norm_add_le u v
  linarith

end LocalF

/-- FS81 Theorem 6.1 (3), (4) for the local functionals (6.18), J pp.579–581: there are constants
`β₀`, `C` (the envelope of property (c)) and `C_d` (property (d)) such that for `β ≥ β₀`, a finite
family of edges with increments `|a_e| ≤ A ≤ β/2`, line directions `|θ_e| ≤ T`, and
`M = C_d β⁻¹ e^{2πA} ≤ 1` (FS81 (6.25)): `‖F_n‖ ≤ 1`, `‖∂_λ F_n‖ ≤ N M T` and
`‖∂²_λ F_n‖ ≤ 2 N² M T²`, with `N = card S`. -/
theorem localF_bounds : ∃ β₀ C C_d : ℝ, 0 < β₀ ∧ 0 ≤ C ∧ 0 ≤ C_d ∧ ∀ β : ℝ, β₀ ≤ β →
    ∀ {ι : Type*} (S : Finset ι) (a x θ : ι → ℝ) (A T μ : ℝ),
      (∀ e ∈ S, |a e| ≤ A) → A ≤ β / 2 → (∀ e ∈ S, |θ e| ≤ T) →
      C_d / β * Real.exp (2 * π * A) ≤ 1 →
      (‖localF₁ β C S a x θ μ‖ ≤ 1 ∧ ‖localF₂ β C S a x θ μ‖ ≤ 1) ∧
      (‖deriv (localF₁ β C S a x θ) μ‖ ≤ S.card * (C_d / β * Real.exp (2 * π * A)) * T ∧
       ‖deriv (localF₂ β C S a x θ) μ‖ ≤ S.card * (C_d / β * Real.exp (2 * π * A)) * T) ∧
      (‖deriv (deriv (localF₁ β C S a x θ)) μ‖ ≤
          2 * S.card ^ 2 * (C_d / β * Real.exp (2 * π * A)) * T ^ 2 ∧
       ‖deriv (deriv (localF₂ β C S a x θ)) μ‖ ≤
          2 * S.card ^ 2 * (C_d / β * Real.exp (2 * π * A)) * T ^ 2) := by
  obtain ⟨β₁, C, hβ₁, hC, hcenv⟩ := exists_translation_envelope
  obtain ⟨β₂, C_d, hβ₂, hCd, hdd⟩ := exists_ratioLogDeriv_bounds
  refine ⟨max β₁ β₂, C, C_d, lt_max_of_lt_left hβ₁, hC, hCd, ?_⟩
  intro β hβ ι S a x θ A T μ haA hA hθT hM1
  have hβ1 : β₁ ≤ β := le_of_max_le_left hβ
  have hβ2 : β₂ ≤ β := le_of_max_le_right hβ
  have hβ0 : 0 < β := lt_of_lt_of_le hβ₁ hβ1
  set M := C_d / β * Real.exp (2 * π * A) with hMdef
  have hM0 : 0 ≤ M := by positivity
  -- bounds for any family `b` with `|b e| ≤ A`
  have hfam : ∀ b : ι → ℝ, (∀ e ∈ S, |b e| ≤ A) →
      ‖edgeProduct β C S b x θ μ‖ ≤ 1 ∧
        ‖deriv (edgeProduct β C S b x θ) μ‖ ≤ S.card * M * T ∧
        ‖deriv (deriv (edgeProduct β C S b x θ)) μ‖ ≤ 2 * S.card ^ 2 * M * T ^ 2 := by
    intro b hb
    have hbβ : ∀ e ∈ S, |b e| ≤ β / 2 := fun e he => (hb e he).trans hA
    have hexp : ∀ e ∈ S, C_d / β * Real.exp (2 * π * |b e|) ≤ M := fun e he => by
      rw [hMdef]
      gcongr
      exact hb e he
    refine edgeProduct_bounds S b x θ hβ0 hbβ hM0 hM1 μ
      (fun e he => hcenv β hβ1 _ _ (hbβ e he)) (fun e he => ?_) (fun e he => ?_) hθT
    · rw [← line_coe]; exact ((hdd β hβ2 _ _ (hbβ e he)).1).trans (hexp e he)
    · rw [← line_coe]; exact ((hdd β hβ2 _ _ (hbβ e he)).2).trans (hexp e he)
  obtain ⟨hPp, hPp', hPp''⟩ := hfam a haA
  obtain ⟨hPm, hPm', hPm''⟩ := hfam (-a) (abs_neg_le S a haA)
  have ha : ∀ e ∈ S, |a e| ≤ β / 2 := fun e he => (haA e he).trans hA
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact norm_I_mul_sub_div_two_le hPp hPm
  · exact norm_add_div_two_le hPp hPm
  · rw [deriv_localF₁ S a x θ hβ0 ha]
    exact norm_I_mul_sub_div_two_le hPp' hPm'
  · rw [deriv_localF₂ S a x θ hβ0 ha]
    exact norm_add_div_two_le hPp' hPm'
  · rw [deriv_deriv_localF₁ S a x θ hβ0 ha]
    exact norm_I_mul_sub_div_two_le hPp'' hPm''
  · rw [deriv_deriv_localF₂ S a x θ hβ0 ha]
    exact norm_add_div_two_le hPp'' hPm''

end FroehlichSpencer.BKT.Rotator.Contour
