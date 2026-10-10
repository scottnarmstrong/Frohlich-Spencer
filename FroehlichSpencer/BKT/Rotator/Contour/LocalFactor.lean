/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Contour.Factor

/-!
# Chain rules for the normalized edge factor (FS81 (6.22)–(6.24))

On the strip `|Im z| < β/2` and for `|a| ≤ β/2`, the normalized factor
`i_β(a; z) = I_β(z + ia) I_β(z)⁻¹ e^{-g(a)/β}` of FS81 (6.19) is `exp` of
`ℓ(z + ia) − ℓ(z) − g(a)/β`, where `ℓ = interpLog β` is the explicit holomorphic logarithm of
`I_β`. Hence its complex derivative is
`[(log I_β)'(z + ia) − (log I_β)'(z)] i_β(a; z)` (no branch of `log` enters). Along a real line
`r(λ) = x + λθ` this gives FS81 (6.22) and the second-derivative formula behind (6.24). Property (d)
(J p.576) bounds the logarithmic-derivative differences by `C_d β⁻¹ e^{2π|a|}`, which yields the
local bounds (6.23)–(6.24).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Contour

open Complex Filter Topology
open scoped Real
open FroehlichSpencer.BKT.Rotator.BesselInterp

/-- `(log I_β)'(z + ia) − (log I_β)'(z)`, through the explicit logarithm. -/
def ratioLogDeriv (β a : ℝ) (z : ℂ) : ℂ :=
  interpLogDeriv β (z + a * Complex.I) - interpLogDeriv β z

/-- `(log I_β)''(z + ia) − (log I_β)''(z)`, through the explicit logarithm. -/
def ratioLogDeriv2 (β a : ℝ) (z : ℂ) : ℂ :=
  interpLogDeriv2 β (z + a * Complex.I) - interpLogDeriv2 β z

/-- The logarithm `ℓ(z + ia) − ℓ(z) − g(a)/β` of the normalized factor. -/
def factorLog (β C a : ℝ) (z : ℂ) : ℂ :=
  interpLog β (z + a * Complex.I) - interpLog β z - ((cEnvelope C a / β : ℝ) : ℂ)

lemma abs_im_add_mul_I_lt {β a : ℝ} {z : ℂ} (ha : |a| ≤ β / 2) (hz : |z.im| < β / 2) :
    |(z + a * Complex.I).im| < β := by
  have h : (z + a * Complex.I).im = z.im + a := by simp
  rw [h]
  calc |z.im + a| ≤ |z.im| + |a| := abs_add_le _ _
    _ < β / 2 + β / 2 := by linarith
    _ = β := by ring

lemma abs_im_lt_of_half {β : ℝ} {z : ℂ} (hz : |z.im| < β / 2) : |z.im| < β := by
  have : 0 ≤ |z.im| := abs_nonneg _
  linarith

lemma isOpen_halfStrip (β : ℝ) : IsOpen {z : ℂ | |z.im| < β / 2} :=
  isOpen_lt (continuous_abs.comp continuous_im) continuous_const

lemma abs_im_ofReal_lt {β : ℝ} (hβ : 0 < β) (x : ℝ) : |((x : ℂ)).im| < β / 2 := by
  simp only [ofReal_im, abs_zero]; linarith

/-- On the strip, `i_β(a; z) = exp (ℓ(z + ia) − ℓ(z) − g(a)/β)`. -/
theorem normalizedFactor_eq_exp {β C a : ℝ} (hβ : 0 < β) (ha : |a| ≤ β / 2) {z : ℂ}
    (hz : |z.im| < β / 2) :
    normalizedFactor β C a z = Complex.exp (factorLog β C a z) := by
  unfold normalizedFactor factorLog
  rw [besselInterp_eq_exp_interpLog hβ (abs_im_add_mul_I_lt ha hz),
    besselInterp_eq_exp_interpLog hβ (abs_im_lt_of_half hz), sub_eq_add_neg _ ((_ : ℝ) : ℂ),
    Complex.exp_add, Complex.exp_sub]

theorem ratioLogDeriv_eq_logDeriv {β a : ℝ} (hβ : 0 < β) (ha : |a| ≤ β / 2) {z : ℂ}
    (hz : |z.im| < β / 2) :
    ratioLogDeriv β a z =
      logDeriv (besselInterp β) (z + a * Complex.I) - logDeriv (besselInterp β) z := by
  unfold ratioLogDeriv
  rw [logDeriv_besselInterp hβ (abs_im_add_mul_I_lt ha hz),
    logDeriv_besselInterp hβ (abs_im_lt_of_half hz)]

theorem ratioLogDeriv2_eq_deriv_logDeriv {β a : ℝ} (hβ : 0 < β) (ha : |a| ≤ β / 2) {z : ℂ}
    (hz : |z.im| < β / 2) :
    ratioLogDeriv2 β a z =
      deriv (logDeriv (besselInterp β)) (z + a * Complex.I) -
        deriv (logDeriv (besselInterp β)) z := by
  unfold ratioLogDeriv2
  rw [deriv_logDeriv_besselInterp hβ (abs_im_add_mul_I_lt ha hz),
    deriv_logDeriv_besselInterp hβ (abs_im_lt_of_half hz)]

theorem hasDerivAt_factorLog {β C a : ℝ} (hβ : 0 < β) (ha : |a| ≤ β / 2) {z : ℂ}
    (hz : |z.im| < β / 2) :
    HasDerivAt (factorLog β C a) (ratioLogDeriv β a z) z := by
  have h1 : HasDerivAt (fun w : ℂ => interpLog β (w + a * Complex.I))
      (interpLogDeriv β (z + a * Complex.I)) z :=
    HasDerivAt.comp_add_const z _ (hasDerivAt_interpLog hβ (abs_im_add_mul_I_lt ha hz))
  have h2 := hasDerivAt_interpLog hβ (abs_im_lt_of_half hz)
  have h3 := (h1.sub h2).sub_const ((cEnvelope C a / β : ℝ) : ℂ)
  exact h3

theorem hasDerivAt_ratioLogDeriv {β a : ℝ} (hβ : 0 < β) (ha : |a| ≤ β / 2) {z : ℂ}
    (hz : |z.im| < β / 2) :
    HasDerivAt (ratioLogDeriv β a) (ratioLogDeriv2 β a z) z := by
  have h1 : HasDerivAt (fun w : ℂ => interpLogDeriv β (w + a * Complex.I))
      (interpLogDeriv2 β (z + a * Complex.I)) z :=
    HasDerivAt.comp_add_const z _ (hasDerivAt_interpLogDeriv hβ (abs_im_add_mul_I_lt ha hz))
  have h2 := hasDerivAt_interpLogDeriv hβ (abs_im_lt_of_half hz)
  exact h1.sub h2

/-- The complex derivative of `i_β(a; ·)`: `[(log I_β)'(z + ia) − (log I_β)'(z)] i_β(a; z)`. -/
theorem hasDerivAt_normalizedFactor {β C a : ℝ} (hβ : 0 < β) (ha : |a| ≤ β / 2) {z : ℂ}
    (hz : |z.im| < β / 2) :
    HasDerivAt (normalizedFactor β C a) (ratioLogDeriv β a z * normalizedFactor β C a z) z := by
  have heq : normalizedFactor β C a =ᶠ[𝓝 z] fun w => Complex.exp (factorLog β C a w) :=
    Filter.eventually_of_mem ((isOpen_halfStrip β).mem_nhds hz)
      fun w hw => normalizedFactor_eq_exp hβ ha hw
  have h := ((hasDerivAt_factorLog (C := C) hβ ha hz).cexp).congr_of_eventuallyEq heq
  rw [← normalizedFactor_eq_exp hβ ha hz, mul_comm] at h
  exact h

/-- Differentiation along the real line `μ ↦ x + μθ`. -/
lemma hasDerivAt_line {f : ℂ → ℂ} {f' : ℂ} {x θ μ₀ : ℝ}
    (hf : HasDerivAt f f' ((x : ℂ) + μ₀ * θ)) :
    HasDerivAt (fun μ : ℝ => f ((x : ℂ) + μ * θ)) (θ * f') μ₀ := by
  have h1 : HasDerivAt (fun w : ℂ => (x : ℂ) + w * θ) (θ : ℂ) (μ₀ : ℂ) := by
    have := ((hasDerivAt_id' (μ₀ : ℂ)).mul_const (θ : ℂ)).const_add (x : ℂ)
    simpa using this
  have h2 := (hf.comp (μ₀ : ℂ) h1).comp_ofReal
  rw [mul_comm] at h2
  exact h2

lemma abs_im_line_lt {β : ℝ} (hβ : 0 < β) (x θ μ : ℝ) :
    |((x : ℂ) + μ * θ).im| < β / 2 := by
  have : ((x : ℂ) + μ * θ).im = 0 := by simp
  rw [this, abs_zero]; linarith

/-- FS81 (6.22): along `r(λ) = x + λθ`,
`∂_λ i_β(a; r(λ)) = θ [(log I_β)'(r + ia) − (log I_β)'(r)] i_β(a; r(λ))`. -/
theorem hasDerivAt_normalizedFactor_line {β C a : ℝ} (hβ : 0 < β) (ha : |a| ≤ β / 2)
    (x θ μ₀ : ℝ) :
    HasDerivAt (fun μ : ℝ => normalizedFactor β C a (x + μ * θ))
      (θ * ratioLogDeriv β a (x + μ₀ * θ) * normalizedFactor β C a (x + μ₀ * θ)) μ₀ := by
  have h := hasDerivAt_line (x := x) (θ := θ) (μ₀ := μ₀)
    (hasDerivAt_normalizedFactor (C := C) hβ ha (abs_im_line_lt hβ x θ μ₀))
  rw [← mul_assoc] at h
  exact h

theorem hasDerivAt_ratioLogDeriv_line {β a : ℝ} (hβ : 0 < β) (ha : |a| ≤ β / 2) (x θ μ₀ : ℝ) :
    HasDerivAt (fun μ : ℝ => ratioLogDeriv β a (x + μ * θ))
      (θ * ratioLogDeriv2 β a (x + μ₀ * θ)) μ₀ :=
  hasDerivAt_line (hasDerivAt_ratioLogDeriv hβ ha (abs_im_line_lt hβ x θ μ₀))

/-- The second derivative of `i_β(a; r(λ))` along the line:
`θ² [((log I_β)'-difference)² + (log I_β)''-difference] i_β(a; r(λ))`. -/
theorem hasDerivAt_normalizedFactor_line_deriv {β C a : ℝ} (hβ : 0 < β) (ha : |a| ≤ β / 2)
    (x θ μ₀ : ℝ) :
    HasDerivAt
      (fun μ : ℝ => θ * ratioLogDeriv β a (x + μ * θ) * normalizedFactor β C a (x + μ * θ))
      (θ ^ 2 * (ratioLogDeriv β a (x + μ₀ * θ) ^ 2 + ratioLogDeriv2 β a (x + μ₀ * θ)) *
        normalizedFactor β C a (x + μ₀ * θ)) μ₀ := by
  have h1 := (hasDerivAt_ratioLogDeriv_line hβ ha x θ μ₀).const_mul (θ : ℂ)
  have h2 := hasDerivAt_normalizedFactor_line (C := C) hβ ha x θ μ₀
  convert h1.mul h2 using 1
  ring

/-- Property (d) for the local factors: constants `β₀`, `C_d` with
`‖(log I_β)'(x + ia) − (log I_β)'(x)‖ ≤ C_d β⁻¹ e^{2π|a|}` and the same for the second
logarithmic derivative, for real `x`, `|a| ≤ β/2`, `β ≥ β₀`. -/
theorem exists_ratioLogDeriv_bounds :
    ∃ β₀ C_d : ℝ, 0 < β₀ ∧ 0 ≤ C_d ∧ ∀ β : ℝ, β₀ ≤ β → ∀ x a : ℝ, |a| ≤ β / 2 →
      ‖ratioLogDeriv β a x‖ ≤ C_d / β * Real.exp (2 * π * |a|) ∧
      ‖ratioLogDeriv2 β a x‖ ≤ C_d / β * Real.exp (2 * π * |a|) := by
  obtain ⟨β₀, C_d, hβ₀, hC, h⟩ := logDeriv_besselInterp_translate_sub_le
  refine ⟨β₀, C_d, hβ₀, hC, fun β hβ x a ha => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hβ₀ hβ
  have hx := abs_im_ofReal_lt hβ0 x
  rw [ratioLogDeriv_eq_logDeriv hβ0 ha hx, ratioLogDeriv2_eq_deriv_logDeriv hβ0 ha hx]
  exact h β hβ x a ha

/-- FS81 (6.23): the first-derivative envelope of one local factor. -/
theorem norm_line_deriv_le {β C a M : ℝ} (x θ : ℝ)
    (hd : ‖ratioLogDeriv β a x‖ ≤ M) (hi : ‖normalizedFactor β C a x‖ ≤ 1) :
    ‖(θ : ℂ) * ratioLogDeriv β a x * normalizedFactor β C a x‖ ≤ M * |θ| := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hd
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |θ| * ‖ratioLogDeriv β a x‖ * ‖normalizedFactor β C a x‖ ≤ |θ| * M * 1 := by
        gcongr
    _ = M * |θ| := by ring

/-- FS81 (6.24): the second-derivative envelope of one local factor,
`(M² + M) θ²`, hence `2 M θ²` when `M ≤ 1`. -/
theorem norm_line_deriv2_le {β C a M : ℝ} (x θ : ℝ)
    (hd : ‖ratioLogDeriv β a x‖ ≤ M) (hd2 : ‖ratioLogDeriv2 β a x‖ ≤ M)
    (hi : ‖normalizedFactor β C a x‖ ≤ 1) :
    ‖(θ : ℂ) ^ 2 * (ratioLogDeriv β a x ^ 2 + ratioLogDeriv2 β a x) *
        normalizedFactor β C a x‖ ≤ (M ^ 2 + M) * θ ^ 2 := by
  have hsum : ‖ratioLogDeriv β a x ^ 2 + ratioLogDeriv2 β a x‖ ≤ M ^ 2 + M := by
    calc ‖ratioLogDeriv β a x ^ 2 + ratioLogDeriv2 β a x‖
        ≤ ‖ratioLogDeriv β a x‖ ^ 2 + ‖ratioLogDeriv2 β a x‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_pow]
      _ ≤ M ^ 2 + M := by gcongr
  have hM : 0 ≤ M := (norm_nonneg _).trans hd2
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc θ ^ 2 * ‖ratioLogDeriv β a x ^ 2 + ratioLogDeriv2 β a x‖ * ‖normalizedFactor β C a x‖
      ≤ θ ^ 2 * (M ^ 2 + M) * 1 := by gcongr
    _ = (M ^ 2 + M) * θ ^ 2 := by ring

end FroehlichSpencer.BKT.Rotator.Contour
