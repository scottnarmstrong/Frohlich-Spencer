/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.BesselInterp.Defs
import FroehlichSpencer.BKT.Rotator.BesselInterp.Coeff
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The steepest-descent contour shift for `I_β(n)`

FS81 (B.2)–(B.4): with `r = sinh⁻¹(n/β)` (so `β sinh r = n` and `β cosh r = √(β² + n²)`), the
`2π`-periodic entire integrand `exp(β cos ζ + i n ζ)` may be integrated over `[-π, π] + ir` instead
of `[-π, π]`, because the vertical sides cancel by periodicity. Taking real parts gives

`2π I_β(n) = e^{-nr} ∫_{-π}^{π} e^{√(β²+n²) cos θ} cos(n(θ - sin θ)) dθ`.
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.BesselInterp

open Complex MeasureTheory
open scoped Real

/-- The (B.1) integrand as an entire function of `ζ`. -/
def besselIntegrand (β : ℝ) (n : ℤ) (ζ : ℂ) : ℂ :=
  Complex.exp (β * Complex.cos ζ + n * ζ * I)

lemma besselIntegrand_add_two_pi (β : ℝ) (n : ℤ) (ζ : ℂ) :
    besselIntegrand β n (ζ + 2 * π) = besselIntegrand β n ζ := by
  unfold besselIntegrand
  have hc : Complex.cos (ζ + 2 * π) = Complex.cos ζ := Complex.cos_periodic ζ
  rw [hc, show (n : ℂ) * (ζ + 2 * π) * I = n * ζ * I + (n * (2 * π * I)) by ring, ← add_assoc,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- (B.3): shifting the period interval to height `r` does not change the integral. -/
theorem integral_besselIntegrand_shift (β : ℝ) (n : ℤ) (r : ℝ) :
    ∫ x in (-π)..π, besselIntegrand β n x =
      ∫ x in (-π)..π, besselIntegrand β n (x + r * I) := by
  have hd : Differentiable ℂ (besselIntegrand β n) := by unfold besselIntegrand; fun_prop
  have h := integral_boundary_rect_eq_zero_of_differentiableOn (besselIntegrand β n)
    (-π : ℂ) ((π : ℂ) + r * I) hd.differentiableOn
  have e1 : ((-π : ℂ)).re = -π := by simp
  have e2 : ((-π : ℂ)).im = 0 := by simp
  have e3 : ((π : ℂ) + r * I).re = π := by simp
  have e4 : ((π : ℂ) + r * I).im = r := by simp
  rw [e1, e2, e3, e4] at h
  have hvert : (∫ y in (0 : ℝ)..r, besselIntegrand β n ((π : ℝ) + y * I)) =
      ∫ y in (0 : ℝ)..r, besselIntegrand β n ((-π : ℝ) + y * I) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [show ((π : ℝ) : ℂ) + y * I = ((-π : ℝ) : ℂ) + y * I + 2 * π by push_cast; ring,
      besselIntegrand_add_two_pi]
  rw [hvert] at h
  simpa [sub_eq_zero] using h

/-- After the shift with `β sinh r = n`, the integrand is `e^{-nr} e^{β cosh r cos θ}
e^{-in(sin θ - θ)}` (the exponent of (B.4)). -/
lemma besselIntegrand_shift_eq {β : ℝ} (n : ℤ) (r x : ℝ) (hsinh : β * Real.sinh r = n) :
    besselIntegrand β n (x + r * I) =
      Real.exp (-(n * r)) * Real.exp (β * Real.cosh r * Real.cos x) *
        Complex.exp (-(n * (Real.sin x - x) : ℝ) * I) := by
  unfold besselIntegrand
  rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [Complex.cos_add, Complex.cos_mul_I, Complex.sin_mul_I]
  have hn : (n : ℂ) = (β : ℂ) * (Real.sinh r : ℂ) := by
    rw [← Complex.ofReal_mul, hsinh]; push_cast; rfl
  push_cast
  rw [hn]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  linear_combination ((β : ℂ) * (Real.sinh r : ℂ) * r) * Complex.I_sq

/-- The (B.1) integral over the centred period. -/
lemma two_pi_mul_besselCoeff (β : ℝ) (n : ℤ) :
    2 * π * besselCoeff β n = ∫ x in (-π)..π, besselIntegrand β n x := by
  have hper : Function.Periodic (fun x : ℝ => besselIntegrand β n x) (2 * π) := by
    intro x
    simp only
    rw [show ((x + 2 * π : ℝ) : ℂ) = (x : ℂ) + 2 * π by push_cast; ring,
      besselIntegrand_add_two_pi]
  have hshift := hper.intervalIntegral_add_eq 0 (-π)
  rw [zero_add, show -π + 2 * π = π by ring] at hshift
  rw [← hshift]
  unfold besselCoeff
  have h2π : (2 * π : ℂ) ≠ 0 := by
    have : (2 * π : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  rw [← mul_assoc, mul_inv_cancel₀ h2π, one_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [besselIntegrand]
  rw [Complex.exp_add, ← Complex.ofReal_cos]

/-- (B.4), real form: `2π I_β(n) = e^{-nr} ∫_{-π}^{π} e^{s cos θ} cos(n(θ - sin θ)) dθ` with
`r = sinh⁻¹(n/β)` and `s = √(β² + n²)`. -/
theorem two_pi_mul_besselCoeffRe {β : ℝ} (hβ : 0 < β) (n : ℤ) :
    2 * π * besselCoeffRe β n =
      ∫ x in (-π)..π, Real.exp (-(n * Real.arsinh (n / β))) *
        Real.exp (Real.sqrt (β ^ 2 + (n : ℝ) ^ 2) * Real.cos x) *
          Real.cos (n * (x - Real.sin x)) := by
  set r := Real.arsinh (n / β) with hr
  set s := Real.sqrt (β ^ 2 + (n : ℝ) ^ 2) with hs
  have hsinh : β * Real.sinh r = n := by
    rw [hr, Real.sinh_arsinh]; field_simp
  have hcosh : β * Real.cosh r = s := by
    rw [hr, Real.cosh_arsinh, hs]
    rw [show β * Real.sqrt (1 + (n / β) ^ 2) = Real.sqrt (β ^ 2 * (1 + (n / β) ^ 2)) by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hβ.le]]
    congr 1
    field_simp
  have hC := two_pi_mul_besselCoeff β n
  rw [besselCoeff_eq, integral_besselIntegrand_shift β n r] at hC
  set A : ℝ → ℝ := fun x => Real.exp (-(n * r)) * Real.exp (s * Real.cos x) with hA
  have hpt : ∀ x : ℝ, besselIntegrand β n (x + r * I) =
      ((A x * Real.cos (n * (x - Real.sin x)) : ℝ) : ℂ) +
        ((A x * Real.sin (n * (x - Real.sin x)) : ℝ) : ℂ) * I := by
    intro x
    rw [besselIntegrand_shift_eq n r x hsinh, hcosh]
    have : (-((n * (Real.sin x - x) : ℝ) : ℂ)) * I = (((n * (x - Real.sin x)) : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [hA]
    push_cast
    ring
  simp_rw [hpt] at hC
  have hcA : Continuous A := by simp only [hA]; fun_prop
  have i1 : IntervalIntegrable
      (fun x : ℝ => ((A x * Real.cos (n * (x - Real.sin x)) : ℝ) : ℂ)) volume (-π) π :=
    (Complex.continuous_ofReal.comp (hcA.mul (by fun_prop))).intervalIntegrable _ _
  have i2 : IntervalIntegrable
      (fun x : ℝ => ((A x * Real.sin (n * (x - Real.sin x)) : ℝ) : ℂ) * I) volume (-π) π :=
    ((Complex.continuous_ofReal.comp (hcA.mul (by fun_prop))).mul
      continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal] at hC
  have hre := congrArg Complex.re hC
  simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero, add_re,
    I_re, I_im, mul_one, add_zero] at hre
  rw [hre]

end FroehlichSpencer.BKT.Rotator.BesselInterp
