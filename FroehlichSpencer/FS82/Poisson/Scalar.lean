module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

@[expose] public section

namespace FroehlichSpencer.FS82.Poisson

open Complex

open Filter Asymptotics

theorem summable_scalar_gaussian (a : ℂ) (ha : 0 < a.re) (w : ℂ) :
    Summable (fun n : ℤ => cexp (-Real.pi * a * (n : ℂ) ^ 2 +
      2 * Real.pi * w * (n : ℂ))) := by
  let f : ℝ → ℂ := fun x => cexp (-Real.pi * a * x ^ 2 + 2 * Real.pi * w * x)
  have hb : f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    apply (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact
      (a := -Real.pi * a) (by
        have hr : (-Real.pi * a).re = -Real.pi * a.re := by simp
        rw [hr]
        nlinarith [mul_pos Real.pi_pos ha])
      (b := 2 * Real.pi * w) (-2)).isBigO
  have hc := hb.comp_tendsto Int.tendsto_coe_cofinite
  have hc' : Summable (fun n : ℤ => f n) :=
    summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : 1 < (2 : ℝ))) hc
  simpa [f] using hc'

theorem summable_dual_scalar_gaussian (a : ℂ) (ha : 0 < a.re) (w : ℂ) :
    Summable (fun k : ℤ => cexp (-Real.pi / a * ((k : ℂ) + I * w) ^ 2)) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have hpi : 0 < (Real.pi / a).re := by
    rw [div_eq_mul_inv, re_ofReal_mul, inv_re]
    exact mul_pos Real.pi_pos (div_pos ha (normSq_pos.mpr ha0))
  let f : ℝ → ℂ := fun x => cexp (-Real.pi / a * ((x : ℂ) + I * w) ^ 2)
  have hpoly (x : ℝ) : -Real.pi / a * ((x : ℂ) + I * w) ^ 2 =
      (-Real.pi / a) * (x : ℂ) ^ 2 + (-2 * Real.pi * I * w / a) * x + Real.pi * w ^ 2 / a := by
    ring_nf
    simp only [I_sq]
    ring
  have hb : f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    have h0 := (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact
      (a := -Real.pi / a) (by
        rw [neg_div, neg_re, neg_lt_zero]
        exact hpi) (b := -2 * Real.pi * I * w / a) (-2)).isBigO
    have heq : f = fun x : ℝ => cexp (Real.pi * w ^ 2 / a) *
        cexp ((-Real.pi / a) * (x : ℂ) ^ 2 + (-2 * Real.pi * I * w / a) * x) := by
      funext x
      change cexp (-Real.pi / a * ((x : ℂ) + I * w) ^ 2) = _
      rw [hpoly x]
      rw [show (-Real.pi / a) * (x : ℂ) ^ 2 + (-2 * Real.pi * I * w / a) * x +
        Real.pi * w ^ 2 / a = (Real.pi * w ^ 2 / a) +
        ((-Real.pi / a) * (x : ℂ) ^ 2 + (-2 * Real.pi * I * w / a) * x) by ring,
        Complex.exp_add]
    rw [heq]
    convert h0.const_mul_left (cexp (Real.pi * w ^ 2 / a)) using 1
  have hc := hb.comp_tendsto Int.tendsto_coe_cofinite
  have hc' : Summable (fun k : ℤ => f k) :=
    summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : 1 < (2 : ℝ))) hc
  simpa [f] using hc'

theorem scalar_poisson (a : ℝ) (ha : 0 < a) (w : ℂ) :
    (∑' n : ℤ, cexp (-(Real.pi : ℂ) * (a : ℂ) * (n : ℂ) ^ 2 +
        2 * Real.pi * w * (n : ℂ))) =
      ((Real.sqrt a : ℝ) : ℂ)⁻¹ *
        ∑' k : ℤ, cexp ((Real.pi : ℂ) / (a : ℂ) * (w - I * (k : ℂ)) ^ 2) := by
  have hp : 0 < ((a : ℝ) : ℂ).re := by simpa using ha
  have h := Complex.tsum_exp_neg_quadratic (a := (a : ℂ)) hp w
  have hsqrt : (a : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt a : ℂ) := by
    rw [show (1 / 2 : ℂ) = (1 / 2 : ℝ) by norm_num]
    rw [← Complex.ofReal_cpow ha.le]
    rw [Real.sqrt_eq_rpow]
  calc
    _ = ∑' n : ℤ, cexp (-Real.pi * (a : ℂ) * (n : ℂ) ^ 2 +
        2 * Real.pi * w * (n : ℂ)) := by simp
    _ = 1 / (a : ℂ) ^ (1 / 2 : ℂ) *
        ∑' k : ℤ, cexp (-Real.pi / (a : ℂ) * ((k : ℂ) + I * w) ^ 2) := h
    _ = _ := by
      rw [hsqrt]
      congr 2
      · ring
      ·
        ext k
        congr 1
        have hs : ((k : ℂ) + I * w) ^ 2 = -(w - I * (k : ℂ)) ^ 2 := by
          calc
            _ = (k : ℂ) ^ 2 + 2 * (k : ℂ) * I * w + I ^ 2 * w ^ 2 := by ring
            _ = _ := by ring_nf; simp only [I_sq]; ring
        rw [hs]
        ring

end FroehlichSpencer.FS82.Poisson
