/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Orthogonality of angle characters

The integral of an integer character over the root interval is the orthogonality relation used in
the Villain current expansion, KP §6.1, p. 33.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace FroehlichSpencer.BKT

/-- An integer character integrates to zero over a full angle interval unless its frequency is
zero, in which case the integral is `2π`. KP §6.1, p. 33. -/
theorem integral_character_Ico (q : ℤ) :
    (∫ θ in Set.Ico (-Real.pi) Real.pi, Complex.exp (Complex.I * (q : ℂ) * (θ : ℂ))) =
      if q = 0 then (2 * Real.pi : ℂ) else 0 := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] :
    -Real.pi ≤ Real.pi)]
  by_cases hq : q = 0
  · subst q
    simp [intervalIntegral.integral_const]
    ring
  · let c : ℂ := Complex.I * (q : ℂ)
    have hc : c ≠ 0 := by
      apply mul_ne_zero Complex.I_ne_zero
      exact_mod_cast hq
    have hperiod : Complex.exp (c * (2 * Real.pi)) = 1 := by
      have harg : c * (2 * Real.pi) = (q : ℂ) * (2 * Real.pi * Complex.I) := by
        dsimp [c]
        ring
      rw [harg]
      exact Complex.exp_int_mul_two_pi_mul_I q
    rw [show (fun θ : ℝ => Complex.exp (Complex.I * (q : ℂ) * (θ : ℂ))) =
        fun θ : ℝ => Complex.exp (c * (θ : ℂ)) by rfl]
    rw [integral_exp_mul_complex hc]
    have hend : Complex.exp (c * (Real.pi : ℂ)) =
        Complex.exp (c * (-Real.pi : ℂ)) := by
      calc
        Complex.exp (c * (Real.pi : ℂ)) =
        Complex.exp (c * ((-Real.pi : ℂ) + 2 * Real.pi)) := by congr 1; ring
        _ = Complex.exp (c * (-Real.pi : ℂ)) * Complex.exp (c * (2 * Real.pi)) := by
          rw [← Complex.exp_add]
          congr 1
          ring
        _ = Complex.exp (c * (-Real.pi : ℂ)) := by rw [hperiod, mul_one]
    rw [hend]
    simp [hq]

/-- Product character orthogonality on the finite product of root intervals. The measure is the
product of the restricted Lebesgue measures, so this is precisely integration over
`[-π, π)^W`. KP §6.1, p. 33. -/
theorem integral_product_character_Ico {W : Type*} [Fintype W] [DecidableEq W]
    (n : W → ℤ) :
    (∫ θ : W → ℝ, ∏ j : W, Complex.exp (Complex.I * (n j : ℂ) * (θ j : ℂ)) ∂
        Measure.pi (fun _ : W => volume.restrict (Set.Ico (-Real.pi) Real.pi))) =
      if n = 0 then (2 * Real.pi : ℂ) ^ Fintype.card W else 0 := by
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (f := fun j (θ : ℝ) => Complex.exp (Complex.I * (n j : ℂ) * (θ : ℂ)))]
  change (∏ j : W,
      ∫ θ in Set.Ico (-Real.pi) Real.pi,
        Complex.exp (Complex.I * (n j : ℂ) * (θ : ℂ))) = _
  by_cases hn : n = 0
  · subst n
    simp
    rw [max_eq_left (by positivity : 0 ≤ Real.pi + Real.pi)]
    congr 1
    push_cast
    ring
  · have hnot : ∃ j, n j ≠ 0 := by
      by_contra h
      apply hn
      funext j
      exact not_not.mp (not_exists.mp h j)
    obtain ⟨j, hj⟩ := hnot
    have hzero :
        (∫ θ in Set.Ico (-Real.pi) Real.pi,
          Complex.exp (Complex.I * (n j : ℂ) * (θ : ℂ))) = 0 := by
      rw [integral_character_Ico]
      simp [hj]
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hzero]
    simp [hn]

end FroehlichSpencer.BKT

end
