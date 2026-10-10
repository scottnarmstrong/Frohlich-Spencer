/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Circle Fourier coefficients of the cosine bond

The coefficient is defined by the circle integral used in FS81 (1.34). This file identifies that
integral with the normalized AddCircle Fourier coefficient and records its reflection symmetry.
The pointwise Fourier expansion is obtained once absolute summability of these integral
coefficients is supplied.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Rotator

/-- The period of the plane-rotator angle. -/
def rotatorPeriod : ℝ := 2 * Real.pi

local instance : Fact (0 < rotatorPeriod) := ⟨by
  dsimp [rotatorPeriod]
  positivity⟩

/-- The complex bond function on the real angle line. -/
def rotatorBondReal (b : ℝ) (t : ℝ) : ℂ :=
  Complex.exp ((b : ℂ) * (Real.cos t : ℂ))

/-- The cosine bond as a continuous function on the circle of period `2π`. -/
def rotatorBondCircle (b : ℝ) : C(AddCircle rotatorPeriod, ℂ) := by
  have hp : rotatorBondReal b 0 = rotatorBondReal b rotatorPeriod := by
    simp [rotatorBondReal, rotatorPeriod, Real.cos_two_pi]
  have hc : ContinuousOn (rotatorBondReal b) (Icc 0 rotatorPeriod) := by
    change ContinuousOn
      (fun t : ℝ => Complex.exp ((b : ℂ) * (Real.cos t : ℂ))) _
    fun_prop
  exact ⟨AddCircle.liftIco rotatorPeriod 0 (rotatorBondReal b),
    AddCircle.liftIco_zero_continuous hp hc⟩

/-- The plane-rotator Fourier coefficient, defined by its circle integral as in FS81 (1.34). -/
def rotatorI (b : ℝ) (m : ℤ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi),
    rotatorBondReal b t * Complex.exp (Complex.I * (m : ℂ) * (t : ℂ))

/-- The integral convention in FS81 (1.34) is the AddCircle coefficient with reversed index. -/
theorem rotatorI_eq_fourierCoeff (b : ℝ) (m : ℤ) :
    rotatorI b m = fourierCoeff (rotatorBondCircle b) (-m) := by
  unfold rotatorI
  change (2 * Real.pi : ℂ)⁻¹ * _ =
    fourierCoeff (AddCircle.liftIco rotatorPeriod 0 (rotatorBondReal b)) (-m)
  rw [fourierCoeff_liftIco_eq (f := rotatorBondReal b) (n := -m) (a := 0)]
  rw [fourierCoeffOn_eq_integral]
  simp only [zero_add, sub_zero, neg_neg, smul_eq_mul]
  congr 1
  · simp [rotatorPeriod]
  · rw [show (0 : ℝ) + rotatorPeriod = 2 * Real.pi by simp [rotatorPeriod]]
    refine intervalIntegral.integral_congr_Ioo_of_le (a := 0) (b := 2 * Real.pi)
      (by positivity) ?_
    intro t ht
    dsimp only
    rw [fourier_coe_apply (T := (2 * Real.pi - 0)) (n := m) (x := t)]
    have he : 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (t : ℂ) /
        ((2 * Real.pi - 0 : ℝ) : ℂ) = Complex.I * (m : ℂ) * (t : ℂ) := by
      push_cast
      field_simp
      ring
    rw [he]
    ring

/-- Reflection of the angle changes the sign of the frequency, and the integral is even in its
integer index. -/
theorem rotatorI_even (b : ℝ) (m : ℤ) : rotatorI b m = rotatorI b (-m) := by
  unfold rotatorI
  have hcomp (f : ℝ → ℂ) :
      (∫ t in (0 : ℝ)..(2 * Real.pi), f t) =
        ∫ t in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - t) := by
    calc
      (∫ t in (0 : ℝ)..(2 * Real.pi), f t) =
          ∫ t in 2 * Real.pi - (2 * Real.pi)..2 * Real.pi - 0, f t := by simp
      _ = ∫ t in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - t) :=
        (intervalIntegral.integral_comp_sub_left f (2 * Real.pi)).symm
  rw [hcomp (fun t => rotatorBondReal b t *
    Complex.exp (Complex.I * (m : ℂ) * (t : ℂ)))]
  congr 1
  refine intervalIntegral.integral_congr_Ioo_of_le (a := 0) (b := 2 * Real.pi)
    (by positivity) ?_
  intro t ht
  simp only [rotatorBondReal, Real.cos_two_pi_sub]
  congr 1
  calc
    Complex.exp (Complex.I * (m : ℂ) * ((2 * Real.pi - t : ℝ) : ℂ)) =
        Complex.exp ((m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
          Complex.I * ((-m : ℤ) : ℂ) * (t : ℂ)) := by
      congr 1
      push_cast
      ring
    _ = Complex.exp ((m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) *
        Complex.exp (Complex.I * ((-m : ℤ) : ℂ) * (t : ℂ)) := Complex.exp_add _ _
    _ = Complex.exp (Complex.I * ((-m : ℤ) : ℂ) * (t : ℂ)) := by
      rw [Complex.exp_int_mul_two_pi_mul_I]
      simp

/-- The pointwise Fourier expansion, provided its integral coefficients are absolutely summable.
The separate factorial majorant requested for these coefficients is not established in this file.
-/
theorem rotatorI_hasPointwiseFourier (b : ℝ) (hI : Summable (rotatorI b))
    (x : AddCircle rotatorPeriod) :
    HasSum (fun m : ℤ => rotatorI b m * fourier m x)
      (rotatorBondCircle b x) := by
  have hcoeff : Summable (fourierCoeff (rotatorBondCircle b)) := by
    convert hI using 1
    funext n
    simpa using (rotatorI_eq_fourierCoeff b (-n)).symm.trans (rotatorI_even b n).symm
  have h := has_pointwise_sum_fourier_series_of_summable hcoeff x
  convert h using 1
  funext n
  rw [smul_eq_mul]
  congr 1
  simpa using (rotatorI_even b n).trans (rotatorI_eq_fourierCoeff b (-n))

end FroehlichSpencer.BKT.Rotator

end
