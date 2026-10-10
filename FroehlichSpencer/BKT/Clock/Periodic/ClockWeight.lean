/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Periodic.Weight
public import FroehlichSpencer.BKT.Generic.Energy.CostEnvelope
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# The clock edge weight after angle rescaling

FS81 §7.1 writes `φ = n θ` and obtains the edge weight
`exp (β cos (φ / n))`, periodic with period `2πn`.

This module proves its compact-periodic weight
properties and the ratio and logarithmic-derivative estimates needed by the generic local-factor
and Taylor bounds.

It does not define the finite compact-angle law or prove a contour translation.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Periodic

open Complex

/-- The clock edge weight after `φ = n θ`. -/
def clockEdgeWeight (β n : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((β : ℂ) * Complex.cos (z / (n : ℂ)))

/-- The real period of the rescaled clock angle. -/
def clockAnglePeriod (n : ℝ) : ℝ := 2 * Real.pi * n

/-- The exact logarithmic cost of a vertical shift of the clock weight. -/
def clockShiftCost (β n u : ℝ) : ℝ := β * (Real.cosh (u / n) - 1)

/-- A bound for the first logarithmic derivative of the clock weight at height `u`. -/
def clockLogDerivBound₁ (β n u : ℝ) : ℝ := β / n * Real.exp (|u| / n)

/-- A bound for the second logarithmic derivative of the clock weight at height `u`. -/
def clockLogDerivBound₂ (β n u : ℝ) : ℝ := β / n ^ 2 * Real.exp (|u| / n)

theorem clockEdgeWeight_analyticAt (β n : ℝ) (z : ℂ) :
    AnalyticAt ℂ (clockEdgeWeight β n) z := by
  unfold clockEdgeWeight
  fun_prop

theorem clockEdgeWeight_ne_zero (β n : ℝ) (z : ℂ) : clockEdgeWeight β n z ≠ 0 := by
  unfold clockEdgeWeight
  exact Complex.exp_ne_zero _

theorem clockEdgeWeight_even (β n : ℝ) (z : ℂ) :
    clockEdgeWeight β n (-z) = clockEdgeWeight β n z := by
  unfold clockEdgeWeight
  rw [neg_div, Complex.cos_neg]

theorem clockEdgeWeight_conj (β n : ℝ) (z : ℂ) :
    (starRingEnd ℂ) (clockEdgeWeight β n z) =
      clockEdgeWeight β n ((starRingEnd ℂ) z) := by
  unfold clockEdgeWeight
  rw [← Complex.exp_conj, map_mul, ← Complex.cos_conj, Complex.conj_ofReal]
  congr 2
  simp [map_div₀]

theorem clockEdgeWeight_periodic (β n : ℝ) (hn : n ≠ 0) (z : ℂ) :
    clockEdgeWeight β n (z + (clockAnglePeriod n : ℂ)) = clockEdgeWeight β n z := by
  unfold clockEdgeWeight clockAnglePeriod
  congr 1
  have hdiv : (z + ((2 * Real.pi * n : ℝ) : ℂ)) / (n : ℂ) =
      z / (n : ℂ) + (2 * Real.pi : ℝ) := by
    push_cast
    field_simp [hn]
  rw [hdiv]
  have hper : ((2 * Real.pi : ℝ) : ℂ) = 2 * Real.pi := by push_cast; ring
  rw [hper, Complex.cos_add_two_pi]

theorem clockEdgeWeight_ofReal (β n t : ℝ) :
    clockEdgeWeight β n t = (Real.exp (β * Real.cos (t / n)) : ℂ) := by
  unfold clockEdgeWeight
  rw [show (t : ℂ) / n = (↑(t / n) : ℂ) by push_cast; simp [div_eq_mul_inv]]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_mul, Complex.ofReal_exp]

theorem clockEdgeWeight_deriv (β n : ℝ) (z : ℂ) :
    deriv (clockEdgeWeight β n) z =
      clockEdgeWeight β n z * (-((β : ℂ) / n) * Complex.sin (z / n)) := by
  unfold clockEdgeWeight
  have hd : HasDerivAt (fun z : ℂ => z / (n : ℂ)) ((n : ℂ)⁻¹) z := by
    simpa [one_div] using (hasDerivAt_id z).div_const (n : ℂ)
  have hcos := (Complex.hasDerivAt_cos (z / (n : ℂ))).comp z hd
  have hmul := hcos.const_mul (β : ℂ)
  have hexp := (Complex.hasDerivAt_exp ((β : ℂ) * Complex.cos (z / (n : ℂ)))).comp z hmul
  simpa [Function.comp_def, div_eq_mul_inv, mul_comm, mul_left_comm] using hexp.deriv

theorem clockEdgeWeight_logDeriv (β n : ℝ) (z : ℂ) :
    logDeriv (clockEdgeWeight β n) z = -((β : ℂ) / n) * Complex.sin (z / n) := by
  change deriv (clockEdgeWeight β n) z / clockEdgeWeight β n z = _
  rw [clockEdgeWeight_deriv]
  field_simp [clockEdgeWeight_ne_zero β n z]

theorem clockEdgeWeight_deriv_logDeriv (β n : ℝ) (z : ℂ) :
    deriv (logDeriv (clockEdgeWeight β n)) z =
      -((β : ℂ) / n ^ 2) * Complex.cos (z / n) := by
  have hfun : logDeriv (clockEdgeWeight β n) =
      fun y => -((β : ℂ) / n) * Complex.sin (y / n) := by
    funext y
    exact clockEdgeWeight_logDeriv β n y
  rw [hfun]
  have hd : HasDerivAt (fun z : ℂ => z / (n : ℂ)) ((n : ℂ)⁻¹) z := by
    simpa [one_div] using (hasDerivAt_id z).div_const (n : ℂ)
  have hsin := (Complex.hasDerivAt_sin (z / (n : ℂ))).comp z hd
  have hmul := hsin.const_mul (-((β : ℂ) / n))
  have h := hmul.deriv
  have hderiv : deriv (fun y : ℂ => -((β : ℂ) / n) * Complex.sin (y / n)) z =
      -((β : ℂ) / n) * (Complex.cos (z / n) * (n : ℂ)⁻¹) := by
    simpa only [Function.comp_def] using h
  rw [hderiv]
  simp only [div_eq_mul_inv, pow_two]
  ring

theorem norm_complex_sin_le_exp_abs_im (z : ℂ) :
    ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have h₁ : ‖Complex.exp (-(z * I))‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    have hre : (-(z * I)).re = z.im := by simp [Complex.mul_re]
    rw [hre]
    exact Real.exp_le_exp.mpr (le_abs_self _)
  have h₂ : ‖Complex.exp (z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    have hre : (z * I).re = -z.im := by simp [Complex.mul_re]
    rw [hre]
    exact Real.exp_le_exp.mpr (neg_le_abs _)
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  norm_num
  calc
    ‖Complex.exp (-(z * I)) - Complex.exp (z * I)‖ / 2 ≤
        (‖Complex.exp (-(z * I))‖ + ‖Complex.exp (z * I)‖) / 2 := by
          gcongr
          exact norm_sub_le _ _
    _ ≤ (Real.exp |z.im| + Real.exp |z.im|) / 2 := by gcongr
    _ = Real.exp |z.im| := by ring

theorem norm_complex_cos_le_exp_abs_im (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h₁ : ‖Complex.exp (z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    have hre : (z * I).re = -z.im := by simp [Complex.mul_re]
    rw [hre]
    exact Real.exp_le_exp.mpr (neg_le_abs _)
  have h₂ : ‖Complex.exp (-(z * I))‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    have hre : (-(z * I)).re = z.im := by simp [Complex.mul_re]
    rw [hre]
    exact Real.exp_le_exp.mpr (le_abs_self _)
  rw [Complex.cos, norm_div]
  norm_num
  calc
    ‖Complex.exp (z * I) + Complex.exp (-(z * I))‖ / 2 ≤
        (‖Complex.exp (z * I)‖ + ‖Complex.exp (-(z * I))‖) / 2 := by
          gcongr
          exact norm_add_le _ _
    _ ≤ (Real.exp |z.im| + Real.exp |z.im|) / 2 := by gcongr
    _ = Real.exp |z.im| := by ring

theorem clockEdgeWeight_cos_shift_re (n t u : ℝ) :
    (Complex.cos (((t : ℂ) + (u : ℂ) * I) / n)).re =
      Real.cos (t / n) * Real.cosh (u / n) := by
  have harg : ((t : ℂ) + (u : ℂ) * I) / n =
      (↑(t / n) : ℂ) + (↑(u / n) : ℂ) * I := by
    apply Complex.ext <;> simp [div_eq_mul_inv]
  rw [harg, Complex.cos_add, Complex.cos_mul_I, Complex.sin_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.mul_re, Complex.mul_im, mul_zero, add_zero, zero_mul, sub_zero, sub_self]

theorem clockEdgeWeight_ratio_le (β n : ℝ) (hβ : 0 ≤ β) (t u : ℝ) :
    ‖clockEdgeWeight β n ((t : ℂ) + (u : ℂ) * I) / clockEdgeWeight β n t‖ ≤
      Real.exp (clockShiftCost β n u) := by
  have harg : (t : ℂ) / n = (↑(t / n) : ℂ) := by
    push_cast
    simp [div_eq_mul_inv]
  unfold clockEdgeWeight
  rw [norm_div, Complex.norm_exp, Complex.norm_exp]
  simp only [Complex.mul_re]
  rw [clockEdgeWeight_cos_shift_re, harg, ← Complex.ofReal_cos]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hcos : Real.cos (t / n) ≤ 1 := (le_abs_self _).trans (Real.abs_cos_le_one _)
  have hcosh : 1 ≤ Real.cosh (u / n) := Real.one_le_cosh _
  have hfactor : 0 ≤ β * (Real.cosh (u / n) - 1) :=
    mul_nonneg hβ (sub_nonneg.mpr hcosh)
  have hmul := mul_le_mul_of_nonneg_right hcos hfactor
  unfold clockShiftCost
  nlinarith [hmul]

private theorem clock_cosh_sub_one_le_sq {x : ℝ} (hx : |x| ≤ 1) :
    Real.cosh x - 1 ≤ x ^ 2 := by
  have hp := Real.norm_exp_sub_one_sub_id_le (x := x) (by rw [Real.norm_eq_abs]; exact hx)
  have hn := Real.norm_exp_sub_one_sub_id_le (x := -x)
    (by rw [Real.norm_eq_abs, abs_neg]; exact hx)
  have hp' : Real.exp x - 1 - x ≤ x ^ 2 := by
    have h := (le_abs_self (Real.exp x - 1 - x)).trans hp
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have hn' : Real.exp (-x) - 1 + x ≤ x ^ 2 := by
    simp only [Real.norm_eq_abs, sub_neg_eq_add, abs_neg, sq_abs] at hn
    exact (le_abs_self _).trans hn
  rw [Real.cosh_eq]
  nlinarith

/-- On the source strip `|u| ≤ n`, the exact shift cost has the quadratic bound (tilde c). -/
theorem clockShiftCost_le_quadratic (β n u : ℝ) (hβ : 0 ≤ β) (hn : 0 < n)
    (hu : |u| ≤ n) : clockShiftCost β n u ≤ β / n ^ 2 * u ^ 2 := by
  unfold clockShiftCost
  have hdiv : |u / n| ≤ 1 := by
    rw [abs_div, abs_of_pos hn]
    apply (div_le_iff₀ hn).2
    nlinarith [hu]
  calc
    β * (Real.cosh (u / n) - 1) ≤ β * (u / n) ^ 2 :=
      mul_le_mul_of_nonneg_left (clock_cosh_sub_one_le_sq hdiv) hβ
    _ = β / n ^ 2 * u ^ 2 := by field_simp

/-- A global exponential envelope for the exact shift cost. -/
theorem clockShiftCost_le_exponential (β n u : ℝ) (hβ : 0 ≤ β) (hn : 0 < n) :
    clockShiftCost β n u ≤ β * Real.exp (|u| / n) := by
  unfold clockShiftCost
  have hcosh (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
    rw [Real.cosh_eq]
    have hx₁ : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self _)
    have hx₂ : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs _)
    nlinarith
  have hsub : Real.cosh (u / n) - 1 ≤ Real.exp |u / n| := by
    have := hcosh (u / n)
    linarith [Real.exp_pos |u / n|]
  calc
    β * (Real.cosh (u / n) - 1) ≤ β * Real.exp |u / n| :=
      mul_le_mul_of_nonneg_left hsub hβ
    _ = β * Real.exp (|u| / n) := by rw [abs_div, abs_of_pos hn]

/-- The clock shift cost satisfies the generic two-branch cost envelope whenever the chosen
contour width is at most `n`. The quadratic coefficient is the source scale `β / n²`. -/
theorem clockShiftCost_isCostEnvelope {β n W : ℝ} (hβ : 0 ≤ β) (hn : 1 ≤ n)
    (hWn : W ≤ n) :
    Generic.IsCostEnvelope (clockShiftCost β n) (β / n ^ 2) (β * W ^ 2 / n ^ 2) W := by
  constructor
  · intro u
    unfold clockShiftCost
    rw [show -u / n = -(u / n) by ring, Real.cosh_neg]
  · simp [clockShiftCost, Real.cosh_zero]
  · positivity
  · positivity
  · intro u hu
    have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
    exact (clockShiftCost_le_quadratic β n u hβ hn0 (hu.trans hn))
  · intro u _ huW
    have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
    have hsq : u ^ 2 ≤ W ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg u) huW 2
    have hcoef : 0 ≤ β / n ^ 2 := div_nonneg hβ (sq_nonneg n)
    have hexp : 1 ≤ Real.exp (2 * Real.pi * |u|) :=
      Real.one_le_exp_iff.mpr (by positivity)
    have hbase := mul_le_mul_of_nonneg_left hsq hcoef
    have htop : β / n ^ 2 * W ^ 2 ≤ β / n ^ 2 * W ^ 2 * Real.exp (2 * Real.pi * |u|) := by
      have h := mul_nonneg (mul_nonneg hcoef (sq_nonneg W)) (sub_nonneg.mpr hexp)
      nlinarith [h]
    calc
      clockShiftCost β n u ≤ β / n ^ 2 * u ^ 2 :=
        clockShiftCost_le_quadratic β n u hβ hn0 (huW.trans hWn)
      _ ≤ β / n ^ 2 * W ^ 2 := hbase
      _ ≤ β * W ^ 2 / n ^ 2 * Real.exp (2 * Real.pi * |u|) := by
        calc
          β / n ^ 2 * W ^ 2 ≤ β / n ^ 2 * W ^ 2 * Real.exp (2 * Real.pi * |u|) := htop
          _ = β * W ^ 2 / n ^ 2 * Real.exp (2 * Real.pi * |u|) := by ring

private theorem clock_abs_sub_sin_le_sq (x : ℝ) : |x - Real.sin x| ≤ x ^ 2 := by
  by_cases hx : |x| ≤ 2
  · have hcube := Real.abs_sub_sin_le x
    have hpow : |x| ^ 3 / 6 ≤ |x| ^ 2 := by
      have h := mul_nonneg (sq_nonneg |x|) (sub_nonneg.mpr hx)
      nlinarith [h]
    calc
      |x - Real.sin x| ≤ |x| ^ 3 / 6 := hcube
      _ ≤ |x| ^ 2 := hpow
      _ = x ^ 2 := sq_abs x
  · have hxlarge : 2 ≤ |x| := le_of_not_ge hx
    have hsin := Real.abs_sin_le_one x
    have htriv : |x - Real.sin x| ≤ |x| + 1 := by
      calc
        |x - Real.sin x| ≤ |x| + |Real.sin x| := abs_sub _ _
        _ ≤ |x| + 1 := by nlinarith [hsin]
    have hquad : |x| + 1 ≤ x ^ 2 := by
      rw [← sq_abs]
      nlinarith [sq_nonneg (|x| - 2)]
    exact htriv.trans hquad

private theorem clock_cos_add_tangent_lower (a x : ℝ) :
    Real.cos (a + x) ≥ Real.cos a - Real.sin a * x - 2 * x ^ 2 := by
  rw [Real.cos_add]
  have hcosLow : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  have hcosUp : Real.cos x ≤ 1 := Real.cos_le_one _
  have hcosDelta : |Real.cos x - 1| ≤ x ^ 2 / 2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hcosUp)]
    linarith [hcosLow]
  have hcosA := Real.abs_cos_le_one a
  have hsinA := Real.abs_sin_le_one a
  have hcosTerm : |Real.cos a * (Real.cos x - 1)| ≤ x ^ 2 / 2 := by
    rw [abs_mul]
    calc
      |Real.cos a| * |Real.cos x - 1| ≤ 1 * (x ^ 2 / 2) :=
        mul_le_mul hcosA hcosDelta (abs_nonneg _) (by positivity)
      _ = x ^ 2 / 2 := one_mul _
  have hsinDelta : |Real.sin x - x| ≤ x ^ 2 := by
    simpa [abs_sub_comm] using clock_abs_sub_sin_le_sq x
  have hsinTerm : |Real.sin a * (x - Real.sin x)| ≤ x ^ 2 := by
    rw [abs_mul]
    calc
      |Real.sin a| * |x - Real.sin x| ≤ 1 * x ^ 2 :=
        mul_le_mul hsinA (clock_abs_sub_sin_le_sq x) (abs_nonneg _) (by positivity)
      _ = x ^ 2 := one_mul _
  have hcosLowTerm : -(x ^ 2 / 2) ≤ Real.cos a * (Real.cos x - 1) := by
    have h := neg_abs_le (Real.cos a * (Real.cos x - 1))
    linarith
  have hsinLowTerm : -x ^ 2 ≤ Real.sin a * (x - Real.sin x) := by
    have h := neg_abs_le (Real.sin a * (x - Real.sin x))
    linarith
  nlinarith

private theorem clockEdgeWeight_logDeriv_ofReal_re (β n t : ℝ) :
    (logDeriv (clockEdgeWeight β n) t).re = -β / n * Real.sin (t / n) := by
  rw [clockEdgeWeight_logDeriv]
  have harg : (t : ℂ) / n = (↑(t / n) : ℂ) := by
    push_cast
    simp [div_eq_mul_inv]
  have hcoeff : -((β : ℂ) / n) = ((-β / n : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, ← Complex.ofReal_sin, hcoeff, ← Complex.ofReal_mul]
  simp only [Complex.ofReal_re]

/-- The real clock weight satisfies the generic one-sided curvature bound, with a uniform second
derivative constant. -/
theorem clockEdgeWeight_hasCurvatureBound {β n : ℝ} (hβ : 0 ≤ β) (hn : 0 < n) :
    Generic.HasCurvatureBound (clockEdgeWeight β n) (2 * β / n ^ 2) := by
  intro t s
  rw [clockEdgeWeight_ofReal β n t, clockEdgeWeight_ofReal β n (t + s)]
  simp only [Complex.ofReal_re, Real.log_exp]
  rw [clockEdgeWeight_logDeriv_ofReal_re]
  have harg : (t + s) / n = t / n + s / n := by ring
  rw [harg]
  have htrig := clock_cos_add_tangent_lower (t / n) (s / n)
  have hβtrig := mul_le_mul_of_nonneg_left htrig hβ
  have hderiv : (-β / n * Real.sin (t / n)) * s =
      -β * Real.sin (t / n) * (s / n) := by
    field_simp
  have hquad : 2 * β / n ^ 2 * s ^ 2 = 2 * β * (s / n) ^ 2 := by
    field_simp
  nlinarith [hβtrig]

theorem clockEdgeWeight_logDeriv_le (β n : ℝ) (hβ : 0 ≤ β) (hn : 0 < n) (t u : ℝ) :
    ‖logDeriv (clockEdgeWeight β n) ((t : ℂ) + (u : ℂ) * I)‖ ≤
      clockLogDerivBound₁ β n u := by
  rw [clockEdgeWeight_logDeriv, norm_mul]
  have hcoeff : ‖-((β : ℂ) / n)‖ = β / n := by
    rw [norm_neg, Complex.norm_div]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ, abs_of_pos hn]
  rw [hcoeff]
  have him : |(((t : ℂ) + (u : ℂ) * I) / n).im| = |u| / n := by
    simp [abs_div, abs_of_pos hn]
  calc
    (β / n) * ‖Complex.sin (((t : ℂ) + (u : ℂ) * I) / n)‖ ≤
        (β / n) * Real.exp |(((t : ℂ) + (u : ℂ) * I) / n).im| :=
          mul_le_mul_of_nonneg_left (norm_complex_sin_le_exp_abs_im _) (div_nonneg hβ hn.le)
    _ = clockLogDerivBound₁ β n u := by rw [him, clockLogDerivBound₁]

theorem clockEdgeWeight_deriv_logDeriv_le (β n : ℝ) (hβ : 0 ≤ β) (hn : 0 < n) (t u : ℝ) :
    ‖deriv (logDeriv (clockEdgeWeight β n)) ((t : ℂ) + (u : ℂ) * I)‖ ≤
      clockLogDerivBound₂ β n u := by
  rw [clockEdgeWeight_deriv_logDeriv, norm_mul]
  have hcoeff : ‖-((β : ℂ) / n ^ 2)‖ = β / n ^ 2 := by
    rw [norm_neg, Complex.norm_div, norm_pow]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ, abs_of_pos hn]
  rw [hcoeff]
  have him : |(((t : ℂ) + (u : ℂ) * I) / n).im| = |u| / n := by
    simp [abs_div, abs_of_pos hn]
  calc
    (β / n ^ 2) * ‖Complex.cos (((t : ℂ) + (u : ℂ) * I) / n)‖ ≤
        (β / n ^ 2) * Real.exp |(((t : ℂ) + (u : ℂ) * I) / n).im| :=
          mul_le_mul_of_nonneg_left (norm_complex_cos_le_exp_abs_im _)
            (div_nonneg hβ (sq_nonneg n))
    _ = clockLogDerivBound₂ β n u := by rw [him, clockLogDerivBound₂]

theorem clockEdgeWeight_compact_rect_bound (β n : ℝ) (hβ : 0 ≤ β) (hn : 0 < n) (A : ℝ)
    (t u : ℝ) (hu : |u| ≤ A) :
    ‖clockEdgeWeight β n ((t : ℂ) + (u : ℂ) * I)‖ ≤ Real.exp (β * Real.exp (A / n)) := by
  rw [clockEdgeWeight, Complex.norm_exp]
  have him : |(((t : ℂ) + (u : ℂ) * I) / n).im| = |u| / n := by
    simp [abs_div, abs_of_pos hn]
  have hheight : |(((t : ℂ) + (u : ℂ) * I) / n).im| ≤ A / n := by
    rw [him]
    exact div_le_div_of_nonneg_right hu hn.le
  have hcos := norm_complex_cos_le_exp_abs_im (((t : ℂ) + (u : ℂ) * I) / n)
  have hreal :
      ((β : ℂ) * Complex.cos (((t : ℂ) + (u : ℂ) * I) / n)).re ≤ β * Real.exp (A / n) := by
    calc
      ((β : ℂ) * Complex.cos (((t : ℂ) + (u : ℂ) * I) / n)).re =
          β * (Complex.cos (((t : ℂ) + (u : ℂ) * I) / n)).re := by
            rw [Complex.mul_re]
            simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      _ ≤ β * ‖Complex.cos (((t : ℂ) + (u : ℂ) * I) / n)‖ :=
          mul_le_mul_of_nonneg_left (Complex.re_le_norm _) hβ
      _ ≤ β * Real.exp |(((t : ℂ) + (u : ℂ) * I) / n).im| :=
          mul_le_mul_of_nonneg_left hcos hβ
      _ ≤ β * Real.exp (A / n) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hheight) hβ
  exact Real.exp_le_exp.mpr hreal

/-- The rescaled clock law's edge weight satisfies the compact-periodic translation interface.
The period and ratio estimates hold uniformly over every real base point, and the two derivative
bounds have the pointwise form of FS81 (7.9) properties (tilde c) and (tilde d). -/
theorem clockEdgeWeight_isCompactPeriodicWeight {β n : ℝ} (hβ : 0 ≤ β) (hn : 0 < n) :
    IsCompactPeriodicWeight (clockEdgeWeight β n) (clockAnglePeriod n)
      (clockShiftCost β n) (clockLogDerivBound₁ β n) (clockLogDerivBound₂ β n) := by
  refine ⟨?_, ?_, clockEdgeWeight_analyticAt β n, clockEdgeWeight_ne_zero β n,
    clockEdgeWeight_even β n, clockEdgeWeight_conj β n, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold clockAnglePeriod
    positivity
  · intro z
    exact clockEdgeWeight_periodic β n hn.ne' z
  · intro t
    have h := congrArg (fun z : ℂ => z.im) (clockEdgeWeight_ofReal β n t)
    simpa only [Complex.ofReal_im] using h
  · intro t
    have h := congrArg (fun z : ℂ => z.re) (clockEdgeWeight_ofReal β n t)
    rw [Complex.ofReal_re] at h
    rw [h]
    exact Real.exp_pos _
  · intro t u
    exact clockEdgeWeight_ratio_le β n hβ t u
  · intro u
    unfold clockShiftCost
    exact mul_nonneg hβ (sub_nonneg.mpr (Real.one_le_cosh _))
  · intro u
    unfold clockShiftCost
    rw [show -u / n = -(u / n) by ring, Real.cosh_neg]
  · simp [clockShiftCost, Real.cosh_zero]
  · intro t u
    exact clockEdgeWeight_logDeriv_le β n hβ hn t u
  · intro t u
    exact clockEdgeWeight_deriv_logDeriv_le β n hβ hn t u
  · intro u
    unfold clockLogDerivBound₁
    positivity
  · intro u
    unfold clockLogDerivBound₂
    positivity
  · intro A hA
    refine ⟨Real.exp (β * Real.exp (A / n)), (Real.exp_pos _).le, ?_⟩
    intro t u _ hu
    exact clockEdgeWeight_compact_rect_bound β n hβ hn A t u hu

end FroehlichSpencer.BKT.Clock.Periodic

end
