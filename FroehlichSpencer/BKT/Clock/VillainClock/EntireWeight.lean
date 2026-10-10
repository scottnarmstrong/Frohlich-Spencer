/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.ShiftBounds
public import FroehlichSpencer.BKT.Clock.Periodic.ClockWeight
public import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Tactic

/-!
# The compact Villain edge weight as an entire periodic function

`villainClockEdgeWeight β n z = Σ_m exp(−(β/2)(z/n + 2πm)²)` is the Villain weight on the
rescaled angle `φ = nθ`. For the compact contour arguments of FS81 §7 it needs the analytic
properties that `clockEdgeWeight` (the cosine weight) has:

* `villainClockEdgeWeight_eq_entire`, `differentiable_villainClockEdgeWeight`: it is entire;
* `villainClockEdgeWeight_periodic`, `villainClockEdgeWeight_even`: period `2πn`, even;
* `villainWeight_le_zero`: the real weight is maximal at `0`;
* `villainClockEdgeWeight_compact_rect_bound`: boundedness on horizontal strips;
* `villainClockEdgeWeight_ratio_le_clockCost`: the shift ratio is bounded by the cosine clock cost
  `β (cosh(u/n) − 1)`, which dominates the Villain cost `β u²/(2n²)`. All cost-dependent statements of
  the cosine marked pipeline therefore apply to the Villain weight unchanged.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

open Complex
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Clock.Periodic

/-- The analytic form of the compact Villain edge weight. -/
def villainEntire (β n : ℝ) (z : ℂ) : ℂ :=
  ∑' m : ℤ, Complex.exp (-(β / 2 : ℝ) * (z / n + (2 * Real.pi * m : ℝ)) ^ 2)

theorem villainClockEdgeWeight_eq_entire (β n : ℝ) (z : ℂ) :
    villainClockEdgeWeight β n z = villainEntire β n z := by
  unfold villainClockEdgeWeight villainComplexWeight villainEntire villainComplexTerm
  congr 1
  funext m
  congr 3
  apply Complex.ext <;> simp [Complex.div_re, Complex.div_im]

/-- A quadratic lower bound used for the Gaussian majorant. -/
theorem villain_sq_add_ge_half (a b : ℝ) : b ^ 2 / 2 - a ^ 2 ≤ (a + b) ^ 2 := by
  nlinarith [sq_nonneg (2 * a + b)]

theorem norm_villainEntire_term_le (β : ℝ) (hβ : 0 ≤ β) {n : ℝ} (hn : 0 < n) {R : ℝ}
    (m : ℤ) {z : ℂ} (hz : ‖z‖ < R) :
    ‖Complex.exp (-(β / 2 : ℝ) * (z / n + (2 * Real.pi * m : ℝ)) ^ 2)‖ ≤
      Real.exp (β * (R / n) ^ 2) * Real.exp (-(β / 4) * (2 * Real.pi * m) ^ 2) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  set w : ℂ := z / n
  have hw : ‖w‖ ≤ R / n := by
    simp only [w, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
    exact div_le_div_of_nonneg_right hz.le hn.le
  have hre : |w.re| ≤ R / n := (Complex.abs_re_le_norm w).trans hw
  have him : |w.im| ≤ R / n := (Complex.abs_im_le_norm w).trans hw
  have hsq : ((w + ((2 * Real.pi * m : ℝ) : ℂ)) ^ 2).re =
      (w.re + 2 * Real.pi * m) ^ 2 - w.im ^ 2 := by
    simp [pow_two, Complex.mul_re]
  have hreal : (-(β / 2 : ℝ) * (w + ((2 * Real.pi * m : ℝ) : ℂ)) ^ 2 : ℂ).re =
      -(β / 2) * ((w.re + 2 * Real.pi * m) ^ 2 - w.im ^ 2) := by
    rw [← hsq]
    simp [Complex.mul_re]
  rw [hreal]
  have h1 := villain_sq_add_ge_half w.re (2 * Real.pi * m)
  have h2 : w.re ^ 2 ≤ (R / n) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre 2
  have h3 : w.im ^ 2 ≤ (R / n) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) him 2
  nlinarith [mul_le_mul_of_nonneg_left h1 hβ, mul_le_mul_of_nonneg_left h2 hβ,
    mul_le_mul_of_nonneg_left h3 hβ]

theorem summable_villainMajorant {β : ℝ} (hβ : 0 < β) :
    Summable fun m : ℤ => Real.exp (-(β / 4) * (2 * Real.pi * m) ^ 2) := by
  have h := VillainWeight.villainWeight_summable (β := β / 2) (by positivity) 0
  refine h.congr fun m => ?_
  congr 1
  ring

/-- **The compact Villain edge weight is entire.** -/
theorem differentiable_villainEntire (β : ℝ) (hβ : 0 < β) {n : ℝ} (hn : 0 < n) :
    Differentiable ℂ (villainEntire β n) := by
  intro z
  have hz : z ∈ Metric.ball (0 : ℂ) (‖z‖ + 1) := by simp
  have hD : DifferentiableOn ℂ (villainEntire β n) (Metric.ball (0 : ℂ) (‖z‖ + 1)) := by
    refine differentiableOn_tsum_of_summable_norm
      ((summable_villainMajorant hβ).mul_left (Real.exp (β * ((‖z‖ + 1) / n) ^ 2)))
      (fun m => ?_) Metric.isOpen_ball (fun m w hw => ?_)
    · exact (Differentiable.cexp (by fun_prop)).differentiableOn
    · exact norm_villainEntire_term_le β hβ.le hn m (by simpa using hw)
  exact hD.differentiableAt (Metric.isOpen_ball.mem_nhds hz)

theorem differentiable_villainClockEdgeWeight (β : ℝ) (hβ : 0 < β) {n : ℝ} (hn : 0 < n) :
    Differentiable ℂ (villainClockEdgeWeight β n) := by
  have h : villainClockEdgeWeight β n = villainEntire β n :=
    funext (villainClockEdgeWeight_eq_entire β n)
  rw [h]
  exact differentiable_villainEntire β hβ hn

theorem continuous_villainClockEdgeWeight (β : ℝ) (hβ : 0 < β) {n : ℝ} (hn : 0 < n) :
    Continuous (villainClockEdgeWeight β n) :=
  (differentiable_villainClockEdgeWeight β hβ hn).continuous

/-- The compact Villain edge weight has the complex period `2πn`. -/
theorem villainClockEdgeWeight_periodic (β : ℝ) {n : ℝ} (hn : n ≠ 0) (z : ℂ) :
    villainClockEdgeWeight β n (z + (clockAnglePeriod n : ℂ)) = villainClockEdgeWeight β n z := by
  rw [villainClockEdgeWeight_eq_entire β n, villainClockEdgeWeight_eq_entire β n]
  unfold villainEntire clockAnglePeriod
  have hshift : ∀ m : ℤ, (z + ((2 * Real.pi * n : ℝ) : ℂ)) / n + ((2 * Real.pi * m : ℝ) : ℂ) =
      z / n + ((2 * Real.pi * ((m + 1 : ℤ) : ℝ) : ℝ) : ℂ) := by
    intro m
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    push_cast
    field_simp
    ring
  simp_rw [hshift]
  exact (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun m : ℤ => Complex.exp (-(β / 2 : ℝ) * (z / n + ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ)) ^ 2))

/-- The compact Villain edge weight is even. -/
theorem villainClockEdgeWeight_even (β n : ℝ) (z : ℂ) :
    villainClockEdgeWeight β n (-z) = villainClockEdgeWeight β n z := by
  rw [villainClockEdgeWeight_eq_entire β n, villainClockEdgeWeight_eq_entire β n]
  unfold villainEntire
  have hneg : ∀ m : ℤ, Complex.exp (-(β / 2 : ℝ) * (-z / n + ((2 * Real.pi * m : ℝ) : ℂ)) ^ 2) =
      Complex.exp (-(β / 2 : ℝ) * (z / n + ((2 * Real.pi * ((-m : ℤ) : ℝ) : ℝ) : ℂ)) ^ 2) := by
    intro m
    congr 1
    push_cast
    ring
  simp_rw [hneg]
  exact (Equiv.neg ℤ).tsum_eq
    (fun m : ℤ => Complex.exp (-(β / 2 : ℝ) * (z / n + ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ)) ^ 2))

/-- The real Villain weight is maximal at `0` (its Fourier coefficients are positive). -/
theorem villainWeight_le_zero {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    villainWeight β x ≤ villainWeight β 0 := by
  rw [VillainWeight.villainWeight_fourier_real hβ x, VillainWeight.villainWeight_fourier_real hβ 0]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hs := VillainWeight.villainWeight_fourier_coeff_summable hβ
  refine Summable.tsum_le_tsum (fun q => ?_) ?_ ?_
  · simp only [mul_zero, Real.cos_zero, mul_one]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.cos_le_one _)
  · refine Summable.of_norm_bounded hs fun q => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
  · simpa using hs

/-- The compact Villain edge weight is bounded on horizontal strips. -/
theorem villainClockEdgeWeight_compact_rect_bound (β : ℝ) (hβ : 0 < β) {n : ℝ} (hn : 0 < n)
    (A : ℝ) (t u : ℝ) (hu : |u| ≤ A) :
    ‖villainClockEdgeWeight β n ((t : ℂ) + (u : ℂ) * I)‖ ≤
      Real.exp (β * A ^ 2 / (2 * n ^ 2)) * villainWeight β 0 := by
  have hnum : villainClockEdgeWeight β n ((t : ℂ) + (u : ℂ) * I) =
      villainComplexWeight β (t / n) (u / n) := by
    simp [villainClockEdgeWeight]
  rw [hnum]
  refine (villainComplexWeight_norm_le β (t / n) (u / n) hβ).trans ?_
  apply mul_le_mul _ (villainWeight_le_zero hβ _) (VillainWeight.villainWeight_pos hβ _).le
    (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  have hu2 : u ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs u]
    exact pow_le_pow_left₀ (abs_nonneg u) hu 2
  rw [div_pow]
  have hn2 : 0 < n ^ 2 := by positivity
  rw [show β * (u ^ 2 / n ^ 2) / 2 = β * u ^ 2 / (2 * n ^ 2) by field_simp]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu2 hβ.le) (by positivity)

/-- `cosh x − 1 ≥ x²/2`. -/
theorem cosh_sub_one_ge (x : ℝ) : x ^ 2 / 2 ≤ Real.cosh x - 1 := by
  have h2 : Real.cosh x = Real.cosh (2 * (x / 2)) := by ring_nf
  rw [h2, Real.cosh_two_mul, Real.cosh_sq]
  have hs : (x / 2) ^ 2 ≤ Real.sinh (x / 2) ^ 2 := by
    rcases le_total 0 (x / 2) with h | h
    · exact pow_le_pow_left₀ h (Real.self_le_sinh_iff.mpr h) 2
    · have h' : Real.sinh (x / 2) ≤ x / 2 := Real.sinh_le_self_iff.mpr h
      nlinarith
  nlinarith

/-- The Villain cost is dominated by the cosine clock cost. -/
theorem villainClockShiftCost_le_clockShiftCost {β : ℝ} (hβ : 0 ≤ β) (n u : ℝ) :
    villainClockShiftCost β n u ≤ clockShiftCost β n u := by
  unfold villainClockShiftCost clockShiftCost
  have h := cosh_sub_one_ge (u / n)
  have h' : β * u ^ 2 / (2 * n ^ 2) = β * ((u / n) ^ 2 / 2) := by
    by_cases hn : n = 0
    · subst hn; simp
    · field_simp
  rw [h']
  exact mul_le_mul_of_nonneg_left h hβ

/-- **The Villain shift ratio is bounded by the cosine clock cost.** -/
theorem villainClockEdgeWeight_ratio_le_clockCost {β n : ℝ} (hβ : 0 < β) (hn : 0 < n)
    (t u : ℝ) :
    ‖villainClockEdgeWeight β n ((t : ℂ) + (u : ℂ) * I) / villainClockEdgeWeight β n t‖ ≤
      Real.exp (clockShiftCost β n u) :=
  (villainClockEdgeWeight_ratio_le β n t u hβ hn).trans
    (Real.exp_le_exp.mpr (villainClockShiftCost_le_clockShiftCost hβ.le n u))

end FroehlichSpencer.BKT.Clock.VillainClock

end
