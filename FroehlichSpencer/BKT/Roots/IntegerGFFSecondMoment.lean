/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Scalar second-order limit for the integer GFF moment argument

For a fixed real observable `x`, the centered hyperbolic exponential has
second-order coefficient `x² / 2`. This is the pointwise limit used in the
moment consequence of KP Theorem 1.1 (p. 3).
-/

@[expose] public section

namespace FroehlichSpencer.BKT

open Filter Topology

/-- The first-order slope of `t ↦ sinh (t * a)` at zero. -/
theorem tendsto_sinh_scale_quotient (a : ℝ) :
    Tendsto (fun t : ℝ => Real.sinh (t * a) / t) (𝓝[≠] 0) (𝓝 a) := by
  have hlinear : HasDerivAt (fun t : ℝ => t * a) a 0 :=
    hasDerivAt_mul_const (x := 0) a
  have hderiv : HasDerivAt (fun t : ℝ => Real.sinh (t * a)) a 0 := by
    convert (HasDerivAt.comp (x := 0)
      (hh₂ := Real.hasDerivAt_sinh (0 * a)) (hh := hlinear)) using 1
    · rfl
    · simp
  have hslope := hderiv.tendsto_slope_zero
  convert hslope using 1
  ext t
  simp [div_eq_mul_inv, mul_comm]

/-- The centered hyperbolic exponential has second-order coefficient
`x² / 2` as its parameter tends to zero through nonzero values. -/
theorem tendsto_cosh_sub_one_div_sq (x : ℝ) :
    Tendsto (fun t : ℝ => (Real.cosh (t * x) - 1) / t ^ 2)
      (𝓝[≠] 0) (𝓝 (x ^ 2 / 2)) := by
  let a := x / 2
  have hquot := tendsto_sinh_scale_quotient a
  have hsq : Tendsto (fun t : ℝ => 2 * (Real.sinh (t * a) / t) ^ 2)
      (𝓝[≠] 0) (𝓝 (2 * a ^ 2)) :=
    tendsto_const_nhds.mul (hquot.pow 2)
  have hfun : (fun t : ℝ => (Real.cosh (t * x) - 1) / t ^ 2) =
      (fun t => 2 * (Real.sinh (t * a) / t) ^ 2) := by
    funext t
    by_cases ht : t = 0
    · simp [ht]
    · have hdouble : t * x = 2 * (t * a) := by dsimp [a]; ring
      rw [hdouble, Real.cosh_two_mul]
      have hid := Real.cosh_sq_sub_sinh_sq (t * a)
      have hnum : Real.cosh (t * a) ^ 2 + Real.sinh (t * a) ^ 2 - 1 =
          2 * Real.sinh (t * a) ^ 2 := by linarith
      rw [hnum]
      field_simp [ht]
  have hlimit : x ^ 2 / 2 = 2 * a ^ 2 := by dsimp [a]; ring
  rw [hfun, hlimit]
  exact hsq

/-- A quadratic lower bound on a symmetric exponential moment forces the
same lower bound on its second-order coefficient. This is the analytic
implication used after establishing the dominated limit for the integer GFF. -/
theorem second_moment_ge_half_of_exponential_lower
    {F : ℝ → ℝ} {Q a : ℝ}
    (hlimit : Tendsto (fun t : ℝ => (F t - 1) / t ^ 2)
      (𝓝[≠] 0) (𝓝 (Q / 2)))
    (hlower : ∀ t : ℝ, t ≠ 0 → Real.exp (a * t ^ 2) ≤ F t) :
    a ≤ Q / 2 := by
  apply ge_of_tendsto hlimit
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htne : t ≠ 0 := by simpa using ht
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero htne
  have hexp := Real.add_one_le_exp (a * t ^ 2)
  have hnum : a * t ^ 2 ≤ F t - 1 := by linarith [hlower t htne]
  exact (le_div_iff₀ ht2).2 hnum

end FroehlichSpencer.BKT

end
