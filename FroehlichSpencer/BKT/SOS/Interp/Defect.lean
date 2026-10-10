/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Interp.Defs

/-!
# The Appendix C coefficients and FS81 (C.2)

With `u = β^{1/3}` and `t = u|n|`, the coefficient of (C.1) is
`β|n| - β^{2/3}(1 + β^{2/3}n²)^{1/2} = u²(t - √(1+t²)) = -u²/(t + √(1+t²))`.
Hence it is nonpositive, even in `n`, bounded by `β^{2/3}` in absolute value for every `n`, and
bounded by `β^{1/3}/(2|n|)` for `n ≠ 0`, which is FS81 (C.2).
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Interp

lemma rpow_one_third_sq {β : ℝ} (hβ : 0 ≤ β) : (β ^ (1 / 3 : ℝ)) ^ 2 = β ^ (2 / 3 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hβ]; norm_num

lemma rpow_one_third_cube {β : ℝ} (hβ : 0 ≤ β) : (β ^ (1 / 3 : ℝ)) ^ 3 = β := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hβ]; norm_num

/-- The coefficient in the form `-u²/(t + √(1+t²))`, `u = β^{1/3}`, `t = u|n|`. -/
lemma sosDefect_eq {β : ℝ} (hβ : 0 ≤ β) (n : ℤ) :
    sosDefect β n = -(β ^ (2 / 3 : ℝ)) /
      (β ^ (1 / 3 : ℝ) * |(n : ℝ)| + Real.sqrt (1 + (β ^ (1 / 3 : ℝ) * |(n : ℝ)|) ^ 2)) := by
  set u := β ^ (1 / 3 : ℝ) with hu
  set t := u * |(n : ℝ)| with ht
  have hu0 : 0 ≤ u := Real.rpow_nonneg hβ _
  have ht0 : 0 ≤ t := mul_nonneg hu0 (abs_nonneg _)
  have h23 : β ^ (2 / 3 : ℝ) = u ^ 2 := (rpow_one_third_sq hβ).symm
  have hβu : β = u ^ 3 := (rpow_one_third_cube hβ).symm
  have hsq : β ^ (2 / 3 : ℝ) * (n : ℝ) ^ 2 = t ^ 2 := by
    rw [h23, ht, mul_pow, sq_abs]
  have hS : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hS2 : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  have hden : 0 < t + Real.sqrt (1 + t ^ 2) := by linarith
  unfold sosDefect
  rw [hsq, h23, eq_div_iff hden.ne', hβu]
  have : u ^ 3 * |(n : ℝ)| = u ^ 2 * t := by rw [ht]; ring
  rw [this]
  linear_combination (-(u ^ 2)) * hS2

lemma sosDefect_nonpos {β : ℝ} (hβ : 0 ≤ β) (n : ℤ) : sosDefect β n ≤ 0 := by
  rw [sosDefect_eq hβ n]
  apply div_nonpos_of_nonpos_of_nonneg
  · have := Real.rpow_nonneg hβ (2 / 3 : ℝ); linarith
  · exact add_nonneg (mul_nonneg (Real.rpow_nonneg hβ _) (abs_nonneg _)) (Real.sqrt_nonneg _)

/-- Every coefficient is at most `β^{2/3}` in absolute value. -/
theorem abs_sosDefect_le {β : ℝ} (hβ : 0 ≤ β) (n : ℤ) : |sosDefect β n| ≤ β ^ (2 / 3 : ℝ) := by
  rw [sosDefect_eq hβ n, abs_div, abs_neg, abs_of_nonneg (Real.rpow_nonneg hβ _)]
  set t := β ^ (1 / 3 : ℝ) * |(n : ℝ)|
  have ht0 : 0 ≤ t := mul_nonneg (Real.rpow_nonneg hβ _) (abs_nonneg _)
  have h1 : 1 ≤ Real.sqrt (1 + t ^ 2) :=
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + t ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  rw [abs_of_pos (by linarith)]
  exact div_le_self (Real.rpow_nonneg hβ _) (by linarith)

/-- FS81 (C.2): `|β|n| - β^{2/3}(1 + β^{2/3}n²)^{1/2}| ≤ β^{1/3}/(2|n|)` for `n ≠ 0`. -/
theorem abs_sosDefect_le_div {β : ℝ} (hβ : 0 < β) {n : ℤ} (hn : n ≠ 0) :
    |sosDefect β n| ≤ β ^ (1 / 3 : ℝ) / (2 * |(n : ℝ)|) := by
  rw [sosDefect_eq hβ.le n, abs_div, abs_neg, abs_of_nonneg (Real.rpow_nonneg hβ.le _)]
  set u := β ^ (1 / 3 : ℝ) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hβ _
  have hn' : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  set t := u * |(n : ℝ)| with ht
  have ht0 : 0 < t := mul_pos hu0 hn'
  have hS : t ≤ Real.sqrt (1 + t ^ 2) :=
    calc t = Real.sqrt (t ^ 2) := (Real.sqrt_sq ht0.le).symm
      _ ≤ Real.sqrt (1 + t ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have h23 : β ^ (2 / 3 : ℝ) = u ^ 2 := (rpow_one_third_sq hβ.le).symm
  rw [abs_of_pos (by linarith), h23, div_le_div_iff₀ (by linarith) (by positivity)]
  have : u ^ 2 * (2 * |(n : ℝ)|) = u * (2 * t) := by rw [ht]; ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (by linarith) hu0.le

lemma sosDefect_neg (β : ℝ) (n : ℤ) : sosDefect β (-n) = sosDefect β n := by
  unfold sosDefect; push_cast; rw [abs_neg, neg_sq]

end FroehlichSpencer.BKT.SOS.Interp
