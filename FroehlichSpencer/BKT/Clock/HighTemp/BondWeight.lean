/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# High-temperature bond weights for the finite clock model

The clock interaction is split into a constant factor and a nonnegative defect
weight. These scalar estimates are uniform in the number of clock states.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.HighTemp

/-- The nonconstant part of the high-temperature bond split. -/
def bondDefect (β x : ℝ) : ℝ := Real.exp (β * (1 + Real.cos x)) - 1

theorem expCos_eq_const_mul_one_add_bondDefect (β x : ℝ) :
    Real.exp (β * Real.cos x) = Real.exp (-β) * (1 + bondDefect β x) := by
  rw [bondDefect]
  rw [show β * Real.cos x = -β + β * (1 + Real.cos x) by ring, Real.exp_add]
  ring

theorem bondDefect_nonneg {β x : ℝ} (hβ : 0 ≤ β) : 0 ≤ bondDefect β x := by
  unfold bondDefect
  have hcos : -1 ≤ Real.cos x := Real.neg_one_le_cos x
  have harg : 0 ≤ β * (1 + Real.cos x) := mul_nonneg hβ (by linarith)
  have : 1 ≤ Real.exp (β * (1 + Real.cos x)) := by
    simpa using (Real.exp_le_exp.mpr harg)
  linarith

theorem bondDefect_le {β x : ℝ} (hβ : 0 ≤ β) :
    bondDefect β x ≤ Real.exp (2 * β) - 1 := by
  unfold bondDefect
  have hcos : Real.cos x ≤ 1 := Real.cos_le_one x
  have harg : β * (1 + Real.cos x) ≤ 2 * β := by nlinarith
  have := (Real.exp_le_exp.mpr harg)
  linarith

theorem bondDefect_ratio_le {β x : ℝ} (hβ : 0 ≤ β) :
    bondDefect β x / (1 + bondDefect β x) ≤ 1 - Real.exp (-2 * β) := by
  set t := β * (1 + Real.cos x)
  have ht : t ≤ 2 * β := by
    dsimp [t]
    nlinarith [Real.cos_le_one x]
  have hden : 1 + bondDefect β x = Real.exp t := by
    simp [bondDefect, t]
  rw [hden]
  have he : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hEq : (Real.exp t - 1) / Real.exp t = 1 - Real.exp (-t) := by
    rw [div_eq_iff he]
    calc
      Real.exp t - 1 = Real.exp t - Real.exp t * Real.exp (-t) := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      _ = Real.exp t * (1 - Real.exp (-t)) := by rw [mul_sub, mul_one]
      _ = (1 - Real.exp (-t)) * Real.exp t := mul_comm _ _
  change (Real.exp t - 1) / Real.exp t ≤ 1 - Real.exp (-2 * β)
  rw [hEq]
  have harg : -2 * β ≤ -t := by linarith
  have hexp : Real.exp (-2 * β) ≤ Real.exp (-t) := Real.exp_le_exp.mpr harg
  linarith

theorem bondDefect_ratio_le_eight {β x : ℝ} (hβ : 0 ≤ β)
    (hβsmall : β ≤ Real.log (8 / 7) / 2) :
    bondDefect β x / (1 + bondDefect β x) ≤ 1 / 8 := by
  calc
    bondDefect β x / (1 + bondDefect β x) ≤ 1 - Real.exp (-2 * β) :=
      bondDefect_ratio_le hβ
    _ ≤ 1 / 8 := by
      have harg : -Real.log (8 / 7) ≤ -2 * β := by linarith
      have hpos : (0 : ℝ) < 8 / 7 := by norm_num
      have hexp : Real.exp (-Real.log (8 / 7)) ≤ Real.exp (-2 * β) :=
        Real.exp_le_exp.mpr harg
      rw [Real.exp_neg, Real.exp_log hpos] at hexp
      norm_num at hexp ⊢
      linarith

end FroehlichSpencer.BKT.Clock.HighTemp

end
