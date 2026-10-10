/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.BesselInterp.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The Debye factor `L_β`

`L_β` is real, positive and even on the real axis, where it equals `debyeRe`. On the strip
`|Im φ| < β` its principal branches are holomorphic: `1 + w²` lies in the slit plane,
`(1+w²)^{1/2}` has positive real part, and so does `w + (1+w²)^{1/2}` (`w = φ/β`). Hence `L_β` is
holomorphic and nonvanishing there (FS81 J p.599: "analytic in the strip `|Im φ| ≤ β/2`").
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.BesselInterp

open Complex
open scoped Real

/-! ### The real axis -/

lemma carsinh_ofReal (x : ℝ) : carsinh x = (Real.arsinh x : ℂ) := by
  unfold carsinh Real.arsinh
  have h1 : (0 : ℝ) ≤ 1 + x ^ 2 := by positivity
  have hs : ((1 : ℂ) + (x : ℂ) ^ 2) ^ (1 / 2 : ℂ) = ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow h1]
    push_cast; ring_nf
  rw [hs, ← Complex.ofReal_add, Complex.ofReal_log]
  have := Real.sqrt_le_sqrt (show x ^ 2 ≤ 1 + x ^ 2 by linarith)
  rw [Real.sqrt_sq_eq_abs] at this
  linarith [neg_abs_le x]

theorem debye_ofReal {β : ℝ} (hβ : 0 < β) (x : ℝ) : debye β x = (debyeRe β x : ℂ) := by
  unfold debye debyeRe
  have h1 : (0 : ℝ) ≤ 1 + x ^ 2 / β ^ 2 := by positivity
  have hs : ((1 : ℂ) + (x : ℂ) ^ 2 / (β : ℂ) ^ 2) ^ (1 / 2 : ℂ) =
      ((Real.sqrt (1 + x ^ 2 / β ^ 2) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow h1]
    push_cast; ring_nf
  have h2 : (0 : ℝ) ≤ β * Real.sqrt (1 + x ^ 2 / β ^ 2) := by positivity
  rw [hs, ← Complex.ofReal_div, carsinh_ofReal, ← Complex.ofReal_mul,
    show (-(1 / 2) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow h2]
  push_cast
  ring_nf

lemma debyeRe_pos {β : ℝ} (hβ : 0 < β) (x : ℝ) : 0 < debyeRe β x := by
  unfold debyeRe
  have : 0 < β * Real.sqrt (1 + x ^ 2 / β ^ 2) := by
    have : 0 < 1 + x ^ 2 / β ^ 2 := by positivity
    positivity
  positivity

lemma debyeRe_neg (β x : ℝ) : debyeRe β (-x) = debyeRe β x := by
  unfold debyeRe
  rw [neg_div, Real.arsinh_neg, neg_sq]
  ring_nf

/-! ### The strip -/

lemma one_add_sq_mem_slitPlane {w : ℂ} (hw : |w.im| < 1) : 1 + w ^ 2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  have hre : (1 + w ^ 2).re = 1 + w.re ^ 2 - w.im ^ 2 := by simp [sq]; ring
  have him : (1 + w ^ 2).im = 2 * w.re * w.im := by simp [sq]; ring
  have hy : w.im ^ 2 < 1 := by
    have := sq_abs w.im ▸ (sq_lt_one_iff₀ (abs_nonneg _)).mpr hw
    exact this
  by_cases h1 : w.re = 0
  · left; rw [hre, h1]; linarith
  · by_cases h2 : w.im = 0
    · left; rw [hre, h2]; nlinarith [sq_nonneg w.re]
    · right; rw [him]; exact mul_ne_zero (mul_ne_zero two_ne_zero h1) h2

lemma half_cpow_re_pos {z : ℂ} (hz : z ∈ slitPlane) : 0 < (z ^ (1 / 2 : ℂ)).re := by
  rw [one_div, cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  rcases mem_slitPlane_iff.mp hz with h | h
  · have := norm_nonneg z; linarith
  · have := abs_re_lt_norm.mpr h; have := neg_abs_le z.re; linarith

lemma half_cpow_sq (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
  rw [one_div]; exact_mod_cast cpow_ofNat_inv_pow z 2

/-- On the strip, `w + (1+w²)^{1/2}` has positive real part, so the principal `log` is
holomorphic there. -/
lemma add_sqrt_re_pos {w : ℂ} (hw : |w.im| < 1) : 0 < (w + (1 + w ^ 2) ^ (1 / 2 : ℂ)).re := by
  set s := (1 + w ^ 2) ^ (1 / 2 : ℂ) with hs
  have hspos : 0 < s.re := half_cpow_re_pos (one_add_sq_mem_slitPlane hw)
  rcases le_or_gt 0 w.re with h | h
  · rw [add_re]; linarith
  · have hsq : s ^ 2 = 1 + w ^ 2 := half_cpow_sq _
    have hprod : (w + s) * (s - w) = 1 := by linear_combination hsq
    have hne : s - w ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    have hinv : w + s = (s - w)⁻¹ := eq_inv_of_mul_eq_one_left hprod
    rw [hinv, inv_re]
    apply div_pos
    · simp; linarith
    · exact normSq_pos.mpr hne

lemma im_div_ofReal_lt {β : ℝ} (hβ : 0 < β) {φ : ℂ} (hφ : |φ.im| < β) : |(φ / β).im| < 1 := by
  rw [div_ofReal_im, abs_div, abs_of_pos hβ, div_lt_one hβ]; exact hφ

theorem debye_differentiableAt {β : ℝ} (hβ : 0 < β) {φ : ℂ} (hφ : |φ.im| < β) :
    DifferentiableAt ℂ (debye β) φ := by
  have hw := im_div_ofReal_lt hβ hφ
  have hβ' : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have heq : ∀ z : ℂ, 1 + z ^ 2 / (β : ℂ) ^ 2 = 1 + (z / β) ^ 2 := fun z => by rw [div_pow]
  have hg : DifferentiableAt ℂ (fun z : ℂ => (1 + z ^ 2 / (β : ℂ) ^ 2) ^ (1 / 2 : ℂ)) φ := by
    refine DifferentiableAt.cpow_const (by fun_prop) ?_
    rw [heq]; exact one_add_sq_mem_slitPlane hw
  have hgre : 0 < ((1 + φ ^ 2 / (β : ℂ) ^ 2) ^ (1 / 2 : ℂ)).re := by
    rw [heq]; exact half_cpow_re_pos (one_add_sq_mem_slitPlane hw)
  have hA : DifferentiableAt ℂ
      (fun z : ℂ => ((β : ℂ) * (1 + z ^ 2 / (β : ℂ) ^ 2) ^ (1 / 2 : ℂ)) ^ (-(1 / 2) : ℂ)) φ := by
    refine DifferentiableAt.cpow_const (hg.const_mul _) ?_
    rw [mem_slitPlane_iff]; left
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact mul_pos hβ hgre
  have hC : DifferentiableAt ℂ (fun z : ℂ => carsinh (z / β)) φ := by
    unfold carsinh
    refine DifferentiableAt.clog ?_ ?_
    · refine (differentiableAt_id.div_const _).add (DifferentiableAt.cpow_const (by fun_prop) ?_)
      exact one_add_sq_mem_slitPlane hw
    · exact mem_slitPlane_iff.mpr (Or.inl (add_sqrt_re_pos hw))
  unfold debye
  exact (hA.const_mul _).mul ((differentiableAt_id.neg.mul hC).add (hg.const_mul _)).cexp

theorem debye_ne_zero {β : ℝ} (hβ : 0 < β) {φ : ℂ} (hφ : |φ.im| < β) : debye β φ ≠ 0 := by
  have hw := im_div_ofReal_lt hβ hφ
  have hgre : 0 < ((1 + φ ^ 2 / (β : ℂ) ^ 2) ^ (1 / 2 : ℂ)).re := by
    rw [show 1 + φ ^ 2 / (β : ℂ) ^ 2 = 1 + (φ / β) ^ 2 by rw [div_pow]]
    exact half_cpow_re_pos (one_add_sq_mem_slitPlane hw)
  have hbase : (β : ℂ) * (1 + φ ^ 2 / (β : ℂ) ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, zero_re] at this
    nlinarith
  unfold debye
  refine mul_ne_zero (mul_ne_zero ?_ ?_) (Complex.exp_ne_zero _)
  · have : (0 : ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
    exact inv_ne_zero (by exact_mod_cast this.ne')
  · exact (cpow_ne_zero_iff).mpr (Or.inl hbase)

end FroehlichSpencer.BKT.Rotator.BesselInterp
