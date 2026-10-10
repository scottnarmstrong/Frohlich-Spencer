/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Vertical increments of holomorphic functions

Two elementary estimates used for the translation properties (c), (d) of FS81 J p.576: the mean
value inequality on a closed disc, and the second-order bound
`Re (f (x + ia) - f x) ≤ M a²` when `f'` is real at the real point `x` and `‖f''‖ ≤ M` on the disc of
radius `|a|` about `x`. A function real on the real axis has real derivatives there.
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.BesselInterp

open Complex Metric

/-- The mean value inequality on a closed disc. -/
theorem norm_sub_le_of_hasDerivAt_closedBall {f f' : ℂ → ℂ} {c y : ℂ} {r M : ℝ}
    (hf : ∀ z ∈ closedBall c r, HasDerivAt f (f' z) z) (hM : ∀ z ∈ closedBall c r, ‖f' z‖ ≤ M)
    (hy : y ∈ closedBall c r) : ‖f y - f c‖ ≤ M * ‖y - c‖ := by
  have hr : 0 ≤ r := dist_nonneg.trans hy
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun z hz => (hf z hz).hasDerivWithinAt) hM
    (convex_closedBall c r) (mem_closedBall_self hr) hy

lemma ofReal_add_mul_I_mem_closedBall (x a : ℝ) : (x : ℂ) + a * I ∈ closedBall (x : ℂ) |a| := by
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

/-- Second-order vertical bound: if `f'(x)` is real and `‖f''‖ ≤ M` on the closed disc of radius
`|a|` about the real point `x`, then `Re (f (x + ia) - f x) ≤ M a²`. -/
theorem re_sub_le_of_hasDerivAt {f f' f'' : ℂ → ℂ} {x a M : ℝ}
    (hf : ∀ z ∈ closedBall (x : ℂ) |a|, HasDerivAt f (f' z) z)
    (hf' : ∀ z ∈ closedBall (x : ℂ) |a|, HasDerivAt f' (f'' z) z)
    (hM : ∀ z ∈ closedBall (x : ℂ) |a|, ‖f'' z‖ ≤ M) (hreal : (f' x).im = 0) :
    (f (x + a * I) - f x).re ≤ M * a ^ 2 := by
  set G : ℂ → ℂ := fun z => f z - f x - (z - x) * f' x with hG
  have hG' : ∀ z ∈ closedBall (x : ℂ) |a|, HasDerivAt G (f' z - f' x) z := by
    intro z hz
    have h1 := ((hf z hz).sub_const (f x)).fun_sub
      (((hasDerivAt_id' z).sub_const (x : ℂ)).mul_const (f' x))
    convert h1 using 1
    ring
  have hbd : ∀ z ∈ closedBall (x : ℂ) |a|, ‖f' z - f' x‖ ≤ M * |a| := by
    intro z hz
    have h := norm_sub_le_of_hasDerivAt_closedBall hf' hM hz
    have hz' : ‖z - x‖ ≤ |a| := by rwa [mem_closedBall, dist_eq_norm] at hz
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (mem_closedBall_self (abs_nonneg a)))
    exact h.trans (mul_le_mul_of_nonneg_left hz' hM0)
  have hmem := ofReal_add_mul_I_mem_closedBall x a
  have h := norm_sub_le_of_hasDerivAt_closedBall hG' hbd hmem
  have hGx : G x = 0 := by simp [hG]
  have hnorm : ‖(x : ℂ) + a * I - x‖ = |a| := by
    rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  rw [hGx, sub_zero, hnorm] at h
  have hsplit : (f (x + a * I) - f x).re = (G (x + a * I)).re := by
    simp only [hG, add_sub_cancel_left, sub_re, mul_re, I_re, I_im, ofReal_re, ofReal_im]
    rw [hreal]; ring
  rw [hsplit]
  calc (G (x + a * I)).re ≤ ‖G (x + a * I)‖ := re_le_norm _
    _ ≤ M * |a| * |a| := h
    _ = M * a ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- A function real on the real axis has real derivatives there. -/
theorem im_eq_zero_of_hasDerivAt_of_real {f : ℂ → ℂ} {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x)
    (hreal : ∀ t : ℝ, (f t).im = 0) : f'.im = 0 := by
  have h1 : HasDerivAt (fun t : ℝ => f t) f' x := hf.comp_ofReal
  have h2 : HasDerivAt (fun t : ℝ => (f t).im) f'.im x :=
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h1)
  have h3 : (fun t : ℝ => (f t).im) = fun _ => (0 : ℝ) := funext hreal
  rw [h3] at h2
  exact h2.unique (hasDerivAt_const x 0)

end FroehlichSpencer.BKT.Rotator.BesselInterp
