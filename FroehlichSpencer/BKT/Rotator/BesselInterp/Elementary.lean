/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Elementary bounds for the uniform Debye estimate

Global Taylor bounds `|θ - sin θ| ≤ |θ|³/6` and `cos θ ≤ 1 - θ²/2 + θ⁴/24`, the even Gaussian
moments `∫ θ^{2k} e^{-aθ²} dθ = Γ(k + 1/2) / (a^k √a)` with their integrability, and the convexity
bound `e^x - e^y ≤ (x - y) e^x`.
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.BesselInterp

open MeasureTheory Set
open scoped Real

lemma abs_sub_sin_le (θ : ℝ) : |θ - Real.sin θ| ≤ |θ| ^ 3 / 6 := by
  have key : ∀ x : ℝ, 0 ≤ x → 0 ≤ x - Real.sin x ∧ x - Real.sin x ≤ x ^ 3 / 6 := by
    intro x hx
    refine ⟨by linarith [Real.sin_le hx], ?_⟩
    rcases hx.eq_or_lt with h | h
    · subst h; simp
    · linarith [Real.sin_gt_sub_cube h]
  rcases le_or_gt 0 θ with h | h
  · obtain ⟨h1, h2⟩ := key θ h
    rw [abs_of_nonneg h1, abs_of_nonneg h]; exact h2
  · obtain ⟨h1, h2⟩ := key (-θ) (by linarith)
    rw [Real.sin_neg] at h1 h2
    rw [abs_of_neg h, show θ - Real.sin θ = -(-θ - -Real.sin θ) by ring, abs_neg,
      abs_of_nonneg h1]
    have : (-θ) ^ 3 = -θ ^ 3 := by ring
    linarith

lemma cos_le_quartic (θ : ℝ) : Real.cos θ ≤ 1 - θ ^ 2 / 2 + θ ^ 4 / 24 := by
  set f : ℝ → ℝ := fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24 - Real.cos x with hf
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (by fun_prop : Continuous f).continuousOn
    · exact (by fun_prop : Differentiable ℝ f).differentiableOn
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      have hd : deriv f x = -x + x ^ 3 / 6 + Real.sin x := by
        have : HasDerivAt f (-(2 * x / 2) + 4 * x ^ 3 / 24 - -Real.sin x) x := by
          have h2 := (hasDerivAt_pow 2 x).div_const 2
          have h4 := (hasDerivAt_pow 4 x).div_const 24
          have hc := Real.hasDerivAt_cos x
          convert ((((hasDerivAt_const x (1 : ℝ)).sub h2).add h4).sub hc) using 1
          push_cast; ring
        rw [this.deriv]; ring
      rw [hd]; linarith [Real.sin_gt_sub_cube hx]
  have h0 : f 0 = 0 := by simp [hf]
  have key : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x := fun x hx =>
    h0 ▸ hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  rcases le_or_gt 0 θ with h | h
  · have := key θ h; simp only [hf] at this; linarith
  · have := key (-θ) (by linarith); simp only [hf, Real.cos_neg] at this
    have e2 : (-θ) ^ 2 = θ ^ 2 := by ring
    have e4 : (-θ) ^ 4 = θ ^ 4 := by ring
    rw [e2, e4] at this; linarith

/-- `e^x - e^y ≤ (x - y) e^x` (convexity of `exp`). -/
lemma exp_sub_exp_le (x y : ℝ) : Real.exp x - Real.exp y ≤ (x - y) * Real.exp x := by
  have h := Real.add_one_le_exp (y - x)
  have hy : Real.exp y = Real.exp x * Real.exp (y - x) := by rw [← Real.exp_add]; ring_nf
  rw [hy]
  have hx := Real.exp_pos x
  nlinarith

/-- Integrability of the even Gaussian moments. -/
lemma integrable_pow_two_mul_mul_exp_neg_mul_sq (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable fun θ : ℝ => θ ^ (2 * k) * Real.exp (-a * θ ^ 2) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq ha (s := ((2 * k : ℕ) : ℝ))
    (by have : (0 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
  simpa only [Real.rpow_natCast] using h

/-- Even Gaussian moments over `ℝ`: `∫ θ^{2k} e^{-aθ²} dθ = Γ(k + 1/2) a^{-(k+1/2)}`. -/
lemma integral_pow_two_mul_mul_exp_neg_mul_sq_rpow (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ θ : ℝ, θ ^ (2 * k) * Real.exp (-a * θ ^ 2) =
      Real.Gamma (k + 1 / 2) * a ^ (-((k : ℝ) + 1 / 2)) := by
  have heven : (fun θ : ℝ => θ ^ (2 * k) * Real.exp (-a * θ ^ 2)) =
      fun θ => (fun x : ℝ => x ^ (2 * k) * Real.exp (-a * x ^ 2)) |θ| := by
    funext θ; simp only [pow_mul, sq_abs]
  rw [heven, integral_comp_abs (f := fun x : ℝ => x ^ (2 * k) * Real.exp (-a * x ^ 2))]
  have hI := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2 * k) (b := a) two_pos
    (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith : (-1 : ℝ) < 2 * k) ha
  have hcongr : ∫ x in Ioi (0 : ℝ), x ^ (2 * k) * Real.exp (-a * x ^ 2) =
      ∫ x in Ioi (0 : ℝ), x ^ ((2 * k : ℕ) : ℝ) * Real.exp (-a * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [Real.rpow_natCast, Real.rpow_two]
  rw [hcongr]
  push_cast
  rw [hI]
  have e1 : (2 * (k : ℝ) + 1) / 2 = k + 1 / 2 := by ring
  have e2 : -(2 * (k : ℝ) + 1) / 2 = -((k : ℝ) + 1 / 2) := by ring
  rw [e1, e2]
  ring

/-- Even Gaussian moments: `∫ θ^{2k} e^{-aθ²} dθ = Γ(k + 1/2) / (a^k √a)`. -/
lemma integral_pow_two_mul_mul_exp_neg_mul_sq (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ θ : ℝ, θ ^ (2 * k) * Real.exp (-a * θ ^ 2) =
      Real.Gamma (k + 1 / 2) / (a ^ k * Real.sqrt a) := by
  rw [integral_pow_two_mul_mul_exp_neg_mul_sq_rpow k ha, Real.rpow_neg ha.le,
    Real.rpow_add ha, Real.rpow_natCast, Real.sqrt_eq_rpow]
  ring

end FroehlichSpencer.BKT.Rotator.BesselInterp
