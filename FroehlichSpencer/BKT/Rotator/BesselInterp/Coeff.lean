/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.BesselInterp.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The Bessel Fourier coefficients are real, even and positive

`besselCoeff β n = (2π)⁻¹ ∫₀^{2π} e^{β cos θ} e^{inθ} dθ` is real (it equals `besselCoeffRe`),
even in `n`, and positive for every `β > 0`. Positivity is used silently by FS81 (B.14), whose
exponent contains `ln I_β(n)`; it is proved here from the exponential series and the recursion
`∫ cos^{k+1} θ cos mθ = ½ (∫ cos^k θ cos (m+1)θ + ∫ cos^k θ cos (m-1)θ)`.
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.BesselInterp

open Complex MeasureTheory
open scoped Real

lemma integral_exp_cos_mul_sin_eq_zero (β : ℝ) (n : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, Real.exp (β * Real.cos θ) * Real.sin (n * θ) = 0 := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ => Real.exp (β * Real.cos θ) * Real.sin (n * θ)) (a := 0) (b := 2 * π) (2 * π)
  simp only [sub_self, sub_zero] at h
  have h2 : ∀ θ : ℝ, Real.exp (β * Real.cos (2 * π - θ)) * Real.sin (n * (2 * π - θ)) =
      -(Real.exp (β * Real.cos θ) * Real.sin (n * θ)) := by
    intro θ
    have : (n : ℝ) * (2 * π - θ) = n * (2 * π) - n * θ := by ring
    rw [this, Real.sin_int_mul_two_pi_sub, Real.cos_two_pi_sub]
    ring
  simp_rw [h2, intervalIntegral.integral_neg] at h
  linarith

/-- The coefficient (B.1) is real. -/
theorem besselCoeff_eq (β : ℝ) (n : ℤ) : besselCoeff β n = besselCoeffRe β n := by
  have hpt : ∀ θ : ℝ, Complex.exp (β * Real.cos θ) * Complex.exp (n * θ * I) =
      ((Real.exp (β * Real.cos θ) * Real.cos (n * θ) : ℝ) : ℂ) +
        ((Real.exp (β * Real.cos θ) * Real.sin (n * θ) : ℝ) : ℂ) * I := by
    intro θ
    have : (n : ℂ) * θ * I = ((n * θ : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.exp_mul_I]
    push_cast
    ring
  have hc : Continuous fun θ : ℝ => Real.exp (β * Real.cos θ) * Real.cos (n * θ) := by fun_prop
  have hs : Continuous fun θ : ℝ => Real.exp (β * Real.cos θ) * Real.sin (n * θ) := by fun_prop
  unfold besselCoeff besselCoeffRe
  simp_rw [hpt]
  have i1 : IntervalIntegrable
      (fun θ : ℝ => ((Real.exp (β * Real.cos θ) * Real.cos (n * θ) : ℝ) : ℂ)) volume 0 (2 * π) :=
    (Complex.continuous_ofReal.comp hc).intervalIntegrable _ _
  have i2 : IntervalIntegrable
      (fun θ : ℝ => ((Real.exp (β * Real.cos θ) * Real.sin (n * θ) : ℝ) : ℂ) * I) volume 0 (2 * π) :=
    ((Complex.continuous_ofReal.comp hs).mul continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
    integral_exp_cos_mul_sin_eq_zero]
  push_cast
  ring

/-- The coefficient is even in the order. -/
theorem besselCoeffRe_neg (β : ℝ) (n : ℤ) : besselCoeffRe β (-n) = besselCoeffRe β n := by
  unfold besselCoeffRe
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [Int.cast_neg, neg_mul, Real.cos_neg]

/-- `J k m = ∫₀^{2π} cos^k θ cos(mθ) dθ`. -/
def cosMoment (k : ℕ) (m : ℤ) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * π, Real.cos θ ^ k * Real.cos (m * θ)

lemma cosMoment_zero (m : ℤ) : cosMoment 0 m = if m = 0 then 2 * π else 0 := by
  unfold cosMoment
  by_cases hm : m = 0
  · simp [hm]
  · rw [ite_eq_right hm]
    simp only [pow_zero, one_mul]
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hm', integral_cos]
    have : (m : ℝ) * (2 * π) = ((2 * m : ℤ) : ℝ) * π := by push_cast; ring
    rw [mul_zero, this, Real.sin_int_mul_pi, Real.sin_zero]
    simp

lemma cosMoment_succ (k : ℕ) (m : ℤ) :
    cosMoment (k + 1) m = (cosMoment k (m + 1) + cosMoment k (m - 1)) / 2 := by
  unfold cosMoment
  have hc : ∀ j : ℤ, Continuous fun θ : ℝ => Real.cos θ ^ k * Real.cos (j * θ) := fun j => by
    fun_prop
  rw [← intervalIntegral.integral_add ((hc _).intervalIntegrable _ _)
      ((hc _).intervalIntegrable _ _), ← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have h1 : ((m + 1 : ℤ) : ℝ) * θ = m * θ + θ := by push_cast; ring
  have h2 : ((m - 1 : ℤ) : ℝ) * θ = m * θ - θ := by push_cast; ring
  rw [h1, h2, Real.cos_add, Real.cos_sub, pow_succ]
  ring

lemma cosMoment_nonneg (k : ℕ) : ∀ m : ℤ, 0 ≤ cosMoment k m := by
  induction k with
  | zero => intro m; rw [cosMoment_zero]; split_ifs <;> positivity
  | succ k ih =>
    intro m; rw [cosMoment_succ]; have := ih (m + 1); have := ih (m - 1); positivity

lemma cosMoment_diag_pos (k : ℕ) : 0 < cosMoment k k := by
  induction k with
  | zero => rw [cosMoment_zero]; simp [Real.pi_pos]
  | succ k ih =>
    rw [cosMoment_succ]
    have h := cosMoment_nonneg k ((k + 1 : ℕ) + 1)
    have : ((k + 1 : ℕ) : ℤ) - 1 = k := by push_cast; ring
    rw [this]
    positivity

lemma hasSum_besselIntegral (β : ℝ) (n : ℤ) :
    HasSum (fun k : ℕ => β ^ k / (Nat.factorial k) * cosMoment k n)
      (∫ θ in (0 : ℝ)..2 * π, Real.exp (β * Real.cos θ) * Real.cos (n * θ)) := by
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := 2 * π)
    (F := fun (k : ℕ) (θ : ℝ) => (β * Real.cos θ) ^ k / (Nat.factorial k) * Real.cos (n * θ))
    (f := fun θ => Real.exp (β * Real.cos θ) * Real.cos (n * θ))
    (fun k _ => |β| ^ k / (Nat.factorial k)) (fun k => by
      exact (by fun_prop : Continuous fun θ : ℝ =>
        (β * Real.cos θ) ^ k / (Nat.factorial k) * Real.cos (n * θ)).aestronglyMeasurable)
    (fun k => Filter.Eventually.of_forall fun θ _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_mul, Nat.abs_cast]
      have h1 := Real.abs_cos_le_one θ
      have h2 := Real.abs_cos_le_one (n * θ)
      calc (|β| * |Real.cos θ|) ^ k / (Nat.factorial k) * |Real.cos (n * θ)|
          ≤ (|β| * 1) ^ k / (Nat.factorial k) * 1 := by gcongr
        _ = |β| ^ k / (Nat.factorial k) := by ring)
    (Filter.Eventually.of_forall fun θ _ => by
      simpa using (NormedSpace.expSeries_div_summable (𝔸 := ℝ) |β|))
    (by exact intervalIntegrable_const)
    (Filter.Eventually.of_forall fun θ _ => by
      have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (β * Real.cos θ)
      rw [← Real.exp_eq_exp_ℝ] at this
      exact this.mul_right _)
  convert key using 1
  funext k
  unfold cosMoment
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [mul_pow]
  ring

/-- `I_β(n) > 0` for every `β > 0` and every integer `n`. -/
theorem besselCoeffRe_pos {β : ℝ} (hβ : 0 < β) (n : ℤ) : 0 < besselCoeffRe β n := by
  unfold besselCoeffRe
  have hn : ∀ θ : ℝ, Real.cos (n * θ) = Real.cos ((n.natAbs : ℤ) * θ) := by
    intro θ
    rcases Int.natAbs_eq n with h | h
    · rw [← h]
    · conv_lhs => rw [h]
      push_cast; rw [neg_mul, Real.cos_neg]
  simp_rw [hn]
  refine mul_pos (by positivity) ?_
  rw [← (hasSum_besselIntegral β (n.natAbs : ℤ)).tsum_eq]
  refine (hasSum_besselIntegral β _).summable.tsum_pos
    (fun k => mul_nonneg (by positivity) (cosMoment_nonneg k _)) n.natAbs ?_
  exact mul_pos (by positivity) (cosMoment_diag_pos _)

end FroehlichSpencer.BKT.Rotator.BesselInterp
