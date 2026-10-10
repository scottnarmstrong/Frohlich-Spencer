/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Ginibre.Evaluation
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Ginibre positivity with an exponential weight

If `F` and `S` are the evaluations of two elements of Ginibre's cone, then
`∫∫ F(θ, θ') exp(S(θ, θ')) dθ dθ' ≥ 0` over `[-π, π)^V × [-π, π)^V`. Every product `F S^k` is again
in the cone, so its integral is `(2π)^{2|V|}` times a nonnegative constant coefficient; the
exponential series converges boundedly, so dominated convergence passes the sign to the limit.
-/

@[expose] public section

open AddMonoidAlgebra MeasureTheory Filter Topology
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Ginibre

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The partial sums of the real exponential series converge to the exponential. -/
theorem tendsto_sum_pow_div_factorial (x : ℝ) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, x ^ k / (Nat.factorial k : ℝ)) atTop
      (𝓝 (Real.exp x)) := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x).tendsto_sum_nat
  rw [← Real.exp_eq_exp_ℝ] at h
  refine h.congr fun N => Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul, inv_mul_eq_div]

theorem abs_sum_pow_div_factorial_le (x : ℝ) (N : ℕ) :
    |∑ k ∈ Finset.range N, x ^ k / (Nat.factorial k : ℝ)| ≤ Real.exp |x| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_of_eq_of_le (Finset.sum_congr rfl fun k _ => ?_)
    (Real.sum_le_exp_of_nonneg (abs_nonneg x) N)
  rw [abs_div, abs_pow, Nat.abs_cast]

/-- **Ginibre positivity.** For `P, Q` in Ginibre's cone with real evaluations `F, S`, the doubled
raw integral of `F exp S` is nonnegative. -/
theorem integral_mul_exp_nonneg {P Q : DupTrigAlgebra V} (hP : IsGinibre P) (hQ : IsGinibre Q)
    {F S : (V → ℝ) × (V → ℝ) → ℝ} (hF : ∀ z, dupEval V P z = (F z : ℂ))
    (hS : ∀ z, dupEval V Q z = (S z : ℂ)) :
    0 ≤ ∫ z, F z * Real.exp (S z) ∂(rotatorRawAngleMeasure V).prod (rotatorRawAngleMeasure V) := by
  set μ := (rotatorRawAngleMeasure V).prod (rotatorRawAngleMeasure V) with hμ
  have hFeq : F = fun z => (dupEval V P z).re := funext fun z => by simp [hF z]
  have hSeq : S = fun z => (dupEval V Q z).re := funext fun z => by simp [hS z]
  have hFc : Continuous F := by
    rw [hFeq]
    exact Complex.continuous_re.comp (continuous_dupEval P)
  have hSc : Continuous S := by
    rw [hSeq]
    exact Complex.continuous_re.comp (continuous_dupEval Q)
  obtain ⟨CF, hCF⟩ := exists_norm_dupEval_le P
  obtain ⟨CS, hCS⟩ := exists_norm_dupEval_le Q
  have hFb (z) : |F z| ≤ CF := by
    have := hCF z
    rwa [hF z, Complex.norm_real, Real.norm_eq_abs] at this
  have hSb (z) : |S z| ≤ CS := by
    have := hCS z
    rwa [hS z, Complex.norm_real, Real.norm_eq_abs] at this
  -- each moment `∫ F S^k` is nonnegative
  have hmoment (k : ℕ) : 0 ≤ ∫ z, F z * S z ^ k ∂μ := by
    have hev : ∀ z, dupEval V (P * Q ^ k) z = ((F z * S z ^ k : ℝ) : ℂ) := by
      intro z
      rw [map_mul, map_pow, Pi.mul_apply, Pi.pow_apply, hF z, hS z]
      push_cast
      ring
    have hint := integral_dupEval (P * Q ^ k)
    simp_rw [hev, integral_complex_ofReal] at hint
    rw [Complex.ofReal_inj.mp hint]
    exact mul_nonneg (by positivity) (hP.mul (hQ.pow k)).coeff_zero_nonneg
  have hcontk (k : ℕ) : Continuous fun z => F z * S z ^ k := hFc.mul (hSc.pow k)
  have hintk (k : ℕ) : Integrable (fun z => F z * S z ^ k) μ := by
    refine Integrable.of_bound (hcontk k).aestronglyMeasurable (CF * CS ^ k) (ae_of_all _ ?_)
    intro z
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul (hFb z) (pow_le_pow_left₀ (abs_nonneg _) (hSb z) k)
      (pow_nonneg (abs_nonneg _) k) ((abs_nonneg _).trans (hFb z))
  -- partial sums of the exponential series
  let G : ℕ → (V → ℝ) × (V → ℝ) → ℝ := fun N z =>
    F z * ∑ k ∈ Finset.range N, S z ^ k / (Nat.factorial k : ℝ)
  have hGnonneg (N : ℕ) : 0 ≤ ∫ z, G N z ∂μ := by
    have hG : (fun z => G N z) =
        fun z => ∑ k ∈ Finset.range N, (F z * S z ^ k) / (Nat.factorial k : ℝ) := by
      funext z
      simp only [G, Finset.mul_sum, mul_div_assoc]
    rw [hG, integral_finsetSum _ fun k _ => (hintk k).div_const _]
    refine Finset.sum_nonneg fun k _ => ?_
    rw [integral_div]
    exact div_nonneg (hmoment k) (by positivity)
  have hlim : Tendsto (fun N => ∫ z, G N z ∂μ) atTop (𝓝 (∫ z, F z * Real.exp (S z) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => CF * Real.exp CS) ?_ ?_ ?_ ?_
    · intro N
      refine Continuous.aestronglyMeasurable ?_
      exact hFc.mul (continuous_finsetSum _ fun k _ => (hSc.pow k).div_const _)
    · exact integrable_const _
    · intro N
      refine ae_of_all _ fun z => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hFb z)
        ((abs_sum_pow_div_factorial_le (S z) N).trans (Real.exp_le_exp.mpr (hSb z)))
        (abs_nonneg _) ((abs_nonneg _).trans (hFb z))
    · exact ae_of_all _ fun z => (tendsto_sum_pow_div_factorial (S z)).const_mul (F z)
  exact ge_of_tendsto' hlim hGnonneg

end FroehlichSpencer.BKT.Rotator.Ginibre

end
