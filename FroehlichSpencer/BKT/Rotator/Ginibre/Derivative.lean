/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Ginibre.System
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The derivative of a cosine expectation in one coupling

Changing the coupling of one interaction term `e₀` to `t`, the expectation `⟨cos(n·θ)⟩` is
differentiable in `t` with derivative the truncated correlation
`⟨cos(n·θ) cos(d_{e₀}·θ)⟩ - ⟨cos(n·θ)⟩ ⟨cos(d_{e₀}·θ)⟩`, which is nonnegative by Ginibre's second
inequality when all couplings are nonnegative. This is the textbook route to monotonicity; the
monotonicity theorem `integral_cos_cosineGibbs_mono` is proved directly by the duplicated-variable
argument and does not use this file.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Ginibre

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]

theorem cosineEnergy_update (d : E → Frequency V) (J : E → ℝ) (e₀ : E) (t : ℝ) (θ : V → ℝ) :
    cosineEnergy d (Function.update J e₀ t) θ =
      cosineEnergy d J θ + (t - J e₀) * Real.cos (phase (d e₀) θ) := by
  rw [← sub_eq_iff_eq_add', cosineEnergy, cosineEnergy, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single e₀ (fun e _ he => by rw [Function.update_of_ne he, sub_self])
      (fun h => absurd (Finset.mem_univ e₀) h), Function.update_self]
  ring

theorem cosineWeight_update (d : E → Frequency V) (J : E → ℝ) (e₀ : E) (t : ℝ) (θ : V → ℝ) :
    cosineWeight d (Function.update J e₀ t) θ =
      cosineWeight d J θ * Real.exp ((t - J e₀) * Real.cos (phase (d e₀) θ)) := by
  rw [cosineWeight, cosineWeight, cosineEnergy_update, Real.exp_add]

variable [DecidableEq V]

/-- Differentiating a weighted integral in one coupling. -/
theorem hasDerivAt_integral_mul_cosineWeight_update (d : E → Frequency V) (J : E → ℝ) (e₀ : E)
    {f : (V → ℝ) → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ θ, |f θ| ≤ C) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ θ, f θ * cosineWeight d (Function.update J e₀ t) θ
        ∂rotatorRawAngleMeasure V)
      (∫ θ, f θ * Real.cos (phase (d e₀) θ) * cosineWeight d (Function.update J e₀ t₀) θ
        ∂rotatorRawAngleMeasure V) t₀ := by
  set c : (V → ℝ) → ℝ := fun θ => Real.cos (phase (d e₀) θ) with hc_def
  set W := cosineWeight d J
  have hcc : Continuous c := Real.continuous_cos.comp (continuous_phase (d e₀))
  have hWc : Continuous W := continuous_cosineWeight d J
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  let F : ℝ → (V → ℝ) → ℝ := fun t θ => f θ * (W θ * Real.exp ((t - J e₀) * c θ))
  let F' : ℝ → (V → ℝ) → ℝ := fun t θ => f θ * c θ * (W θ * Real.exp ((t - J e₀) * c θ))
  have hFeq (t : ℝ) : (fun θ => f θ * cosineWeight d (Function.update J e₀ t) θ) = F t := by
    funext θ
    rw [cosineWeight_update]
  have hF'eq : (fun θ => f θ * c θ * cosineWeight d (Function.update J e₀ t₀) θ) = F' t₀ := by
    funext θ
    rw [cosineWeight_update]
  simp_rw [hFeq]
  rw [hF'eq]
  have hFc (t : ℝ) : Continuous (F t) := by
    have : Continuous fun θ => (t - J e₀) * c θ := continuous_const.mul hcc
    exact hf.mul (hWc.mul (Real.continuous_exp.comp this))
  have hF'c (t : ℝ) : Continuous (F' t) := by
    have : Continuous fun θ => (t - J e₀) * c θ := continuous_const.mul hcc
    exact (hf.mul hcc).mul (hWc.mul (Real.continuous_exp.comp this))
  set K := Real.exp (|t₀ - J e₀| + 1)
  have hexp (t : ℝ) (ht : t ∈ ball t₀ 1) (θ : V → ℝ) :
      Real.exp ((t - J e₀) * c θ) ≤ K := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : |t - t₀| < 1 := by simpa [Real.dist_eq] using ht
    have h2 : |c θ| ≤ 1 := Real.abs_cos_le_one _
    calc (t - J e₀) * c θ ≤ |(t - J e₀) * c θ| := le_abs_self _
      _ = |t - J e₀| * |c θ| := abs_mul _ _
      _ ≤ |t - J e₀| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = |(t - t₀) + (t₀ - J e₀)| := by ring_nf
      _ ≤ |t - t₀| + |t₀ - J e₀| := abs_add_le _ _
      _ ≤ |t₀ - J e₀| + 1 := by linarith
  have hbound : Integrable (fun θ => C * K * W θ) (rotatorRawAngleMeasure V) :=
    (integrable_cosineWeight d J).const_mul _
  have hFint : Integrable (F t₀) (rotatorRawAngleMeasure V) := by
    rw [← hFeq]
    exact integrable_mul_cosineWeight d _ hf hC
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds t₀ one_pos)
    (Eventually.of_forall fun t => (hFc t).aestronglyMeasurable) hFint
    (hF'c t₀).aestronglyMeasurable (bound := fun θ => C * K * W θ)
    (ae_of_all _ fun θ t ht => ?_) hbound (ae_of_all _ fun θ t _ => ?_)).2
  · have hW : 0 < W θ := cosineWeight_pos d J θ
    have he := Real.exp_pos ((t - J e₀) * c θ)
    simp only [F', Real.norm_eq_abs, abs_mul, abs_of_pos hW, abs_of_pos he]
    have h2 : |c θ| ≤ 1 := Real.abs_cos_le_one _
    calc |f θ| * |c θ| * (W θ * Real.exp ((t - J e₀) * c θ))
        ≤ C * 1 * (W θ * K) := by
          refine mul_le_mul (mul_le_mul (hC θ) h2 (abs_nonneg _) hC0)
            (mul_le_mul_of_nonneg_left (hexp t ht θ) hW.le) (by positivity) (by positivity)
      _ = C * K * W θ := by ring
  · have h := (((hasDerivAt_id t).sub_const (J e₀)).mul_const (c θ)).exp.const_mul (W θ)
    have h' := h.const_mul (f θ)
    refine h'.congr_deriv ?_
    show _ = f θ * c θ * (W θ * Real.exp ((t - J e₀) * c θ))
    simp only [id]
    ring

/-- **Derivative in one coupling = truncated correlation.** -/
theorem hasDerivAt_integral_cos_cosineGibbs_update (d : E → Frequency V) (J : E → ℝ) (e₀ : E)
    (n : Frequency V) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ θ, Real.cos (phase n θ) ∂cosineGibbs d (Function.update J e₀ t))
      ((∫ θ, Real.cos (phase n θ) * Real.cos (phase (d e₀) θ)
          ∂cosineGibbs d (Function.update J e₀ t₀)) -
        (∫ θ, Real.cos (phase n θ) ∂cosineGibbs d (Function.update J e₀ t₀)) *
          ∫ θ, Real.cos (phase (d e₀) θ) ∂cosineGibbs d (Function.update J e₀ t₀)) t₀ := by
  simp only [integral_cosineGibbs]
  have hN := hasDerivAt_integral_mul_cosineWeight_update d J e₀
    (f := fun θ => Real.cos (phase n θ)) (Real.continuous_cos.comp (continuous_phase n)) (C := 1)
    (fun θ => Real.abs_cos_le_one _) t₀
  have hZ := hasDerivAt_integral_mul_cosineWeight_update d J e₀ (f := fun _ => 1)
    continuous_const (C := 1) (fun _ => by simp) t₀
  simp only [one_mul] at hZ
  have hZpos := cosinePartition_pos d (Function.update J e₀ t₀)
  have h := hN.div hZ hZpos.ne'
  rw [cosinePartition] at hZpos
  refine h.congr_deriv ?_
  rw [cosinePartition]
  field_simp

/-- With nonnegative couplings, the derivative of `⟨cos(n·θ)⟩` in any coupling is nonnegative. -/
theorem deriv_integral_cos_cosineGibbs_update_nonneg (d : E → Frequency V) {J : E → ℝ}
    (hJ : ∀ e, 0 ≤ J e) (e₀ : E) (n : Frequency V) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    0 ≤ deriv (fun t => ∫ θ, Real.cos (phase n θ) ∂cosineGibbs d (Function.update J e₀ t)) t₀ := by
  rw [(hasDerivAt_integral_cos_cosineGibbs_update d J e₀ n t₀).deriv, sub_nonneg]
  refine integral_cos_mul_cos_cosineGibbs_ge d (fun e => ?_) n (d e₀)
  by_cases he : e = e₀
  · subst he
    rw [Function.update_self]
    exact ht₀
  · rw [Function.update_of_ne he]
    exact hJ e

end FroehlichSpencer.BKT.Rotator.Ginibre

end
