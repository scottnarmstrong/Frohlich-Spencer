/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.StripWeightScaling
public import FroehlichSpencer.BKT.Generic.Energy.CostEnvelope

/-! # Gaussian edge data for the Villain Theorem C route

At Villain inverse temperature `B`, the dual pinned Gaussian field has edge weight
`exp(-|∇φ|²/(2B))`. This file packages the weight estimates consumed by rooted T1.5-NG.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Villain.TheoremC

open Complex
open FroehlichSpencer.BKT.Generic

/-- The Gaussian edge weight on the pinned real field dual to a Villain model at `B`. -/
def gaussianVillainWeight (B : ℝ) (z : ℂ) : ℂ := gaussianWeight (B⁻¹) z

/-- The exact Gaussian translation cost at Villain inverse temperature `B`. -/
def gaussianVillainCost (B u : ℝ) : ℝ := (B⁻¹ / 2) * u ^ 2

theorem gaussianWeight_logDeriv (b : ℝ) :
    logDeriv (gaussianWeight b) = fun z => -((b : ℂ) * z) := by
  funext z
  rw [logDeriv_apply]
  let F : ℂ → ℂ := fun y => -((b / 2 : ℝ) : ℂ) * y ^ 2
  have hF : HasDerivAt F (-((b : ℂ) * z)) z := by
    dsimp [F]
    convert (hasDerivAt_pow 2 z).const_mul (-((b / 2 : ℝ) : ℂ)) using 1
    all_goals
      simp
      ring
  have hcomp := (Complex.hasDerivAt_exp (F z)).comp z hF
  change deriv (Complex.exp ∘ F) z / Complex.exp (F z) = -((b : ℂ) * z)
  rw [hcomp.deriv]
  field_simp [Complex.exp_ne_zero]

theorem deriv_logDeriv_gaussianWeight (b : ℝ) (z : ℂ) :
    deriv (logDeriv (gaussianWeight b)) z = -(b : ℂ) := by
  rw [gaussianWeight_logDeriv]
  simp

/-- A Gaussian weight has the logarithmic derivative variation bounds needed by T1.5-NG. -/
theorem hasLogDerivBounds_gaussianVillainWeight {B : ℝ} (hB : 0 < B) (W : ℝ) :
    HasLogDerivBounds (gaussianVillainWeight B) W (fun u => B⁻¹ * |u|) := by
  have hBinv : 0 < B⁻¹ := inv_pos.mpr hB
  refine ⟨?_, ?_⟩
  · intro t u hu
    rw [show gaussianVillainWeight B = gaussianWeight (B⁻¹) from rfl,
      gaussianWeight_logDeriv]
    change ‖-(((B⁻¹ : ℝ) : ℂ) * ((t : ℂ) + (u : ℂ) * I)) -
        -(((B⁻¹ : ℝ) : ℂ) * (t : ℂ))‖ ≤ B⁻¹ * |u|
    have hval : -(((B⁻¹ : ℝ) : ℂ) * ((t : ℂ) + (u : ℂ) * I)) -
        (-(((B⁻¹ : ℝ) : ℂ) * (t : ℂ))) = -(((B⁻¹ : ℝ) : ℂ) * (u : ℂ) * I) := by ring
    rw [hval]
    have hn : ‖-(((B⁻¹ : ℝ) : ℂ) * (u : ℂ) * I)‖ = B⁻¹ * |u| := by
      have hbn : ‖((B⁻¹ : ℝ) : ℂ)‖ = B⁻¹ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hBinv.le]
      have hun : ‖(u : ℂ)‖ = |u| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      rw [norm_neg, norm_mul, norm_mul, hbn, hun, Complex.norm_I]
      ring
    rw [hn]
  · intro t u hu
    rw [show gaussianVillainWeight B = gaussianWeight (B⁻¹) from rfl,
      deriv_logDeriv_gaussianWeight, deriv_logDeriv_gaussianWeight]
    simp
    positivity

/-- The exact Gaussian curvature is bounded by the convenient constant `1/B`. -/
theorem hasCurvatureBound_gaussianVillainWeight {B : ℝ} (hB : 0 < B) :
    HasCurvatureBound (gaussianVillainWeight B) B⁻¹ := by
  intro t s
  rw [show gaussianVillainWeight B = gaussianWeight (B⁻¹) from rfl,
    gaussianWeight_ofReal, gaussianWeight_ofReal, gaussianWeight_logDeriv]
  simp only [Complex.ofReal_re, Real.log_exp]
  have hBinv : 0 ≤ B⁻¹ := (inv_pos.mpr hB).le
  have hre : (-( ((B⁻¹ : ℝ) : ℂ) * (t : ℂ))).re = -B⁻¹ * t := by
    simp [Complex.mul_re]
  rw [hre]
  nlinarith [sq_nonneg s]

/-- The quadratic Gaussian cost is an envelope with the coefficient required in the large-`B`
parameter choice used by the rooted T1.5-NG assembly. -/
theorem isCostEnvelope_gaussianVillainCost {B : ℝ} (hB : 0 < B) (W : ℝ) :
    IsCostEnvelope (gaussianVillainCost B) B⁻¹ B⁻¹ W := by
  have hBinv : 0 ≤ B⁻¹ := (inv_pos.mpr hB).le
  refine ⟨?_, ?_, hBinv, hBinv, ?_, ?_⟩
  · intro u; simp [gaussianVillainCost]
  · simp [gaussianVillainCost]
  · intro u hu
    dsimp [gaussianVillainCost]
    nlinarith [mul_nonneg hBinv (sq_nonneg u)]
  · intro u hu hW
    have hu0 : 0 ≤ |u| := abs_nonneg u
    have hlog : Real.log |u| ≤ |u| - 1 :=
      Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos hu)
    have hlog2 : 2 * Real.log |u| ≤ 2 * Real.pi * |u| := by
      have hpi := Real.two_le_pi
      nlinarith
    have hexp : |u| ^ 2 ≤ Real.exp (2 * Real.pi * |u|) := by
      have hpow : Real.exp (2 * Real.log |u|) = |u| ^ 2 := by
        rw [show 2 * Real.log |u| = Real.log |u| + Real.log |u| by ring,
          Real.exp_add, Real.exp_log (lt_of_lt_of_le one_pos hu)]
        ring
      rw [← hpow]
      exact Real.exp_le_exp.mpr hlog2
    dsimp [gaussianVillainCost]
    rw [← sq_abs]
    nlinarith [mul_nonneg hBinv (Real.exp_pos (2 * Real.pi * |u|)).le]

/-- All Gaussian estimates consumed by the rooted moment theorem at Villain inverse temperature
`B`. The strip can be chosen independently of the real weight. -/
theorem gaussianVillainWeight_data {B : ℝ} (hB : 0 < B) (W : ℝ) (hW : 0 ≤ W) :
    IsStripWeight (gaussianVillainWeight B) W (gaussianVillainCost B) ∧
      (∀ z : ℂ, |z.im| ≤ W → gaussianVillainWeight B z ≠ 0) ∧
      HasLogDerivBounds (gaussianVillainWeight B) W (fun u => B⁻¹ * |u|) ∧
      HasCurvatureBound (gaussianVillainWeight B) B⁻¹ ∧
      IsCostEnvelope (gaussianVillainCost B) B⁻¹ B⁻¹ W := by
  refine ⟨?_, ?_, hasLogDerivBounds_gaussianVillainWeight hB W,
    hasCurvatureBound_gaussianVillainWeight hB,
    isCostEnvelope_gaussianVillainCost hB W⟩
  · have hBinv : 0 < B⁻¹ := inv_pos.mpr hB
    change IsStripWeight (gaussianWeight B⁻¹) W (fun u => B⁻¹ / 2 * u ^ 2)
    exact isStripWeight_gaussianWeight hBinv hW
  · intro z hz
    exact gaussianWeight_ne_zero _ _

end FroehlichSpencer.BKT.Villain.TheoremC

end
