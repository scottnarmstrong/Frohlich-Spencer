/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Surface.GaussianLaw
public import FroehlichSpencer.Surface.BoundedDensityLaw
import Mathlib.Tactic

/-! # Bounded density of the Gaussian single-site law -/

public section

namespace FroehlichSpencer

/-- The Gaussian law has the bounded density from its source formula (1.14). -/
theorem has_bounded_density_gaussian_law (γ : ℝ) (hγ : 0 < γ) :
    HasBoundedDensity (gaussianLaw γ hγ) (Real.sqrt (2 * Real.pi * γ)) := by
  let v : NNReal := ⟨γ, le_of_lt hγ⟩
  have hv : v ≠ 0 := by
    intro he
    have hval : (v : ℝ) = 0 := congrArg (fun x : NNReal => (x : ℝ)) he
    have : γ = 0 := by change γ = 0 at hval; exact hval
    linarith
  have hδ : 0 < Real.sqrt (2 * Real.pi * γ) := by positivity
  refine ⟨hδ, ProbabilityTheory.gaussianPDF 0 v, ?_, ?_, ?_⟩
  · exact ProbabilityTheory.measurable_gaussianPDF 0 v
  · change ProbabilityTheory.gaussianReal 0 v = _
    rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 hv]
  · intro t
    apply ENNReal.ofReal_le_ofReal
    have harg : -(t - 0) ^ 2 / (2 * γ) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · exact neg_nonpos.mpr (sq_nonneg (t - 0))
      · positivity
    have hexp : Real.exp (-(t - 0) ^ 2 / (2 * γ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr harg
    have hcoef : 0 ≤ (Real.sqrt (2 * Real.pi * γ))⁻¹ := by positivity
    have hreal : ProbabilityTheory.gaussianPDFReal 0 v t ≤
        (Real.sqrt (2 * Real.pi * γ))⁻¹ := by
      rw [ProbabilityTheory.gaussianPDFReal]
      calc
        (Real.sqrt (2 * Real.pi * γ))⁻¹ * Real.exp (-(t - 0) ^ 2 / (2 * γ)) ≤
            (Real.sqrt (2 * Real.pi * γ))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hexp hcoef
        _ = (Real.sqrt (2 * Real.pi * γ))⁻¹ := by ring
    simpa [ProbabilityTheory.gaussianPDF, v] using hreal

end FroehlichSpencer

end
