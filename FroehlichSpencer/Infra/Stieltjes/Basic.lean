/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Measure.ResolventTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Stieltjes transform of a measure on `ℝ` and the Poisson kernel

`stieltjes μ z = ∫ t, (t - z)⁻¹ dμ(t)` for a measure `μ` on `ℝ` and `z ∈ ℂ` (meaningful for
`Im z ≠ 0`; it is Mathlib's `MeasureTheory.resolventTransform` specialised to `ℝ → ℂ`), and the
Poisson kernel of the upper half-plane `poissonKernel η x = η / (π (x² + η²))`, which satisfies
`Im (t - (E + iη))⁻¹ = π · poissonKernel η (t - E)`.

Motivation: the integrated density of states
of Fröhlich–Spencer (1983), (1.10), Fröhlich–Spencer (1983), is recovered from Stieltjes
transforms of eigenvalue counting measures; nothing here is model specific.
-/

@[expose] public section

open MeasureTheory Complex

namespace FroehlichSpencer.Infra

/-- The Stieltjes transform `S_μ(z) = ∫ (t - z)⁻¹ dμ(t)` of a measure on `ℝ`. -/
noncomputable def stieltjes (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ t, ((t : ℂ) - z)⁻¹ ∂μ

/-- The Poisson kernel of the upper half-plane, `P_η(x) = η / (π (x² + η²))`. -/
noncomputable def poissonKernel (η x : ℝ) : ℝ :=
  η / (Real.pi * (x ^ 2 + η ^ 2))

theorem stieltjes_def (μ : Measure ℝ) (z : ℂ) :
    stieltjes μ z = ∫ t, ((t : ℂ) - z)⁻¹ ∂μ := rfl

/-- The Stieltjes transform is Mathlib's resolvent transform for `ℝ → ℂ`. -/
theorem stieltjes_eq_resolventTransform (μ : Measure ℝ) (z : ℂ) :
    stieltjes μ z = resolventTransform μ z := by
  rw [stieltjes, resolventTransform_apply]
  congr 1
  funext t
  simp [resolvent, Ring.inverse_eq_inv', Algebra.algebraMap_eq_smul_one]

theorem im_inv_ofReal_sub (t E η : ℝ) :
    (((t : ℂ) - (E + η * I))⁻¹).im = η / ((t - E) ^ 2 + η ^ 2) := by
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [sub_im, ofReal_im, add_im, mul_im, I_re, I_im, ofReal_re, sub_re, add_re, mul_re]
  ring_nf

theorem im_inv_ofReal_sub_eq_poissonKernel (t E η : ℝ) :
    (((t : ℂ) - (E + η * I))⁻¹).im = Real.pi * poissonKernel η (t - E) := by
  rw [im_inv_ofReal_sub, poissonKernel]
  have : (0 : ℝ) < Real.pi := Real.pi_pos
  by_cases h : (t - E) ^ 2 + η ^ 2 = 0
  · rw [h]; simp
  · field_simp

end FroehlichSpencer.Infra
