/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Stieltjes.EigenvalueMeasure
public import FroehlichSpencer.Infra.Stieltjes.Transform
public import FroehlichSpencer.Infra.Spectral.Regularity
public import FroehlichSpencer.Infra.Spectral.ResolventNorm
public import Mathlib.Probability.Kernel.Basic

/-!
# Properties of the eigenvalue counting measure and the induced kernel

Values of `eigenvalueMeasure hH = |ι|⁻¹ ∑ δ_{λ_i}` on measurable sets, finiteness, the
distribution function `eigenvalueCount hH E / |ι|`, the Stieltjes transform
`|ι|⁻¹ Tr (H - z)⁻¹`, measurability in the potential for `A + diagonal (v ∘ f)`, and the Markov
kernel `v ↦ eigenvalueMeasure (A + diagonal (v ∘ f))`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Filter Topology Set Matrix Finset
open scoped ENNReal

namespace FroehlichSpencer.Infra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}

open Classical in
theorem eigenvalueMeasure_apply (hH : H.IsHermitian) {s : Set ℝ} (hs : MeasurableSet s) :
    eigenvalueMeasure hH s = ((Fintype.card ι : ℝ≥0∞)⁻¹) * #{i | hH.eigenvalues i ∈ s} := by
  rw [eigenvalueMeasure_def, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.dirac_apply' _ hs, smul_eq_mul]
  congr 1
  rw [Finset.card_filter]
  push_cast
  rfl

theorem eigenvalueMeasure_univ_le_one (hH : H.IsHermitian) : eigenvalueMeasure hH univ ≤ 1 := by
  rw [eigenvalueMeasure_def, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  by_cases h : Fintype.card ι = 0
  · simp [h]
  · exact (ENNReal.inv_mul_cancel (by exact_mod_cast h) (ENNReal.natCast_ne_top _)).le

instance isFiniteMeasure_eigenvalueMeasure (hH : H.IsHermitian) :
    IsFiniteMeasure (eigenvalueMeasure hH) := by
  rw [eigenvalueMeasure_def]
  have : IsFiniteMeasure (∑ i, Measure.dirac (hH.eigenvalues i)) := by
    have : ∀ i, IsFiniteMeasure (Measure.dirac (hH.eigenvalues i)) := fun _ => inferInstance
    infer_instance
  refine ⟨?_⟩
  rw [Measure.smul_apply, smul_eq_mul]
  by_cases h : Fintype.card ι = 0
  · have := Fintype.card_eq_zero_iff.mp h
    simp
  · exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (by positivity)) (measure_lt_top _ _)

theorem isProbabilityMeasure_eigenvalueMeasure [Nonempty ι] (hH : H.IsHermitian) :
    IsProbabilityMeasure (eigenvalueMeasure hH) := by
  refine ⟨?_⟩
  rw [eigenvalueMeasure_def, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  have h0 : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card ι := Fintype.card_pos
    positivity
  exact ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top _)

theorem measureReal_eigenvalueMeasure_Iic (hH : H.IsHermitian) (E : ℝ) :
    (eigenvalueMeasure hH).real (Iic E) = eigenvalueCount hH E / Fintype.card ι := by
  classical
  rw [Measure.real, eigenvalueMeasure_apply hH measurableSet_Iic]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    inv_mul_eq_div]
  rfl

theorem stieltjes_eigenvalueMeasure (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    stieltjes (eigenvalueMeasure hH) z =
      (Fintype.card ι : ℂ)⁻¹ * ((H - z • (1 : Matrix ι ι ℂ))⁻¹).trace := by
  have hne : ∀ i, (hH.eigenvalues i : ℂ) ≠ z := fun i h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have htr : ((H - z • (1 : Matrix ι ι ℂ))⁻¹).trace =
      ∑ i, ((hH.eigenvalues i : ℂ) - z)⁻¹ := by
    rw [inv_sub_smul_one_eq hH z hne, Matrix.trace_mul_comm, ← mul_assoc]
    have hU : star (hH.eigenvectorUnitary : Matrix ι ι ℂ) * (hH.eigenvectorUnitary : Matrix ι ι ℂ)
        = 1 := Unitary.coe_star_mul_self _
    rw [hU, one_mul, Matrix.trace_diagonal]
  have hc : eigenvalueMeasure hH =
      ((Fintype.card ι : NNReal)⁻¹) • ∑ i, Measure.dirac (hH.eigenvalues i) := by
    rw [eigenvalueMeasure_def]
    ext t ht
    by_cases h : Fintype.card ι = 0
    · have := Fintype.card_eq_zero_iff.mp h
      simp
    · simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
      rw [ENNReal.coe_inv (by exact_mod_cast h)]
      simp
  rw [hc, stieltjes_smul, stieltjes_sum_dirac, htr]
  simp

theorem measurable_eigenvalueMeasure_apply {J : Type*} {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (f : ι → J) {s : Set ℝ} (hs : MeasurableSet s) :
    Measurable fun v : J → ℝ =>
      eigenvalueMeasure (isHermitian_add_diagonal hA fun i => v (f i)) s := by
  classical
  have h : ∀ v : J → ℝ,
      eigenvalueMeasure (isHermitian_add_diagonal hA fun i => v (f i)) s =
      ((Fintype.card ι : ℝ≥0∞)⁻¹) *
        ∑ i, if (isHermitian_add_diagonal hA fun i => v (f i)).eigenvalues i ∈ s
          then (1 : ℝ≥0∞) else 0 := by
    intro v
    rw [eigenvalueMeasure_apply _ hs, Finset.card_filter]
    push_cast
    rfl
  simp_rw [h]
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
  have hm := measurable_eigenvalues (measurable_add_diagonal_comp A f)
    (fun v => isHermitian_add_diagonal hA fun i => v (f i)) i
  exact Measurable.ite (hm hs) measurable_const measurable_const

/-- The kernel `v ↦` eigenvalue counting measure of `A + diagonal (v ∘ f)`. -/
noncomputable def eigenvalueKernel {J : Type*} {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (f : ι → J) : Kernel (J → ℝ) ℝ :=
  Kernel.mk (fun v => eigenvalueMeasure (isHermitian_add_diagonal hA fun i => v (f i)))
    (Measure.measurable_of_measurable_coe _ fun _ hs =>
      measurable_eigenvalueMeasure_apply hA f hs)

theorem eigenvalueKernel_apply {J : Type*} {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ι → J)
    (v : J → ℝ) :
    eigenvalueKernel hA f v = eigenvalueMeasure (isHermitian_add_diagonal hA fun i => v (f i)) :=
  rfl

instance {J : Type*} {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ι → J) :
    IsFiniteKernel (eigenvalueKernel hA f) :=
  ⟨⟨1, ENNReal.one_lt_top, fun v => by
    rw [eigenvalueKernel_apply]
    exact eigenvalueMeasure_univ_le_one _⟩⟩

instance [Nonempty ι] {J : Type*} {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ι → J) :
    IsMarkovKernel (eigenvalueKernel hA f) :=
  ⟨fun v => by
    rw [eigenvalueKernel_apply]
    exact isProbabilityMeasure_eigenvalueMeasure _⟩

end FroehlichSpencer.Infra
