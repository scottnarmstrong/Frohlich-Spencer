/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Shears of `ℝ^V` preserve Lebesgue measure (generic core)

The shear `S φ = φ + φ(j₀) u` with `u(j₀) = 0` is a unipotent linear map of `V → ℝ`: by the matrix
determinant lemma its determinant is `1 + u(j₀) = 1` (`det_shear`), so it preserves Lebesgue
measure (`measurePreserving_shear`), and it is invertible with inverse the shear by `-u`.

* the multi-site contour shift (`Generic/EdgeLaw/MultiSiteShift.lean`): a shear turns the
  simultaneous translation `φ ↦ φ + i a` into a translation of the single coordinate `j₀`;
* the normalization of the rooted edge law (`Generic/EdgeLaw/Normalization.lean`): a composition of
  shears maps a field to its increments along a spanning tree.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The shear `φ ↦ φ + φ(j₀) u`. -/
def shear (j₀ : V) (u : V → ℝ) : (V → ℝ) →ₗ[ℝ] (V → ℝ) :=
  LinearMap.id + (LinearMap.proj j₀ : (V → ℝ) →ₗ[ℝ] ℝ).smulRight u

omit [Fintype V] [DecidableEq V] in
@[simp] theorem shear_apply (j₀ : V) (u φ : V → ℝ) : shear j₀ u φ = φ + φ j₀ • u := rfl

omit [Fintype V] [DecidableEq V] in
theorem shear_apply_apply (j₀ : V) (u φ : V → ℝ) (j : V) :
    shear j₀ u φ j = φ j + φ j₀ * u j := rfl

omit [Fintype V] [DecidableEq V] in
/-- The shear by `-u` undoes the shear by `u` when `u(j₀) = 0`. -/
theorem shear_neg_shear {j₀ : V} {u : V → ℝ} (hu : u j₀ = 0) (φ : V → ℝ) :
    shear j₀ (-u) (shear j₀ u φ) = φ := by
  funext j
  simp only [shear_apply_apply, hu, mul_zero, add_zero, Pi.neg_apply]
  ring

omit [Fintype V] [DecidableEq V] in
theorem shear_shear_neg {j₀ : V} {u : V → ℝ} (hu : u j₀ = 0) (φ : V → ℝ) :
    shear j₀ u (shear j₀ (-u) φ) = φ := by
  have hu' : (-u) j₀ = 0 := by rw [Pi.neg_apply, hu, neg_zero]
  have := shear_neg_shear hu' φ
  rwa [neg_neg] at this

/-- The shear as a linear equivalence (`u(j₀) = 0`). -/
def shearEquiv {j₀ : V} {u : V → ℝ} (hu : u j₀ = 0) : (V → ℝ) ≃ₗ[ℝ] (V → ℝ) :=
  LinearEquiv.ofLinearMap (f := shear j₀ u) (g := shear j₀ (-u))
    (LinearMap.ext fun φ => shear_shear_neg hu φ) (LinearMap.ext fun φ => shear_neg_shear hu φ)

/-- The matrix determinant lemma: a shear with `u(j₀) = 0` has determinant one. -/
theorem det_shear {j₀ : V} {u : V → ℝ} (hu : u j₀ = 0) : LinearMap.det (shear j₀ u) = 1 := by
  rw [← LinearMap.det_toMatrix']
  have hmat : LinearMap.toMatrix' (shear j₀ u) =
      1 + Matrix.replicateCol Unit u * Matrix.replicateRow Unit (Pi.single j₀ (1 : ℝ)) := by
    ext i j
    rw [LinearMap.toMatrix'_apply, shear_apply_apply, Matrix.add_apply, Matrix.mul_apply]
    simp only [Matrix.replicateCol_apply, Matrix.replicateRow_apply, Finset.univ_unique,
      Finset.sum_singleton, Matrix.one_apply, Pi.single_apply]
    by_cases hij : i = j <;> by_cases h : j = j₀ <;> simp_all [eq_comm]
  rw [hmat, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct, Pi.single_apply, hu]

/-- A shear with `u(j₀) = 0` preserves Lebesgue measure on `V → ℝ`. -/
theorem measurePreserving_shear {j₀ : V} {u : V → ℝ} (hu : u j₀ = 0) :
    MeasurePreserving (shear j₀ u) (volume : Measure (V → ℝ)) volume := by
  refine ⟨(LinearMap.continuous_of_finiteDimensional (shear j₀ u)).measurable, ?_⟩
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi (by rw [det_shear hu]; exact one_ne_zero),
    det_shear hu, inv_one, abs_one, ENNReal.ofReal_one, one_smul]

omit [DecidableEq V] in
/-- A shear is a measurable embedding. -/
theorem measurableEmbedding_shear {j₀ : V} {u : V → ℝ} (hu : u j₀ = 0) :
    MeasurableEmbedding (shear j₀ u) :=
  (shearEquiv hu).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding

/-- Change of variables under a shear. -/
theorem integral_comp_shear {j₀ : V} {u : V → ℝ} (hu : u j₀ = 0) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : (V → ℝ) → F) :
    ∫ φ, f (shear j₀ u φ) = ∫ φ, f φ :=
  (measurePreserving_shear hu).integral_comp (measurableEmbedding_shear hu) f

/-- Integrability is invariant under a shear. -/
theorem integrable_comp_shear_iff {j₀ : V} {u : V → ℝ} (hu : u j₀ = 0) {F : Type*}
    [NormedAddCommGroup F] {f : (V → ℝ) → F} :
    Integrable (fun φ => f (shear j₀ u φ)) ↔ Integrable f :=
  (measurePreserving_shear hu).integrable_comp_emb (measurableEmbedding_shear hu)

/-- Change of variables under a shear, for lower integrals. -/
theorem lintegral_comp_shear {j₀ : V} {u : V → ℝ} (hu : u j₀ = 0) (f : (V → ℝ) → ENNReal) :
    ∫⁻ φ, f (shear j₀ u φ) = ∫⁻ φ, f φ :=
  (measurePreserving_shear hu).lintegral_comp_emb (measurableEmbedding_shear hu) f

end FroehlichSpencer.BKT.Generic

end
