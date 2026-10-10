/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Green.Basic

/-!
# Regularity of finite-volume resolvent entries

The entries `resolventColumn a v Λ z y x` of the finite-volume resolvent are continuous and
measurable functions of the potential `v : X → ℝ` (product topology and product σ-algebra; they
depend only on `v|_Λ`), and continuous in `z` on `{Im z ≠ 0}`.

Motivation: finite-volume inputs
for the measurability of the infinite-volume Green function, cf.

Fröhlich–Spencer (1983),
Fröhlich–Spencer (1983).
-/

@[expose] public section

open Matrix

namespace FroehlichSpencer.Infra

variable {X : Type*} [DecidableEq X] {a : X → X → ℂ}

private theorem continuousOn_inv_apply {T Λ : Type*} [TopologicalSpace T] [Fintype Λ]
    [DecidableEq Λ] (M : T → Matrix Λ Λ ℂ) (hM : Continuous M) {S : Set T}
    (hdet : ∀ t ∈ S, (M t).det ≠ 0) (i j : Λ) :
    ContinuousOn (fun t => (M t)⁻¹ i j) S := by
  have h : ∀ t, (M t)⁻¹ i j = ((M t).det)⁻¹ * (M t).adjugate i j := by
    intro t
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  simp_rw [h]
  exact (hM.matrix_det.continuousOn.inv₀ hdet).mul
    (hM.matrix_adjugate.matrix_elem i j).continuousOn

private theorem det_ne_zero_restrictedOp (ha : ∀ x y, a y x = star (a x y)) (v : X → ℝ)
    (Λ : Finset X) {z : ℂ} (hz : z.im ≠ 0) :
    (restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp
    (FroehlichSpencer.Matrix.IsHermitian.isUnit_sub_zsmul_one_of_im_ne_zero _
      (isHermitian_restrictedOp ha v Λ) z hz)).ne_zero

private theorem continuous_restrictedOp_sub (a : X → X → ℂ) (Λ : Finset X) (z : ℂ) :
    Continuous fun w : Λ → ℝ =>
      (Matrix.of (fun x y : Λ => a x y) + Matrix.diagonal (fun x : Λ => (w x : ℂ)) -
        z • (1 : Matrix Λ Λ ℂ)) := by
  refine continuous_const.add ?_ |>.sub continuous_const
  refine continuous_matrix fun i j => ?_
  by_cases h : i = j
  · subst h
    simp only [diagonal_apply_eq]
    exact Complex.continuous_ofReal.comp (continuous_apply i)
  · simpa [Matrix.diagonal_apply_ne _ h] using continuous_const

private theorem continuous_entry_finite (ha : ∀ x y, a y x = star (a x y)) (Λ : Finset X)
    {z : ℂ} (hz : z.im ≠ 0) (i j : Λ) :
    Continuous fun w : Λ → ℝ =>
      ((Matrix.of (fun x y : Λ => a x y) + Matrix.diagonal (fun x : Λ => (w x : ℂ)) -
        z • (1 : Matrix Λ Λ ℂ))⁻¹) i j := by
  rw [← continuousOn_univ]
  refine continuousOn_inv_apply _ (continuous_restrictedOp_sub a Λ z) (fun w _ => ?_) i j
  have := det_ne_zero_restrictedOp ha (fun x => if h : x ∈ Λ then w ⟨x, h⟩ else 0) Λ hz
  simpa [restrictedOp] using this

private theorem resolventColumn_eq_finite (a : X → X → ℂ) (v : X → ℝ) (Λ : Finset X) (z : ℂ)
    (y x : X) (hx : x ∈ Λ) (hy : y ∈ Λ) :
    resolventColumn a v Λ z y x =
      ((Matrix.of (fun x y : Λ => a x y) +
        Matrix.diagonal (fun x : Λ => ((fun u : Λ => v u) x : ℂ)) -
        z • (1 : Matrix Λ Λ ℂ))⁻¹) ⟨x, hx⟩ ⟨y, hy⟩ :=
  resolventColumn_of_mem a v z hx hy

theorem continuous_resolventColumn (ha : ∀ x y, a y x = star (a x y)) (Λ : Finset X) {z : ℂ}
    (hz : z.im ≠ 0) (y x : X) :
    Continuous fun v : X → ℝ => resolventColumn a v Λ z y x := by
  by_cases h : x ∈ Λ ∧ y ∈ Λ
  · have : (fun v : X → ℝ => resolventColumn a v Λ z y x) = fun v =>
        ((Matrix.of (fun x y : Λ => a x y) +
          Matrix.diagonal (fun x : Λ => ((fun u : Λ => v u) x : ℂ)) -
          z • (1 : Matrix Λ Λ ℂ))⁻¹) ⟨x, h.1⟩ ⟨y, h.2⟩ :=
      funext fun v => resolventColumn_eq_finite a v Λ z y x h.1 h.2
    rw [this]
    exact (continuous_entry_finite ha Λ hz ⟨x, h.1⟩ ⟨y, h.2⟩).comp
      (continuous_pi fun u => continuous_apply (u : X))
  · have : (fun v : X → ℝ => resolventColumn a v Λ z y x) = fun _ => 0 :=
      funext fun v => by simp [resolventColumn, h]
    rw [this]
    exact continuous_const

theorem measurable_resolventColumn (ha : ∀ x y, a y x = star (a x y)) (Λ : Finset X) {z : ℂ}
    (hz : z.im ≠ 0) (y x : X) :
    Measurable fun v : X → ℝ => resolventColumn a v Λ z y x := by
  by_cases h : x ∈ Λ ∧ y ∈ Λ
  · have : (fun v : X → ℝ => resolventColumn a v Λ z y x) = (fun w : Λ → ℝ =>
        ((Matrix.of (fun x y : Λ => a x y) + Matrix.diagonal (fun x : Λ => (w x : ℂ)) -
          z • (1 : Matrix Λ Λ ℂ))⁻¹) ⟨x, h.1⟩ ⟨y, h.2⟩) ∘ (fun v (u : Λ) => v u) :=
      funext fun v => resolventColumn_eq_finite a v Λ z y x h.1 h.2
    rw [this]
    exact (continuous_entry_finite ha Λ hz ⟨x, h.1⟩ ⟨y, h.2⟩).measurable.comp
      (Measurable.of_eval fun u => measurable_pi_apply (u : X))
  · have : (fun v : X → ℝ => resolventColumn a v Λ z y x) = fun _ => 0 :=
      funext fun v => by simp [resolventColumn, h]
    rw [this]
    exact measurable_const

theorem continuousOn_resolventColumn (ha : ∀ x y, a y x = star (a x y)) (v : X → ℝ)
    (Λ : Finset X) (y x : X) :
    ContinuousOn (fun z : ℂ => resolventColumn a v Λ z y x) {z | z.im ≠ 0} := by
  by_cases h : x ∈ Λ ∧ y ∈ Λ
  · have : (fun z : ℂ => resolventColumn a v Λ z y x) = fun z =>
        ((restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ))⁻¹) ⟨x, h.1⟩ ⟨y, h.2⟩ :=
      funext fun z => resolventColumn_of_mem a v z h.1 h.2
    rw [this]
    refine continuousOn_inv_apply (fun z : ℂ => restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ))
      ?_ (fun z hz => det_ne_zero_restrictedOp ha v Λ hz) _ _
    exact continuous_const.sub (continuous_id.smul continuous_const)
  · have : (fun z : ℂ => resolventColumn a v Λ z y x) = fun _ => 0 :=
      funext fun z => by simp [resolventColumn, h]
    rw [this]
    exact continuousOn_const

end FroehlichSpencer.Infra
