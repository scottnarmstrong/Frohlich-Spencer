/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.AxisEuclidean
import Mathlib.Analysis.InnerProductSpace.Adjoint

public section

open scoped BigOperators InnerProductSpace
namespace FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Cubical

variable {B : SourceBox}

@[expose] noncomputable def sumAxisEuclidean :
    EuclideanSpace ℝ (DualCell 4 B) →ₗ[ℝ]
      EuclideanSpace ℝ (DualCell 4 B) :=
  ∑ i : Fin 4, axisEuclidean (B := B) i

@[expose] noncomputable def sumAxisAdjointEuclidean :
    EuclideanSpace ℝ (DualCell 4 B) →ₗ[ℝ]
      EuclideanSpace ℝ (DualCell 4 B) :=
  ∑ i : Fin 4, axisAdjointEuclidean (B := B) i

theorem axisAdjoint_axis_anticommute (i j : Fin 4) (hij : i ≠ j)
    (x : EuclideanSpace ℝ (DualCell 4 B)) :
    axisAdjointEuclidean i (axisEuclidean j x) +
      axisEuclidean j (axisAdjointEuclidean i x) = 0 := by
  have h := congrArg (fun L : DualRealChain 4 B →ₗ[ℝ] DualRealChain 4 B =>
    L (euclideanToFinsupp x))
    (dualExteriorDifferenceAxisAdjoint_comp_anticommute i j hij)
  simp only [LinearMap.add_apply, LinearMap.comp_apply] at h
  have h' := congrArg (finsuppToEuclidean (α := DualCell 4 B)) h
  simpa [axisAdjointEuclidean, axisEuclidean, LinearMap.comp_apply,
    euclideanToFinsupp_finsuppToEuclidean] using h'

theorem sumAxis_hodge_operator (x : EuclideanSpace ℝ (DualCell 4 B)) :
    sumAxisAdjointEuclidean (sumAxisEuclidean x) +
      sumAxisEuclidean (sumAxisAdjointEuclidean x) =
        ∑ i : Fin 4,
          (axisAdjointEuclidean i (axisEuclidean i x) +
            axisEuclidean i (axisAdjointEuclidean i x)) := by
  classical
  change (∑ i : Fin 4,
      axisAdjointEuclidean i (∑ j : Fin 4, axisEuclidean j x)) +
    (∑ i : Fin 4,
      axisEuclidean i (∑ j : Fin 4, axisAdjointEuclidean j x)) = _
  calc
    (∑ i : Fin 4,
        axisAdjointEuclidean i (∑ j : Fin 4, axisEuclidean j x)) +
      (∑ i : Fin 4,
        axisEuclidean i (∑ j : Fin 4, axisAdjointEuclidean j x)) =
      (∑ i : Fin 4, ∑ j : Fin 4,
        axisAdjointEuclidean i (axisEuclidean j x)) +
      (∑ i : Fin 4, ∑ j : Fin 4,
        axisEuclidean i (axisAdjointEuclidean j x)) := by
          congr 1
          · apply Finset.sum_congr rfl
            intro i hi
            rw [map_sum]
          · apply Finset.sum_congr rfl
            intro i hi
            rw [map_sum]
    _ = (∑ i : Fin 4, ∑ j : Fin 4,
        axisAdjointEuclidean i (axisEuclidean j x)) +
      (∑ i : Fin 4, ∑ j : Fin 4,
        axisEuclidean j (axisAdjointEuclidean i x)) := by
          congr 1
          rw [Finset.sum_comm]
    _ = ∑ i : Fin 4, ∑ j : Fin 4,
        (axisAdjointEuclidean i (axisEuclidean j x) +
          axisEuclidean j (axisAdjointEuclidean i x)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_add_distrib]
    _ = ∑ i : Fin 4,
        (axisAdjointEuclidean i (axisEuclidean i x) +
          axisEuclidean i (axisAdjointEuclidean i x)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_eq_single i
            (by
              intro j hj hji
              exact axisAdjoint_axis_anticommute i j hji.symm x)
            (by simp)]

theorem sumAxis_adjoint_inner (x y : EuclideanSpace ℝ (DualCell 4 B)) :
    inner ℝ (sumAxisEuclidean x) y =
      inner ℝ x (sumAxisAdjointEuclidean y) := by
  change inner ℝ (∑ i : Fin 4, axisEuclidean i x) y =
    inner ℝ x (∑ i : Fin 4, axisAdjointEuclidean i y)
  rw [sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h := LinearMap.adjoint_inner_right
    (axisEuclidean (B := B) i) x y
  rw [axisEuclidean_adjoint] at h
  exact h.symm

theorem axisAdjoint_adjoint (i : Fin 4) :
    (axisAdjointEuclidean (B := B) i).adjoint =
      axisEuclidean (B := B) i := by
  rw [← axisEuclidean_adjoint, LinearMap.adjoint_adjoint]

theorem sumAxis_hodge_energy (x : EuclideanSpace ℝ (DualCell 4 B)) :
    ‖sumAxisEuclidean x‖^2 + ‖sumAxisAdjointEuclidean x‖^2 =
      ∑ i : Fin 4,
        (‖axisEuclidean i x‖^2 + ‖axisAdjointEuclidean i x‖^2) := by
  have hAx :
      inner ℝ (sumAxisEuclidean x) (sumAxisEuclidean x) =
        inner ℝ (sumAxisAdjointEuclidean (sumAxisEuclidean x)) x := by
    calc
      inner ℝ (sumAxisEuclidean x) (sumAxisEuclidean x) =
          inner ℝ x (sumAxisAdjointEuclidean (sumAxisEuclidean x)) :=
            sumAxis_adjoint_inner x (sumAxisEuclidean x)
      _ = inner ℝ (sumAxisAdjointEuclidean (sumAxisEuclidean x)) x :=
            real_inner_comm _ _
  have hBx :
      inner ℝ (sumAxisAdjointEuclidean x) (sumAxisAdjointEuclidean x) =
        inner ℝ (sumAxisEuclidean (sumAxisAdjointEuclidean x)) x := by
    have h := sumAxis_adjoint_inner (sumAxisAdjointEuclidean x) x
    exact h.symm
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hAx, hBx]
  rw [← inner_add_left, sumAxis_hodge_operator, sum_inner]
  simp_rw [inner_add_left]
  apply Finset.sum_congr rfl
  intro i hi
  have h₁ := LinearMap.adjoint_inner_left
    (axisEuclidean (B := B) i) x (axisEuclidean i x)
  have h₂ := LinearMap.adjoint_inner_left
    (axisAdjointEuclidean (B := B) i) x (axisAdjointEuclidean i x)
  rw [axisEuclidean_adjoint] at h₁
  rw [axisAdjoint_adjoint] at h₂
  rw [h₁, h₂, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

end FroehlichSpencer.FS82.Gaussian
end
