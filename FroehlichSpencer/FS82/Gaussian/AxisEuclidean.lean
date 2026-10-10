/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.AxisAdjoint
import Mathlib.Analysis.InnerProductSpace.Adjoint

public section

open scoped BigOperators InnerProductSpace
namespace FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Cubical

variable {B : SourceBox}

@[expose] noncomputable def axisEuclidean (i : Fin 4) :
    EuclideanSpace ℝ (DualCell 4 B) →ₗ[ℝ] EuclideanSpace ℝ (DualCell 4 B) :=
  finsuppToEuclidean.comp
    ((dualExteriorDifferenceAxis (B := B) i).comp euclideanToFinsupp)

@[expose] noncomputable def axisAdjointEuclidean (i : Fin 4) :
    EuclideanSpace ℝ (DualCell 4 B) →ₗ[ℝ] EuclideanSpace ℝ (DualCell 4 B) :=
  finsuppToEuclidean.comp
    ((dualExteriorDifferenceAxisAdjoint (B := B) i).comp euclideanToFinsupp)

theorem axisEuclidean_single (i : Fin 4) (c f : DualCell 4 B) :
    axisEuclidean i (EuclideanSpace.single c (1 : ℝ)) f =
      dualExteriorDifferenceAxisStencilBasis i c f := by
  simp [axisEuclidean, LinearMap.comp_apply, euclideanToFinsupp,
    EuclideanSpace.single, finsuppToEuclidean_apply]

theorem axisAdjointEuclidean_single (i : Fin 4) (c f : DualCell 4 B) :
    axisAdjointEuclidean i (EuclideanSpace.single c (1 : ℝ)) f =
      dualExteriorDifferenceAxisAdjointStencilBasis i c f := by
  simp [axisAdjointEuclidean, LinearMap.comp_apply, euclideanToFinsupp,
    EuclideanSpace.single, finsuppToEuclidean_apply]

theorem euclidean_coordinate_expansion
    (L : EuclideanSpace ℝ (DualCell 4 B) →ₗ[ℝ]
      EuclideanSpace ℝ (DualCell 4 B))
    (x : EuclideanSpace ℝ (DualCell 4 B)) (f : DualCell 4 B) :
    L x f = ∑ c : DualCell 4 B, x c * L (EuclideanSpace.single c 1) f := by
  have hdecomp : x = ∑ c : DualCell 4 B, x c • EuclideanSpace.single c (1 : ℝ) := by
    ext c
    rw [WithLp.ofLp_sum]
    rw [Finset.sum_apply c]
    calc
      x c = ∑ y : DualCell 4 B, (if c = y then x y else 0) := by
        symm
        exact Fintype.sum_ite_eq c (fun y : DualCell 4 B => x y)
      _ = ∑ y : DualCell 4 B, x y * EuclideanSpace.single y 1 c := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases h : c = y
        · subst y
          simp [EuclideanSpace.single]
        · simp [EuclideanSpace.single, h]
  conv_lhs => rw [hdecomp, map_sum, WithLp.ofLp_sum]
  simp only [map_smul, WithLp.ofLp_smul]
  rw [Finset.sum_apply f]
  simp only [Pi.smul_apply, smul_eq_mul]

theorem axisAdjointEuclidean_apply (i : Fin 4)
    (x : EuclideanSpace ℝ (DualCell 4 B)) (c : DualCell 4 B) :
    axisAdjointEuclidean i x c =
      ∑ y : DualCell 4 B,
        x y * dualExteriorDifferenceAxisAdjointStencilBasis i y c := by
  rw [euclidean_coordinate_expansion (axisAdjointEuclidean i) x c]
  apply Finset.sum_congr rfl
  intro y hy
  rw [axisAdjointEuclidean_single]

theorem axisEuclidean_adjoint (i : Fin 4) :
    (axisEuclidean (B := B) i).adjoint = axisAdjointEuclidean i := by
  classical
  apply LinearMap.ext
  intro x
  ext c
  have h := LinearMap.adjoint_inner_right
    (axisEuclidean (B := B) i) (EuclideanSpace.single c (1 : ℝ)) x
  have hleft :
      inner ℝ (axisEuclidean i (EuclideanSpace.single c (1 : ℝ))) x =
        ∑ y : DualCell 4 B,
          dualExteriorDifferenceAxisStencilBasis i c y * x y := by
    simp [PiLp.inner_apply, RCLike.inner_apply, axisEuclidean_single, mul_comm]
  have hright :
      inner ℝ (EuclideanSpace.single c (1 : ℝ))
          ((axisEuclidean i).adjoint x) = ((axisEuclidean i).adjoint x) c := by
    rw [PiLp.inner_apply]
    simp [EuclideanSpace.single]
  calc
    ((axisEuclidean i).adjoint x) c =
        inner ℝ (EuclideanSpace.single c (1 : ℝ))
          ((axisEuclidean i).adjoint x) := hright.symm
    _ = inner ℝ (axisEuclidean i (EuclideanSpace.single c (1 : ℝ))) x := h
    _ = ∑ y : DualCell 4 B,
        dualExteriorDifferenceAxisStencilBasis i c y * x y := hleft
    _ = axisAdjointEuclidean i x c := by
      rw [axisAdjointEuclidean_apply]
      apply Finset.sum_congr rfl
      intro y hy
      rw [axisStencilCoefficient_symm]
      ring

end FroehlichSpencer.FS82.Gaussian
end
