/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.SourceLiftPoincare

public section

open scoped InnerProductSpace
namespace FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Cubical

/-- The compressed physical stencil's quadratic form is the curl energy. -/
theorem latticeStencil_inner_eq_d1_norm_sq {B : SourceBox}
    (origin : Fin 4 → ℤ)
    (τ : EuclideanSpace ℝ (SourceDualOneCells B)) :
    inner ℝ τ (latticeStencilOperator origin τ) =
      ‖(latticeExactOneComplex (B := B) origin).d₁ τ‖ ^ 2 := by
  calc
    inner ℝ τ (latticeStencilOperator origin τ) =
        inner ℝ τ (formLaplacian (latticeExactOneComplex (B := B) origin) τ) := by
          rw [← latticeFormLaplacian_eq_stencil]
    _ = inner ℝ
        ((latticeExactOneComplex (B := B) origin).d₁ τ)
        ((latticeExactOneComplex (B := B) origin).d₁ τ) := by
          change inner ℝ τ
            (((latticeExactOneComplex (B := B) origin).d₁).adjoint
              ((latticeExactOneComplex (B := B) origin).d₁ τ)) = _
          exact LinearMap.adjoint_inner_right
            ((latticeExactOneComplex (B := B) origin).d₁) τ
            ((latticeExactOneComplex (B := B) origin).d₁ τ)
    _ = _ := real_inner_self_eq_norm_sq _

/-- The physical co-closed one-forms satisfy the finite-box Poincare bound
with constant `c = 1`. -/
theorem latticeW_poincare {B : SourceBox} (origin : Fin 4 → ℤ) (N : ℕ)
    (hB : ∀ i : Fin 4, B i ≤ N)
    (τ : coClosed (latticeExactOneComplex (B := B) origin)) :
    ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖ ^ 2 ≤
      ((N + 1 : ℕ) : ℝ) ^ 2 *
        inner ℝ (τ : EuclideanSpace ℝ (SourceDualOneCells B))
          (latticeStencilOperator origin τ) := by
  let T := sourceDualTLinear (B := B)
  let x := sourceOneLift (T (τ : EuclideanSpace ℝ (SourceDualOneCells B)))
  have hTadj : T.adjoint = T := sourceDualTLinear_symmetric.adjoint_eq
  have hTnorm (u : EuclideanSpace ℝ (SourceDualOneCells B)) :
      ‖T u‖ ^ 2 = ‖u‖ ^ 2 := by
    calc
      ‖T u‖ ^ 2 = inner ℝ (T u) (T u) :=
        (real_inner_self_eq_norm_sq (T u)).symm
      _ = inner ℝ u (T.adjoint (T u)) :=
        (LinearMap.adjoint_inner_right T u (T u)).symm
      _ = inner ℝ u u := by
        rw [hTadj]
        change inner ℝ u (sourceDualTLinear (sourceDualTLinear u)) = _
        rw [sourceDualTLinear_apply_apply]
      _ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
  have hcoτ :
      ((latticeExactOneComplex (B := B) origin).d₀.adjoint)
        (τ : EuclideanSpace ℝ (SourceDualOneCells B)) = 0 :=
    LinearMap.mem_ker.mp τ.property
  have hco : sourceDualD₀.adjoint
      (T (τ : EuclideanSpace ℝ (SourceDualOneCells B))) = 0 := by
    have h := hcoτ
    change ((T.comp sourceDualD₀).adjoint)
      (τ : EuclideanSpace ℝ (SourceDualOneCells B)) = 0 at h
    rw [LinearMap.adjoint_comp, hTadj] at h
    simpa [LinearMap.comp_apply] using h
  have hclosed : sumAxisAdjointEuclidean x = 0 := by
    dsimp [x]
    exact sumAxisAdjoint_sourceOneLift_eq_zero _ hco
  have hdegree : ∀ q : DualCell 4 B, dualCellDegree q ≠ 1 → x q = 0 := by
    intro q hq
    dsimp [x]
    exact sourceOneLift_apply_of_ne_degree _ q hq
  have hfull := fullOneForm_poincare N hB x hdegree hclosed
  have hnormx :
      ‖x‖ ^ 2 = ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖ ^ 2 := by
    calc
      ‖x‖ ^ 2 =
          ‖T (τ : EuclideanSpace ℝ (SourceDualOneCells B))‖ ^ 2 := by
            dsimp [x]
            calc
              ‖sourceOneLift (T (τ : EuclideanSpace ℝ (SourceDualOneCells B)))‖ ^ 2 =
                  inner ℝ
                    (sourceOneLift (T (τ : EuclideanSpace ℝ (SourceDualOneCells B))))
                    (sourceOneLift (T (τ : EuclideanSpace ℝ (SourceDualOneCells B)))) :=
                      (real_inner_self_eq_norm_sq _).symm
              _ = inner ℝ (T (τ : EuclideanSpace ℝ (SourceDualOneCells B)))
                    (T (τ : EuclideanSpace ℝ (SourceDualOneCells B))) :=
                      sourceOneLift_inner _ _
              _ = ‖T (τ : EuclideanSpace ℝ (SourceDualOneCells B))‖ ^ 2 :=
                    real_inner_self_eq_norm_sq _
      _ = ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖ ^ 2 :=
            hTnorm _
  have hcurlmap : sourceDualD₁ (T (τ : EuclideanSpace ℝ (SourceDualOneCells B))) =
      (latticeExactOneComplex (B := B) origin).d₁
        (τ : EuclideanSpace ℝ (SourceDualOneCells B)) := rfl
  have hnormcurl : ‖sumAxisEuclidean x‖ ^ 2 =
      ‖(latticeExactOneComplex (B := B) origin).d₁
        (τ : EuclideanSpace ℝ (SourceDualOneCells B))‖ ^ 2 := by
    calc
      ‖sumAxisEuclidean x‖ ^ 2 =
          ‖sourceTwoLift (sourceDualD₁
            (T (τ : EuclideanSpace ℝ (SourceDualOneCells B))))‖ ^ 2 := by
              rw [sourceOneLift_sumAxis_eq_d1]
      _ = ‖sourceDualD₁
            (T (τ : EuclideanSpace ℝ (SourceDualOneCells B)))‖ ^ 2 := by
              calc
                _ = inner ℝ
                    (sourceTwoLift (sourceDualD₁
                      (T (τ : EuclideanSpace ℝ (SourceDualOneCells B)))))
                    (sourceTwoLift (sourceDualD₁
                      (T (τ : EuclideanSpace ℝ (SourceDualOneCells B))))) :=
                        (real_inner_self_eq_norm_sq _).symm
                _ = inner ℝ
                    (sourceDualD₁ (T (τ : EuclideanSpace ℝ (SourceDualOneCells B))))
                    (sourceDualD₁ (T (τ : EuclideanSpace ℝ (SourceDualOneCells B)))) :=
                        sourceTwoLift_inner _ _
                _ = _ := real_inner_self_eq_norm_sq _
      _ = _ := by rw [hcurlmap]
  have henergy := latticeStencil_inner_eq_d1_norm_sq origin
    (τ : EuclideanSpace ℝ (SourceDualOneCells B))
  calc
    ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖ ^ 2 = ‖x‖ ^ 2 := hnormx.symm
    _ ≤ ((N + 1 : ℕ) : ℝ) ^ 2 * ‖sumAxisEuclidean x‖ ^ 2 := hfull
    _ = ((N + 1 : ℕ) : ℝ) ^ 2 *
        ‖(latticeExactOneComplex (B := B) origin).d₁
          (τ : EuclideanSpace ℝ (SourceDualOneCells B))‖ ^ 2 := by rw [hnormcurl]
    _ = ((N + 1 : ℕ) : ℝ) ^ 2 *
        inner ℝ (τ : EuclideanSpace ℝ (SourceDualOneCells B))
          (latticeStencilOperator origin τ) := by rw [← henergy]


end FroehlichSpencer.FS82.Gaussian
end
