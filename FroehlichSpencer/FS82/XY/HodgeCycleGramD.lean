/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.FiniteHodge
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Hodge inverse in cycle-basis coordinates

For a finite exact-one complex, choose a basis of the image of its second
differential and arbitrary lifts of that basis. The inverse-Hodge quadratic
on co-closed sources is the inverse Gram quadratic of their evaluations on
those lifts. This is the coordinate identity needed to use cycle coordinates
in finite Poisson summation.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Gaussian
open Module
open scoped InnerProductSpace

variable {V E P : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype P] [DecidableEq P]

/-- The Gram matrix of a basis of the image of the second differential. -/
noncomputable def hodgeImageGram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ExactOneComplex V E P) (b : Basis ι ℝ C.d₁.range) : Matrix ι ι ℝ :=
  Matrix.gram ℝ (fun i => b i)

/-- Coordinates of a co-closed source against chosen lifts of an image basis. -/
noncomputable def hodgeLiftCoordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ExactOneComplex V E P) (_b : Basis ι ℝ C.d₁.range)
    (lift : ι → EuclideanSpace ℝ E) (μ : coClosed C) : ι → ℝ :=
  fun i => inner ℝ (μ : EuclideanSpace ℝ E) (lift i)

/-- The inverse Hodge quadratic is the inverse Gram quadratic in lift
coordinates. No orthogonality of the chosen lifts is needed. -/
theorem hodgeInverseQuadratic_eq_inverseImageGram {ι : Type*}
    [Fintype ι] [DecidableEq ι] (C : ExactOneComplex V E P)
    (b : Basis ι ℝ C.d₁.range) (lift : ι → EuclideanSpace ℝ E)
    (hlift : ∀ i, C.d₁ (lift i) = (b i : EuclideanSpace ℝ P))
    (μ : coClosed C) :
    inner ℝ (μ : EuclideanSpace ℝ E)
        (hodgeInverseOnCoClosed C μ : EuclideanSpace ℝ E) =
      dotProduct (hodgeLiftCoordinates C b lift μ)
        ((hodgeImageGram C b)⁻¹.mulVec
          (hodgeLiftCoordinates C b lift μ)) := by
  let G := hodgeImageGram C b
  let q := hodgeLiftCoordinates C b lift μ
  let u := hodgeInverseOnCoClosed C μ
  let y : C.d₁.range := ⟨C.d₁ (u : EuclideanSpace ℝ E), ⟨u, rfl⟩⟩
  let a : ι → ℝ := b.equivFun y
  have hy : ∑ i, a i • b i = y := by
    simp [a]
  have hspec : formLaplacian C (u : EuclideanSpace ℝ E) = μ.1 := by
    exact congrArg Subtype.val (hodgeOnCoClosed_hodgeInverse C μ)
  have hq : G.mulVec a = q := by
    funext i
    have hqi : q i = inner ℝ y (b i) := by
      change inner ℝ μ.1 (lift i) =
        inner ℝ (C.d₁ (u : EuclideanSpace ℝ E))
          (b i : EuclideanSpace ℝ P)
      rw [← hspec, formLaplacian]
      change inner ℝ (C.d₁.adjoint (C.d₁ (u : EuclideanSpace ℝ E)))
          (lift i) = _
      rw [LinearMap.adjoint_inner_left C.d₁]
      rw [hlift i]
    calc
      (G.mulVec a) i = ∑ j, G i j * a j := by
        simp [Matrix.mulVec, dotProduct]
      _ = ∑ j, a j * G i j := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = inner ℝ y (b i) := by
        change ∑ j, a j * G i j =
          inner ℝ (y : EuclideanSpace ℝ P) (b i : EuclideanSpace ℝ P)
        have hy' : (∑ j, a j • C.d₁.range.subtype (b j)) =
            C.d₁.range.subtype y := by
          have h := congrArg C.d₁.range.subtype hy
          rw [map_sum] at h
          simpa only [map_smul] using h
        change ∑ j, a j * G i j =
          inner ℝ (C.d₁.range.subtype y)
            (C.d₁.range.subtype (b i))
        rw [← hy']
        rw [sum_inner]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [G, hodgeImageGram, Matrix.gram_apply]
        simp only [Submodule.coe_inner, real_inner_smul_left]
        conv_rhs => rw [real_inner_comm]
        have hbi : (b i : EuclideanSpace ℝ P) =
            C.d₁.range.subtype (b i) := rfl
        have hbj : (b j : EuclideanSpace ℝ P) =
            C.d₁.range.subtype (b j) := rfl
        rw [hbi, hbj]
      _ = q i := hqi.symm
  have hGpos : G.PosDef := by
    exact Matrix.posDef_gram_of_linearIndependent b.linearIndependent
  let _ : Invertible G := hGpos.isUnit.invertible
  have hGa : G⁻¹.mulVec q = a := by
    calc
      G⁻¹.mulVec q = G⁻¹.mulVec (G.mulVec a) := by rw [hq]
      _ = (G⁻¹ * G).mulVec a := by rw [Matrix.mulVec_mulVec]
      _ = a := by rw [Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  have hquad : inner ℝ μ.1 (u : EuclideanSpace ℝ E) =
      dotProduct a (G.mulVec a) := by
    calc
      inner ℝ μ.1 (u : EuclideanSpace ℝ E) =
          inner ℝ (formLaplacian C (u : EuclideanSpace ℝ E))
            (u : EuclideanSpace ℝ E) := by rw [hspec]
      _ = inner ℝ (C.d₁ (u : EuclideanSpace ℝ E))
          (C.d₁ (u : EuclideanSpace ℝ E)) :=
        LinearMap.adjoint_inner_left C.d₁ _ _
      _ = inner ℝ y y := rfl
      _ = dotProduct a (G.mulVec a) := by
        rw [← hy]
        simpa [G, hodgeImageGram] using
          (Matrix.star_dotProduct_gram_mulVec
            (fun i => b i) a a).symm
  change inner ℝ μ.1 (u : EuclideanSpace ℝ E) =
    dotProduct q (G⁻¹.mulVec q)
  calc
    _ = dotProduct a (G.mulVec a) := hquad
    _ = dotProduct (G.mulVec a) a := by rw [dotProduct_comm]
    _ = dotProduct q (G⁻¹.mulVec q) := by rw [hq, hGa]

/-- The mixed inverse-Hodge pairing is the inverse Gram pairing of the two
source coordinate vectors. This is the bilinear chart identity used for the
path phase after Poisson summation. -/
theorem hodgeInversePairing_eq_inverseImageGram {ι : Type*}
    [Fintype ι] [DecidableEq ι] (C : ExactOneComplex V E P)
    (b : Basis ι ℝ C.d₁.range) (lift : ι → EuclideanSpace ℝ E)
    (hlift : ∀ i, C.d₁ (lift i) = (b i : EuclideanSpace ℝ P))
    (μ ν : coClosed C) :
    inner ℝ μ (hodgeInverseOnCoClosed C ν) =
      dotProduct (hodgeLiftCoordinates C b lift μ)
        ((hodgeImageGram C b)⁻¹.mulVec
          (hodgeLiftCoordinates C b lift ν)) := by
  let G := hodgeImageGram C b
  let qμ := hodgeLiftCoordinates C b lift μ
  let qν := hodgeLiftCoordinates C b lift ν
  have hcoordAdd :
      hodgeLiftCoordinates C b lift (μ + ν) = qμ + qν := by
    funext i
    simp [hodgeLiftCoordinates, qμ, qν, inner_add_left]
  have hGpos : G.PosDef :=
    Matrix.posDef_gram_of_linearIndependent b.linearIndependent
  have hGsym : G.IsSymm := Matrix.isHermitian_iff_isSymm.mp hGpos.isHermitian
  have hInvSym : (G⁻¹).IsSymm := hGsym.inv
  have hmatrix :
      dotProduct (qμ + qν) (G⁻¹.mulVec (qμ + qν)) -
        dotProduct qμ (G⁻¹.mulVec qμ) -
        dotProduct qν (G⁻¹.mulVec qν) =
      2 * dotProduct qμ (G⁻¹.mulVec qν) := by
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
    rw [hInvSym.dotProduct_mulVec_comm (x := qν) (y := qμ)]
    ring
  have hcross : inner ℝ ν (hodgeInverseOnCoClosed C μ) =
      inner ℝ μ (hodgeInverseOnCoClosed C ν) := by
    calc
      _ = inner ℝ (hodgeInverseOnCoClosed C μ) ν := real_inner_comm _ _
      _ = _ := hodgeInverseOnCoClosed_symmetric C μ ν
  have hpolar :
      2 * inner ℝ μ (hodgeInverseOnCoClosed C ν) =
        inner ℝ (μ + ν) (hodgeInverseOnCoClosed C (μ + ν)) -
          inner ℝ μ (hodgeInverseOnCoClosed C μ) -
          inner ℝ ν (hodgeInverseOnCoClosed C ν) := by
    simp only [map_add, inner_add_left, inner_add_right]
    rw [hcross]
    ring
  have hsum := hodgeInverseQuadratic_eq_inverseImageGram C b lift hlift (μ + ν)
  have hμ := hodgeInverseQuadratic_eq_inverseImageGram C b lift hlift μ
  have hν := hodgeInverseQuadratic_eq_inverseImageGram C b lift hlift ν
  rw [hcoordAdd] at hsum
  have hsum' :
      inner ℝ (μ + ν) (hodgeInverseOnCoClosed C (μ + ν)) =
        dotProduct (qμ + qν) (G⁻¹.mulVec (qμ + qν)) := by
    simpa [G, qμ, qν] using hsum
  have hμ' : inner ℝ μ (hodgeInverseOnCoClosed C μ) =
      dotProduct qμ (G⁻¹.mulVec qμ) := by
    simpa [G, qμ] using hμ
  have hν' : inner ℝ ν (hodgeInverseOnCoClosed C ν) =
      dotProduct qν (G⁻¹.mulVec qν) := by
    simpa [G, qν] using hν
  change inner ℝ μ (hodgeInverseOnCoClosed C ν) =
    dotProduct qμ (G⁻¹.mulVec qν)
  have hdouble :
      2 * inner ℝ μ (hodgeInverseOnCoClosed C ν) =
        2 * dotProduct qμ (G⁻¹.mulVec qν) := by
    calc
      _ = inner ℝ (μ + ν) (hodgeInverseOnCoClosed C (μ + ν)) -
          inner ℝ μ (hodgeInverseOnCoClosed C μ) -
          inner ℝ ν (hodgeInverseOnCoClosed C ν) := hpolar
      _ = _ := by rw [hsum', hμ', hν', hmatrix]
  exact (mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hdouble)

end FroehlichSpencer.FS82.XY

end
