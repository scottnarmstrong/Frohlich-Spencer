module
public import FroehlichSpencer.FS82.Poisson.Scalar
public import FroehlichSpencer.FS82.Poisson.PiSplit
public import FroehlichSpencer.FS82.Poisson.Block
public import FroehlichSpencer.FS82.Poisson.QuadScalar
public import FroehlichSpencer.FS82.Poisson.GaussianSummable
public import FroehlichSpencer.FS82.Poisson.DualSummable
public import FroehlichSpencer.FS82.Poisson.ProductSummable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

@[expose] public section

namespace FroehlichSpencer.FS82.Poisson

open Complex Matrix
noncomputable section

def finVector (n : ℕ) (x : Fin n → ℤ) (k : ℤ) : Fin (n + 1) → ℤ :=
  finSumPiEquiv n (x, k)

def finBilinear (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (x : Fin n → ℤ) : ℂ := ∑ i, (blkB A i 0 : ℂ) * (x i : ℂ)

def finQuad (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℤ) : ℂ :=
  ∑ i, ∑ j, (x i : ℂ) * (A i j : ℂ) * (x j : ℂ)

def finLinear (n : ℕ) (w : Fin (n + 1) → ℂ) (x : Fin n → ℤ) : ℂ :=
  ∑ i, w (Fin.castSucc i) * (x i : ℂ)

def finSchur (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  blkD A - blkB A * (blkE A)⁻¹ * (blkB A).conjTranspose

def finScalar (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : ℝ :=
  blkE A 0 0

def finSchurSource (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (w : Fin (n + 1) → ℂ) (l : ℤ) : Fin n → ℂ := fun i =>
  w (Fin.castSucc i) - (blkB A i 0 : ℂ) / (finScalar n A : ℂ) *
    (w (Fin.last n) - I * (l : ℂ))

theorem fin_linear_split (n : ℕ) (w : Fin (n + 1) → ℂ)
    (x : Fin n → ℤ) (k : ℤ) :
    (∑ i, w i * (finVector n x k i : ℂ)) =
      finLinear n w x + w (Fin.last n) * (k : ℂ) := by
  rw [Fin.sum_univ_castSucc]
  simp [finVector, finLinear]

theorem fin_quad_reindex (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (x : Fin n → ℤ) (k : ℤ) :
    (∑ i, ∑ j, (finVector n x k i : ℂ) * (A i j : ℂ) * (finVector n x k j : ℂ)) =
      (∑ s, ∑ t, ((piSumEquiv n).symm (x, k) s : ℂ) *
        ((reA A s t : ℝ) : ℂ) * ((piSumEquiv n).symm (x, k) t : ℂ)) := by
  classical
  unfold finVector finSumPiEquiv
  refine Fintype.sum_equiv (eFin n).symm _ _ ?_
  intro i
  refine Fintype.sum_equiv (eFin n).symm _ _ ?_
  intro j
  simp [reA, eFin, Matrix.reindex_apply, Equiv.piCongrLeft_apply, piSumEquiv]

theorem fin_quad_split (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef)
    (x : Fin n → ℤ) (k : ℤ) :
    (∑ i, ∑ j, (finVector n x k i : ℂ) * (A i j : ℂ) * (finVector n x k j : ℂ)) =
      finQuad n (blkD A) x + 2 * (k : ℂ) * finBilinear n A x +
        (blkE A 0 0 : ℂ) * (k : ℂ) ^ 2 := by
  rw [fin_quad_reindex]
  simpa [finQuad, finBilinear] using reindexed_quad_split A hA x k

theorem fin_exponent_split (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef)
    (w : Fin (n + 1) → ℂ) (x : Fin n → ℤ) (k : ℤ) :
    -(Real.pi : ℂ) *
        (∑ i, ∑ j, (finVector n x k i : ℂ) * (A i j : ℂ) * (finVector n x k j : ℂ)) +
        2 * Real.pi * ∑ i, w i * (finVector n x k i : ℂ) =
      (-(Real.pi : ℂ) * finQuad n (blkD A) x +
          2 * Real.pi * finLinear n w x) +
        (-(Real.pi : ℂ) * (blkE A 0 0 : ℂ) * (k : ℂ) ^ 2 +
          2 * Real.pi * (w (Fin.last n) - finBilinear n A x) * (k : ℂ)) := by
  rw [fin_quad_split n A hA, fin_linear_split]
  ring

theorem fin_scalar_pos (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef) :
    0 < finScalar n A := by
  exact (reA_posdef hA).diag_pos (i := Sum.inr 0)

theorem fin_schur_pos (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef) :
    (finSchur n A).PosDef := by
  simpa [finSchur] using (schur_block_posdef hA)

theorem fin_block_scalar_inv (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (ha : 0 < finScalar n A) :
    (blkE A)⁻¹ 0 0 = (finScalar n A)⁻¹ := by
  let E := blkE A
  let a := finScalar n A
  have hE : E = Matrix.diagonal (fun _ : Fin 1 => a) := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  have hleft : (Matrix.diagonal (fun _ : Fin 1 => a⁻¹)) * E = 1 := by
    rw [hE]
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Matrix.diagonal]
    exact inv_mul_cancel₀ (ne_of_gt ha)
  have hinv : E⁻¹ = Matrix.diagonal (fun _ : Fin 1 => a⁻¹) :=
    Matrix.inv_eq_left_inv hleft
  simp [E, a, hinv, Matrix.diagonal]

theorem fin_schur_entry (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef) (i j : Fin n) :
    finSchur n A i j = blkD A i j -
      blkB A i 0 * (finScalar n A)⁻¹ * blkB A j 0 := by
  have hentry :
      (blkB A * (blkE A)⁻¹ * (blkB A).conjTranspose) i j =
        blkB A i 0 * (finScalar n A)⁻¹ * blkB A j 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply]
    rw [fin_block_scalar_inv n A (fin_scalar_pos n A hA)]
    simp
  change blkD A i j - (blkB A * (blkE A)⁻¹ * (blkB A).conjTranspose) i j = _
  rw [hentry]

theorem fin_schur_quad (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef)
    (x : Fin n → ℤ) :
    finQuad n (finSchur n A) x = finQuad n (blkD A) x -
      (finScalar n A)⁻¹ * (finBilinear n A x) ^ 2 := by
  simp only [finQuad]
  simp_rw [fin_schur_entry n A hA]
  simp_rw [Complex.ofReal_sub, Complex.ofReal_mul, mul_sub]
  simp_rw [sub_mul]
  simp_rw [Finset.sum_sub_distrib]
  have hdouble :
      (∑ i, ∑ j, (x i : ℂ) * ((blkB A i 0 : ℂ) *
        ((finScalar n A)⁻¹ : ℂ) * (blkB A j 0 : ℂ)) * (x j : ℂ)) =
        ((finScalar n A)⁻¹ : ℂ) * (finBilinear n A x) ^ 2 := by
    let f : Fin n → ℂ := fun i => (blkB A i 0 : ℂ) * (x i : ℂ)
    have hprod :
        (∑ i, ∑ j, f i * f j) = (∑ i, f i) * (∑ j, f j) := by
      calc
        _ = ∑ i, f i * ∑ j, f j := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← Finset.mul_sum]
        _ = _ := by rw [← Finset.sum_mul]
    have hcoeff :
        (∑ i, ∑ j, ((finScalar n A)⁻¹ : ℂ) * (f i * f j)) =
          ((finScalar n A)⁻¹ : ℂ) * (∑ i, ∑ j, f i * f j) := by
      calc
        _ = ∑ i, ((finScalar n A)⁻¹ : ℂ) * ∑ j, f i * f j := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← Finset.mul_sum]
        _ = _ := by rw [← Finset.mul_sum]
    calc
      _ = ∑ i, ∑ j, ((finScalar n A)⁻¹ : ℂ) * (f i * f j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ((finScalar n A)⁻¹ : ℂ) * (∑ i, ∑ j, f i * f j) := hcoeff
      _ = ((finScalar n A)⁻¹ : ℂ) * ((∑ i, f i) * (∑ j, f j)) := by rw [hprod]
      _ = _ := by simp [finBilinear, f, pow_two]
  have hcast : ((finScalar n A)⁻¹ : ℂ) = ((finScalar n A)⁻¹ : ℝ) := by simp
  rw [← hcast, hdouble]

theorem fin_schur_source_linear (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (w : Fin (n + 1) → ℂ)
    (x : Fin n → ℤ) (l : ℤ) :
    (∑ i, finSchurSource n A w l i * (x i : ℂ)) =
      finLinear n w x -
        ((w (Fin.last n) - I * (l : ℂ)) / (finScalar n A : ℂ)) * finBilinear n A x := by
  unfold finSchurSource finLinear finBilinear
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  have hfactor :
      (∑ i, ((blkB A i 0 : ℂ) / (finScalar n A : ℂ) *
        (w (Fin.last n) - I * (l : ℂ))) * (x i : ℂ)) =
        ((w (Fin.last n) - I * (l : ℂ)) / (finScalar n A : ℂ)) *
          (∑ i, (blkB A i 0 : ℂ) * (x i : ℂ)) := by
    calc
      _ = ∑ i, ((w (Fin.last n) - I * (l : ℂ)) /
          (finScalar n A : ℂ)) * ((blkB A i 0 : ℂ) * (x i : ℂ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [Finset.mul_sum]
  rw [hfactor]

theorem fin_schur_complete_square (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef)
    (w : Fin (n + 1) → ℂ) (x : Fin n → ℤ) (l : ℤ) :
    -(Real.pi : ℂ) * finQuad n (blkD A) x +
        2 * Real.pi * finLinear n w x +
        (Real.pi : ℂ) / (finScalar n A : ℂ) *
          (w (Fin.last n) - finBilinear n A x - I * (l : ℂ)) ^ 2 =
      (Real.pi : ℂ) / (finScalar n A : ℂ) *
          (w (Fin.last n) - I * (l : ℂ)) ^ 2 +
        (-(Real.pi : ℂ) * finQuad n (finSchur n A) x +
          2 * Real.pi * ∑ i, finSchurSource n A w l i * (x i : ℂ)) := by
  rw [fin_schur_quad n A hA, fin_schur_source_linear]
  have ha := fin_scalar_pos n A hA
  have hcast : ((finScalar n A)⁻¹ : ℝ) = (finScalar n A : ℂ)⁻¹ := by
    simp
  rw [hcast]
  field_simp [ne_of_gt ha]
  ring

theorem fin_bottom_pos (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef) :
    (blkE A).PosDef := by
  have hH : (reA A).PosDef := reA_posdef hA
  have hh := hH.submatrix (e := Sum.inr) (by
    intro i j hij
    exact Sum.inr.inj hij)
  change ((reA A).submatrix Sum.inr Sum.inr).PosDef at hh
  change ((reA A).submatrix Sum.inr Sum.inr).PosDef
  exact hh

theorem fin_block_eq (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef) :
    reA A = Matrix.fromBlocks (blkD A) (blkB A)
      ((blkB A).conjTranspose) (blkE A) := by
  have hH : (reA A).PosDef := reA_posdef hA
  have hHerm : (reA A).IsHermitian := hH.isHermitian
  rw [reA_block] at hHerm
  have hb := (Matrix.isHermitian_fromBlocks_iff).1 hHerm
  have hBC : blkC A = (blkB A).conjTranspose := hb.2.1.symm
  rw [reA_block, hBC]

set_option linter.style.haveILetI false in
theorem fin_det_split (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef) :
    A.det = finScalar n A * (finSchur n A).det := by
  let E := blkE A
  let D := blkD A
  let B := blkB A
  let C := B.conjTranspose
  let S := finSchur n A
  have hEpos : E.PosDef := by simpa [E] using fin_bottom_pos n A hA
  letI : Invertible E := hEpos.isUnit.invertible
  have hblock : reA A = Matrix.fromBlocks D B C E := by
    simpa [E, D, B, C] using fin_block_eq n A hA
  have hSchur : D - B * E⁻¹ * C = S := by
    rfl
  have hEeq : E = Matrix.diagonal (fun _ : Fin 1 => finScalar n A) := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  have hEdet : E.det = finScalar n A := by
    rw [hEeq, Matrix.det_unique]
    simp [Matrix.diagonal]
  have hdet : (reA A).det = E.det * S.det := by
    rw [hblock, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv, hSchur]
  calc
    A.det = (reA A).det := (Matrix.det_reindex_self (eFin n).symm A).symm
    _ = E.det * S.det := hdet
    _ = finScalar n A * (finSchur n A).det := by rw [hEdet]

set_option linter.style.haveILetI false in
theorem fin_inv_block_formula (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef) :
    reA (A⁻¹) = Matrix.fromBlocks (finSchur n A)⁻¹
      (-((finSchur n A)⁻¹ * blkB A * (blkE A)⁻¹))
      (-((blkE A)⁻¹ * (blkB A).conjTranspose * (finSchur n A)⁻¹))
      ((blkE A)⁻¹ + (blkE A)⁻¹ * (blkB A).conjTranspose *
        (finSchur n A)⁻¹ * blkB A * (blkE A)⁻¹) := by
  let E := blkE A
  let D := blkD A
  let B := blkB A
  let C := B.conjTranspose
  let S := finSchur n A
  have hH : (reA A).PosDef := reA_posdef hA
  have hEpos : E.PosDef := by simpa [E] using fin_bottom_pos n A hA
  have hSpos : S.PosDef := by simpa [S] using fin_schur_pos n A hA
  letI : Invertible E := hEpos.isUnit.invertible
  letI : Invertible S := hSpos.isUnit.invertible
  letI : Invertible (reA A) := hH.isUnit.invertible
  have hblock : reA A = Matrix.fromBlocks D B C E := by
    simpa [E, D, B, C] using fin_block_eq n A hA
  letI : Invertible (Matrix.fromBlocks D B C E) :=
    Invertible.copy (inferInstance : Invertible (reA A)) _ hblock.symm
  have hSchur : D - B * ⅟E * C = S := by
    rw [Matrix.invOf_eq_nonsing_inv, ← finSchur]
  letI : Invertible (D - B * ⅟E * C) :=
    Invertible.copy (inferInstance : Invertible S) _ hSchur
  have hSchur' : D - B * E⁻¹ * C = S := by
    simpa [Matrix.invOf_eq_nonsing_inv] using hSchur
  have hReInv : reA (A⁻¹) = (reA A)⁻¹ := by
    exact (Matrix.inv_reindex (eFin n).symm (eFin n).symm A).symm
  calc
    reA (A⁻¹) = (reA A)⁻¹ := hReInv
    _ = (Matrix.fromBlocks D B C E)⁻¹ := by rw [hblock]
    _ = Matrix.fromBlocks S⁻¹ (-(S⁻¹ * B * E⁻¹))
          (-(E⁻¹ * C * S⁻¹)) (E⁻¹ + E⁻¹ * C * S⁻¹ * B * E⁻¹) := by
      rw [← Matrix.invOf_eq_nonsing_inv, Matrix.invOf_fromBlocks₂₂_eq]
      simp only [Matrix.invOf_eq_nonsing_inv]
      rw [hSchur']
    _ = _ := by simp [S, B, C, E]

def qform {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (x : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, x i * M i j * x j

theorem qform_dotProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (x : ι → ℂ) :
    qform M x = x ⬝ᵥ M *ᵥ x := by
  simp [qform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem dotProduct_transpose_mulVec {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (x z : ι → ℂ) :
    x ⬝ᵥ Mᵀ *ᵥ z = M *ᵥ x ⬝ᵥ z := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply]
  calc
    _ = ∑ i, ∑ j, x i * (M j i * z j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.mul_sum _ _ _
    _ = ∑ j, ∑ i, x i * (M j i * z j) := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        _ = ∑ i, (M j i * x i) * z j := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by rw [Finset.sum_mul]

theorem qform_congruence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P M : Matrix ι ι ℂ) (x : ι → ℂ) :
    qform (Pᵀ * M * P) x = qform M (P *ᵥ x) := by
  rw [qform_dotProduct, qform_dotProduct]
  calc
    _ = x ⬝ᵥ Pᵀ *ᵥ (M *ᵥ (P *ᵥ x)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = P *ᵥ x ⬝ᵥ (M *ᵥ (P *ᵥ x)) := dotProduct_transpose_mulVec P x _
    _ = _ := rfl

theorem qform_fromBlocks {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (x : m → ℂ) (y : n → ℂ) :
    qform (Matrix.fromBlocks A B C D) (Sum.elim x y) =
      qform A x + (∑ i, ∑ j, x i * B i j * y j) +
      (∑ i, ∑ j, y i * C i j * x j) + qform D y := by
  simp [qform, Matrix.fromBlocks, Fintype.sum_sum_type, Finset.sum_add_distrib,
    mul_assoc]
  ring

theorem block_inverse_factorization {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (S : Matrix m m ℂ) (X : Matrix m n ℂ) (Xt : Matrix n m ℂ)
    (E : Matrix n n ℂ) (htranspose : Xᵀ = Xt) :
    Matrix.fromBlocks S (-(S * X)) (-(Xt * S)) (E + Xt * S * X) =
      (Matrix.fromBlocks (1 : Matrix m m ℂ) (-X) 0 (1 : Matrix n n ℂ))ᵀ *
        (Matrix.fromBlocks S 0 0 E) *
        Matrix.fromBlocks (1 : Matrix m m ℂ) (-X) 0 (1 : Matrix n n ℂ) := by
  simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose, Matrix.transpose_one,
    Matrix.transpose_zero, Matrix.transpose_neg, htranspose, Matrix.zero_mul,
    Matrix.mul_zero, Matrix.mul_one, add_comm, Matrix.mul_assoc]

def toComplexMatrix {ι κ : Type*} (M : Matrix ι κ ℝ) : Matrix ι κ ℂ :=
  fun i j => (M i j : ℂ)

theorem toComplexMatrix_fromBlocks {m n : Type*}
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ) (D : Matrix n n ℝ) :
    toComplexMatrix (Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks (toComplexMatrix A) (toComplexMatrix B)
        (toComplexMatrix C) (toComplexMatrix D) := by
  ext i j
  cases i <;> cases j <;> rfl

theorem toComplexMatrix_mul {m n o : Type*} [Fintype n]
    (A : Matrix m n ℝ) (B : Matrix n o ℝ) :
    toComplexMatrix (A * B) = toComplexMatrix A * toComplexMatrix B := by
  ext i j
  simp [toComplexMatrix, Matrix.mul_apply]

theorem toComplexMatrix_transpose {m n : Type*} (A : Matrix m n ℝ) :
    toComplexMatrix Aᵀ = (toComplexMatrix A)ᵀ := by
  ext i j
  rfl

theorem toComplexMatrix_add {m n : Type*} (A B : Matrix m n ℝ) :
    toComplexMatrix (A + B) = toComplexMatrix A + toComplexMatrix B := by
  ext i j
  simp [toComplexMatrix]

theorem toComplexMatrix_neg {m n : Type*} (A : Matrix m n ℝ) :
    toComplexMatrix (-A) = -toComplexMatrix A := by
  ext i j
  simp [toComplexMatrix]

theorem toComplexMatrix_zero {m n : Type*} :
    toComplexMatrix (0 : Matrix m n ℝ) = 0 := by
  ext i j
  rfl

theorem toComplexMatrix_one {m : Type*} [DecidableEq m] :
    toComplexMatrix (1 : Matrix m m ℝ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [toComplexMatrix, Matrix.one_apply, h]

theorem fin_inverse_quadratic (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef)
    (x : Fin n → ℂ) (y : Fin 1 → ℂ) :
    qform (toComplexMatrix (reA (A⁻¹))) (Sum.elim x y) =
      qform (toComplexMatrix ((finSchur n A)⁻¹))
          (x - (toComplexMatrix (blkB A * (blkE A)⁻¹)) *ᵥ y) +
        qform (toComplexMatrix ((blkE A)⁻¹)) y := by
  let S := finSchur n A
  let B := blkB A
  let C := B.conjTranspose
  let E := blkE A
  let Sc := toComplexMatrix (S⁻¹)
  let Bc := toComplexMatrix B
  let Cc := toComplexMatrix C
  let Ec := toComplexMatrix (E⁻¹)
  let X := Bc * Ec
  let Xt := Ec * Cc
  let P : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ :=
    Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (-X)
      (0 : Matrix (Fin 1) (Fin n) ℂ) (1 : Matrix (Fin 1) (Fin 1) ℂ)
  let D0 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ :=
    Matrix.fromBlocks Sc 0 0 Ec
  have hInvC : toComplexMatrix (reA (A⁻¹)) =
      Matrix.fromBlocks Sc (-(Sc * Bc * Ec)) (-(Ec * Cc * Sc))
        (Ec + Ec * Cc * Sc * Bc * Ec) := by
    have hh := congrArg toComplexMatrix (fin_inv_block_formula n A hA)
    simpa [S, B, C, E, Sc, Bc, Cc, Ec, toComplexMatrix_fromBlocks,
      toComplexMatrix_mul, toComplexMatrix_add, toComplexMatrix_neg,
      toComplexMatrix_zero, toComplexMatrix_one] using hh
  have hEt : Ecᵀ = Ec := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  have hCt : Bcᵀ = Cc := by
    ext i j
    simp [Bc, Cc, B, C, toComplexMatrix]
  have hXt : Xᵀ = Xt := by
    change (Bc * Ec)ᵀ = Ec * Cc
    rw [Matrix.transpose_mul, hEt, hCt]
  have hfactor : toComplexMatrix (reA (A⁻¹)) = Pᵀ * D0 * P := by
    calc
      _ = Matrix.fromBlocks Sc (-(Sc * X)) (-(Xt * Sc)) (Ec + Xt * Sc * X) := by
        simpa [X, Xt, Matrix.mul_assoc] using hInvC
      _ = _ := by
        simpa [P, D0] using block_inverse_factorization Sc X Xt Ec hXt
  rw [hfactor, qform_congruence]
  have hvec : P *ᵥ Sum.elim x y = Sum.elim (x - X *ᵥ y) y := by
    have hh := Matrix.fromBlocks_mulVec
      (1 : Matrix (Fin n) (Fin n) ℂ) (-X) (0 : Matrix (Fin 1) (Fin n) ℂ)
      (1 : Matrix (Fin 1) (Fin 1) ℂ) (Sum.elim x y)
    simpa [P, Matrix.one_mulVec, Matrix.neg_mulVec, Matrix.zero_mulVec,
      sub_eq_add_neg] using hh
  rw [hvec]
  change qform (Matrix.fromBlocks Sc 0 0 Ec) (Sum.elim (x - X *ᵥ y) y) = _
  rw [qform_fromBlocks]
  simp only [Matrix.zero_apply, zero_mul, mul_zero]
  have hXc : X = toComplexMatrix (blkB A * (blkE A)⁻¹) := by
    dsimp [X, Bc, Ec]
    exact (toComplexMatrix_mul (blkB A) ((blkE A)⁻¹)).symm
  rw [← hXc]
  simp [Sc, Ec, S, E]

def finDualVector (n : ℕ) (w : Fin (n + 1) → ℂ)
    (x : Fin n → ℤ) (l : ℤ) : Fin (n + 1) → ℂ :=
  fun i => w i - I * (finVector n x l i : ℂ)

def finDualSumVector (n : ℕ) (w : Fin (n + 1) → ℂ)
    (x : Fin n → ℤ) (l : ℤ) : Fin n ⊕ Fin 1 → ℂ :=
  Sum.elim (fun i => w (Fin.castSucc i) - I * (x i : ℂ))
    (fun _ => w (Fin.last n) - I * (l : ℂ))

theorem fin_qform_reindex (n : ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (x : Fin n → ℤ) (l : ℤ) (w : Fin (n + 1) → ℂ) :
    qform (toComplexMatrix M) (finDualVector n w x l) =
      qform (toComplexMatrix (reA M)) (finDualSumVector n w x l) := by
  have hv (s : Fin n ⊕ Fin 1) :
      finDualVector n w x l (eFin n s) = finDualSumVector n w x l s := by
    cases s with
    | inl i =>
        simp [finDualVector, finDualSumVector, finVector, finSumPiEquiv,
          Equiv.piCongrLeft_apply, piSumEquiv, eFin]
        rfl
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [finDualVector, finDualSumVector, finVector, finSumPiEquiv,
        Equiv.piCongrLeft_apply, piSumEquiv, eFin]
      rfl
  unfold qform
  refine Fintype.sum_equiv (eFin n).symm _ _ ?_
  intro i
  refine Fintype.sum_equiv (eFin n).symm _ _ ?_
  intro j
  have hvi : finDualVector n w x l i = finDualSumVector n w x l ((eFin n).symm i) := by
    simpa [eFin] using hv ((eFin n).symm i)
  have hvj : finDualVector n w x l j = finDualSumVector n w x l ((eFin n).symm j) := by
    simpa [eFin] using hv ((eFin n).symm j)
  rw [hvi, hvj]
  simp [toComplexMatrix, reA, Matrix.reindex_apply]

theorem fin_X_mulVec_const (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef)
    (z : ℂ) (i : Fin n) :
    ((toComplexMatrix (blkB A * (blkE A)⁻¹)) *ᵥ (fun _ : Fin 1 => z)) i =
      (blkB A i 0 : ℂ) / (finScalar n A : ℂ) * z := by
  have ha := fin_scalar_pos n A hA
  have hE00 : toComplexMatrix ((blkE A)⁻¹) 0 0 =
      (finScalar n A : ℂ)⁻¹ := by
    change (((blkE A)⁻¹ 0 0 : ℝ) : ℂ) = _
    rw [fin_block_scalar_inv n A ha]
    simp
  rw [toComplexMatrix_mul]
  simp only [Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_one,
    dotProduct, Fin.sum_univ_one]
  rw [hE00]
  simp only [toComplexMatrix]
  field_simp [ne_of_gt ha]

theorem fin_bottom_qform (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef) (z : ℂ) :
    qform (toComplexMatrix ((blkE A)⁻¹)) (fun _ : Fin 1 => z) =
      (finScalar n A : ℂ)⁻¹ * z ^ 2 := by
  have ha := fin_scalar_pos n A hA
  simp only [qform, Fin.sum_univ_one, toComplexMatrix]
  rw [fin_block_scalar_inv n A ha]
  simp [finScalar, pow_two]
  ring

theorem fin_dual_quadratic_split (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef)
    (w : Fin (n + 1) → ℂ) (x : Fin n → ℤ) (l : ℤ) :
    (∑ i, ∑ j, (w i - I * (finVector n x l i : ℂ)) *
        ((A⁻¹ i j : ℝ) : ℂ) * (w j - I * (finVector n x l j : ℂ))) =
      (finScalar n A : ℂ)⁻¹ * (w (Fin.last n) - I * (l : ℂ)) ^ 2 +
        (∑ i, ∑ j, (finSchurSource n A w l i - I * (x i : ℂ)) *
          (((finSchur n A)⁻¹ i j : ℝ) : ℂ) *
            (finSchurSource n A w l j - I * (x j : ℂ))) := by
  let u : Fin n → ℂ := fun i => w (Fin.castSucc i) - I * (x i : ℂ)
  let y : Fin 1 → ℂ := fun _ => w (Fin.last n) - I * (l : ℂ)
  have hq0 := fin_qform_reindex n (A⁻¹) x l w
  have hq1 := fin_inverse_quadratic n A hA u y
  have hmv (i : Fin n) :
      ((toComplexMatrix (blkB A * (blkE A)⁻¹)) *ᵥ y) i =
        ((blkB A i 0 : ℂ) / (finScalar n A : ℂ)) *
          (w (Fin.last n) - I * (l : ℂ)) := by
    simpa [y] using fin_X_mulVec_const n A hA (w (Fin.last n) - I * (l : ℂ)) i
  have htop :
      (u - (toComplexMatrix (blkB A * (blkE A)⁻¹)) *ᵥ y) =
        (fun i => finSchurSource n A w l i - I * (x i : ℂ)) := by
    funext i
    simp only [Pi.sub_apply, u]
    rw [hmv i]
    simp [finSchurSource]
    ring
  have hvect : finDualSumVector n w x l = Sum.elim u y := by
    funext s
    cases s with
    | inl i => simp [finDualSumVector, u, y]
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [finDualSumVector, u, y]
  have hbottom := fin_bottom_qform n A hA (w (Fin.last n) - I * (l : ℂ))
  change qform (toComplexMatrix (A⁻¹)) (finDualVector n w x l) = _
  rw [hq0, hvect, hq1, htop, hbottom]
  simp [qform, toComplexMatrix]
  ring

def finLinearCoord {n : ℕ} (w : Fin n → ℂ) (x : Fin n → ℤ) : ℂ :=
  ∑ i, w i * (x i : ℂ)

def finSource0 (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (w : Fin (n + 1) → ℂ) : Fin n → ℂ := fun i =>
  w (Fin.castSucc i) - (blkB A i 0 : ℂ) *
    ((finScalar n A)⁻¹ : ℝ) * w (Fin.last n)

def finMixedExp (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (w : Fin (n + 1) → ℂ) (x : Fin n → ℤ) (l : ℤ) : ℂ :=
  -(Real.pi : ℂ) * finQuad n (blkD A) x +
    2 * Real.pi * finLinear n w x +
    (Real.pi : ℂ) / (finScalar n A : ℂ) *
      (w (Fin.last n) - finBilinear n A x - I * (l : ℂ)) ^ 2

theorem fin_scalar_square_expand (a : ℝ) (_ha : 0 < a) (v : ℂ) (l : ℤ) :
    (Real.pi : ℂ) / (a : ℂ) * (v - I * (l : ℂ)) ^ 2 =
      (Real.pi : ℂ) * (a⁻¹ : ℝ) * v ^ 2 +
        (-(Real.pi : ℂ) * (a⁻¹ : ℝ) * (l : ℂ) ^ 2 +
          2 * Real.pi * (-I * (a⁻¹ : ℝ) * v) * (l : ℂ)) := by
  have hI : I ^ 2 = (-1 : ℂ) := Complex.I_sq
  have hinv : (a : ℂ)⁻¹ = ((a⁻¹ : ℝ) : ℂ) := by simp
  rw [div_eq_mul_inv, hinv]
  ring_nf
  rw [hI]
  ring

theorem fin_schur_source_linear_decomp (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (w : Fin (n + 1) → ℂ)
    (x : Fin n → ℤ) (l : ℤ) :
    (∑ i, finSchurSource n A w l i * (x i : ℂ)) =
      finLinearCoord (finSource0 n A w) x +
        I * ((finScalar n A)⁻¹ : ℝ) * finBilinear n A x * (l : ℂ) := by
  rw [fin_schur_source_linear]
  simp [finSource0, finLinearCoord, finLinear, finBilinear,
    Finset.mul_sum, div_eq_mul_inv]
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem fin_mixed_exp_decompose (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef)
    (w : Fin (n + 1) → ℂ) (x : Fin n → ℤ) (l : ℤ) :
    finMixedExp n A w x l =
      (Real.pi : ℂ) * ((finScalar n A)⁻¹ : ℝ) * (w (Fin.last n)) ^ 2 +
        (-(Real.pi : ℂ) * finQuad n (finSchur n A) x +
          2 * Real.pi * finLinearCoord (finSource0 n A w) x) +
        (-(Real.pi : ℂ) * ((finScalar n A)⁻¹ : ℝ) * (l : ℂ) ^ 2 +
          2 * Real.pi * (-I * ((finScalar n A)⁻¹ : ℝ) * w (Fin.last n)) * (l : ℂ)) +
        (2 * Real.pi * I * ((finScalar n A)⁻¹ : ℝ) * finBilinear n A x * (l : ℂ)) := by
  unfold finMixedExp
  rw [fin_schur_complete_square n A hA]
  rw [fin_scalar_square_expand (finScalar n A) (fin_scalar_pos n A hA)
    (w (Fin.last n)) l]
  rw [fin_schur_source_linear_decomp]
  ring

theorem fin_mixed_exp_summable (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef)
    (w : Fin (n + 1) → ℂ) :
    Summable (fun p : (Fin n → ℤ) × ℤ => cexp (finMixedExp n A w p.1 p.2)) := by
  classical
  let a : ℝ := finScalar n A
  let v : ℂ := w (Fin.last n)
  let s : Matrix (Fin n) (Fin n) ℝ := finSchur n A
  let u : Fin n → ℂ := finSource0 n A w
  let f (x : Fin n → ℤ) : ℂ := cexp (-(Real.pi : ℂ) * finQuad n s x +
    2 * Real.pi * finLinearCoord u x)
  let g (l : ℤ) : ℂ := cexp (-(Real.pi : ℂ) * (a⁻¹ : ℝ) * (l : ℂ)^2 +
    2 * Real.pi * (-I * (a⁻¹ : ℝ) * v) * (l : ℂ))
  let c : ℂ := cexp ((Real.pi : ℂ) * (a⁻¹ : ℝ) * v^2)
  have ha : 0 < a := by dsimp [a]; exact fin_scalar_pos n A hA
  have hs : s.PosDef := by dsimp [s]; exact fin_schur_pos n A hA
  have hf : Summable f := by
    dsimp [f, s, u]
    exact summable_tilted_gaussian (finSchur n A) hs (finSource0 n A w)
  have hg : Summable g := by
    dsimp [g]
    exact summable_scalar_gaussian ((a⁻¹ : ℝ) : ℂ)
      (by simp [ha]) (-I * (a⁻¹ : ℝ) * v)
  have hprod : Summable (fun p : (Fin n → ℤ) × ℤ => f p.1 * g p.2) :=
    summable_prod_of_summable f g hf hg
  have hphase (x : Fin n → ℤ) (l : ℤ) :
      ‖cexp (2 * Real.pi * I * (a⁻¹ : ℝ) * finBilinear n A x * (l : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (2 * Real.pi * I * (a⁻¹ : ℝ) * finBilinear n A x * (l : ℂ)).re = 0 := by
      simp [finBilinear, Complex.mul_re, Complex.mul_im, mul_assoc,
        mul_left_comm, mul_comm]
    rw [hre]
    simp
  have hbound (p : (Fin n → ℤ) × ℤ) :
      ‖cexp (finMixedExp n A w p.1 p.2)‖ ≤ ‖c‖ * ‖f p.1 * g p.2‖ := by
    rw [fin_mixed_exp_decompose n A hA w p.1 p.2]
    dsimp [c, f, g, a, v, s, u]
    simp only [Complex.exp_add, Complex.norm_mul]
    rw [hphase]
    simp [Complex.norm_exp]
    apply le_of_eq
    ac_rfl
  exact Summable.of_norm_bounded (hprod.norm.mul_left ‖c‖) hbound

end

end FroehlichSpencer.FS82.Poisson
