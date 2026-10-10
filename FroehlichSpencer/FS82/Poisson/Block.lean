module
public import Mathlib.Data.Matrix.Block
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

namespace FroehlichSpencer.FS82.Poisson

open Matrix
variable {n : ℕ}
noncomputable section

def eFin (n : ℕ) : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv

def reA (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  Matrix.reindex (eFin n).symm (eFin n).symm A

def blkD (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => reA A (Sum.inl i) (Sum.inl j)

def blkB (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : Matrix (Fin n) (Fin 1) ℝ :=
  fun i j => reA A (Sum.inl i) (Sum.inr j)

def blkC (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : Matrix (Fin 1) (Fin n) ℝ :=
  fun i j => reA A (Sum.inr i) (Sum.inl j)

def blkE (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  fun i j => reA A (Sum.inr i) (Sum.inr j)

theorem reA_block (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    reA A = Matrix.fromBlocks (blkD A) (blkB A) (blkC A) (blkE A) := by
  ext i j
  cases i <;> cases j <;> rfl

theorem block_herm {A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ} (hA : A.PosDef) :
    (blkC A) = (blkB A).transpose := by
  have hh : (reA A).IsHermitian := by
    change (Matrix.reindex (eFin n).symm (eFin n).symm A).IsHermitian
    rw [Matrix.reindex_apply]
    exact hA.isHermitian.submatrix (eFin n)
  rw [reA_block] at hh
  have hblocks := (Matrix.isHermitian_fromBlocks_iff).1 hh
  have hBC : (blkB A).conjTranspose = blkC A := hblocks.2.1
  ext i j
  have hij := congrArg (fun M : Matrix (Fin 1) (Fin n) ℝ => M i j) hBC
  simpa [Matrix.conjTranspose_apply, Matrix.transpose_apply] using hij.symm

theorem reA_posdef {A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ} (hA : A.PosDef) : (reA A).PosDef := by
  change (Matrix.reindex (eFin n).symm (eFin n).symm A).PosDef
  rw [Matrix.reindex_apply]
  exact hA.submatrix (e := eFin n) (eFin n).injective
set_option linter.style.haveILetI false in
theorem schur_block_posdef {A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ} (hA : A.PosDef) :
    let S := blkD A - blkB A * (blkE A)⁻¹ * (blkB A).conjTranspose
    S.PosDef := by
  let H := reA A
  let D := blkD A
  let B := blkB A
  let E := blkE A
  have hH : H.PosDef := by simpa [H] using reA_posdef hA
  have hE : E.PosDef := by
    have hh := hH.submatrix (e := Sum.inr) (by intro i j h; exact Sum.inr.inj h)
    change (H.submatrix Sum.inr Sum.inr).PosDef at hh
    change E.PosDef
    exact hh
  haveI : Invertible E := hE.isUnit.invertible
  have hBC : blkC A = B.conjTranspose := by
    have hhh : (H).IsHermitian := hH.isHermitian
    change (reA A).IsHermitian at hhh
    rw [reA_block] at hhh
    have hb := (Matrix.isHermitian_fromBlocks_iff).1 hhh
    simpa [B] using hb.2.1.symm
  have hblock : H = Matrix.fromBlocks D B (B.conjTranspose) E := by
    change reA A = Matrix.fromBlocks D B (B.conjTranspose) E
    rw [reA_block]
    simp only [D, B, E]
    rw [hBC]
  let S : Matrix (Fin n) (Fin n) ℝ := D - B * E⁻¹ * B.conjTranspose
  have hSpsd : S.PosSemidef := by
    have hpsd : (Matrix.fromBlocks D B (B.conjTranspose) E).PosSemidef := by
      rw [← hblock]
      exact hH.posSemidef
    have hp := Matrix.PosDef.fromBlocks₂₂ D B hE
    simpa [S] using hp.mp hpsd
  have hunitH : IsUnit (Matrix.fromBlocks D B (B.conjTranspose) E) := by
    rw [← hblock]
    exact hH.isUnit
  have hSunit : IsUnit S := by
    have hu := (Matrix.isUnit_fromBlocks_iff_of_invertible₂₂ (A := D) (B := B)
      (C := B.conjTranspose) (D := E)).mp hunitH
    simpa [S] using hu
  exact (hSpsd.posDef_iff_isUnit).2 hSunit

end

end FroehlichSpencer.FS82.Poisson
