module

public import Mathlib.Basic.Complex.Basic
public import FroehlichSpencer.FS82.Poisson.Block
public import FroehlichSpencer.FS82.Poisson.PiSplit
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace FroehlichSpencer.FS82.Poisson

open Complex Matrix

private theorem block_bilinear_form {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (x : m → ℂ) (y : n → ℂ) :
    (∑ s, ∑ t, Sum.elim x y s * (Matrix.fromBlocks A B C D s t) * Sum.elim x y t) =
      (∑ i, ∑ j, x i * A i j * x j) + (∑ i, ∑ j, x i * B i j * y j) +
      (∑ i, ∑ j, y i * C i j * x j) + (∑ i, ∑ j, y i * D i j * y j) := by
  simp [Matrix.fromBlocks, Fintype.sum_sum_type, Finset.sum_add_distrib, mul_assoc]
  ring

theorem reindexed_quad_split {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef)
    (x : Fin n → ℤ) (k : ℤ) :
    (∑ s, ∑ t, ((piSumEquiv n).symm (x, k) s : ℂ) *
      ((reA A s t : ℝ) : ℂ) * ((piSumEquiv n).symm (x, k) t : ℂ)) =
      (∑ i, ∑ j, (x i : ℂ) * (blkD A i j : ℂ) * (x j : ℂ)) +
        2 * (k : ℂ) * ∑ i, (blkB A i 0 : ℂ) * (x i : ℂ) +
        (blkE A 0 0 : ℂ) * (k : ℂ) ^ 2 := by
  have hBC : blkC A = (blkB A).conjTranspose := by
    have hH : (reA A).PosDef := reA_posdef hA
    have hhh : (reA A).IsHermitian := hH.isHermitian
    rw [reA_block] at hhh
    have hb := (Matrix.isHermitian_fromBlocks_iff).1 hhh
    ext i j
    have hij := congrArg (fun M : Matrix (Fin 1) (Fin n) ℝ => M i j) hb.2.1
    simpa [Matrix.conjTranspose_apply] using hij.symm
  have hblock : reA A = Matrix.fromBlocks (blkD A) (blkB A)
      ((blkB A).conjTranspose) (blkE A) := by
    rw [reA_block]
    rw [hBC]
  rw [hblock]
  have hcoef (i : Fin n) :
      ∑ j : Fin 1, (blkB A i j : ℂ) * ((piSumEquiv n).symm (x, k) (Sum.inr j) : ℂ) =
        (blkB A i 0 : ℂ) * (k : ℂ) := by
    simp [piSumEquiv]
  simp [piSumEquiv, Finset.mul_sum, mul_assoc]
  simp_rw [Finset.sum_add_distrib]
  have hcross :
      (∑ i, (x i : ℂ) * ((blkB A i 0 : ℂ) * (k : ℂ))) =
        ∑ i, (k : ℂ) * (blkB A i 0 : ℂ) * (x i : ℂ) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hcross]
  have hsame :
      (∑ i, (k : ℂ) * (blkB A i 0 : ℂ) * (x i : ℂ)) =
        ∑ i, (k : ℂ) * ((blkB A i 0 : ℂ) * (x i : ℂ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hterms :
      (∑ i, (k : ℂ) * (blkB A i 0 : ℂ) * (x i : ℂ)) +
        (∑ i, (k : ℂ) * ((blkB A i 0 : ℂ) * (x i : ℂ))) =
      ∑ i, 2 * ((k : ℂ) * ((blkB A i 0 : ℂ) * (x i : ℂ))) := by
    rw [hsame]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hscalar : (k : ℂ) * ((blkE A 0 0 : ℂ) * (k : ℂ)) =
      (blkE A 0 0 : ℂ) * (k : ℂ) ^ 2 := by ring
  linear_combination hterms + hscalar

end FroehlichSpencer.FS82.Poisson
