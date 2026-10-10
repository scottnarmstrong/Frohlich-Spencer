/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Resolvent.Complex
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Decoupled finite-volume resolvents

This generic block decomposition is motivated by Fröhlich–Spencer (1983),
equations (2.10)–(2.13), pp. 159–160. No lattice or model-specific operator
is introduced here.
-/

public section

namespace FroehlichSpencer
namespace Matrix

/-- Remove the matrix entries that connect a set to its complement. -/
@[expose] def decouple {ι : Type*} (B : Set ι) [DecidablePred (· ∈ B)]
    (H : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => if i ∈ B then (if j ∈ B then H i j else 0) else
    (if j ∈ B then 0 else H i j)

@[simp]
theorem decouple_apply {ι : Type*} (B : Set ι) [DecidablePred (· ∈ B)]
    (H : Matrix ι ι ℂ) (i j : ι) :
    decouple B H i j = if i ∈ B then (if j ∈ B then H i j else 0) else
      (if j ∈ B then 0 else H i j) := by
  rfl

/-- The entries removed by `decouple`; this convention follows the requested `H - decouple` sign. -/
@[expose] def coupling {ι : Type*} (B : Set ι) [DecidablePred (· ∈ B)]
    (H : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  H - decouple B H

@[simp]
theorem coupling_apply {ι : Type*} (B : Set ι) [DecidablePred (· ∈ B)]
    (H : Matrix ι ι ℂ) (i j : ι) :
    coupling B H i j = H i j - decouple B H i j := by
  rfl

/-- Reindexing by `B ⊕ Bᶜ` displays `decouple` as the direct sum of principal submatrices. -/
theorem decouple_eq_reindex_fromBlocks {ι : Type*} (B : Set ι) [DecidablePred (· ∈ B)]
    (H : Matrix ι ι ℂ) :
    decouple B H =
      Matrix.reindex (Equiv.Set.sumCompl B) (Equiv.Set.sumCompl B)
        (Matrix.fromBlocks (H.submatrix (↑) (↑)) 0 0
          (H.submatrix (↑) (↑) : Matrix (Bᶜ : Set ι) (Bᶜ : Set ι) ℂ)) := by
  ext i j
  by_cases hi : i ∈ B <;> by_cases hj : j ∈ B
  · simp [decouple, Matrix.reindex_apply, hi, hj,
      Equiv.Set.sumCompl_symm_apply_of_mem hi,
      Equiv.Set.sumCompl_symm_apply_of_mem hj]
  · simp [decouple, Matrix.reindex_apply, hi, hj,
      Equiv.Set.sumCompl_symm_apply_of_mem hi,
      Equiv.Set.sumCompl_symm_apply_of_notMem hj]
  · simp [decouple, Matrix.reindex_apply, hi, hj,
      Equiv.Set.sumCompl_symm_apply_of_notMem hi,
      Equiv.Set.sumCompl_symm_apply_of_mem hj]
  · simp [decouple, Matrix.reindex_apply, hi, hj,
      Equiv.Set.sumCompl_symm_apply_of_notMem hi,
      Equiv.Set.sumCompl_symm_apply_of_notMem hj]

/-- Decoupling preserves Hermitian symmetry. -/
theorem decouple_isHermitian {ι : Type*} (B : Set ι) [DecidablePred (· ∈ B)]
    {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) : (decouple B H).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hi : i ∈ B <;> by_cases hj : j ∈ B <;>
    simp [decouple_apply, hi, hj, hH.apply]

/-- The shifted decoupled matrix is a direct sum after reindexing its two blocks. -/
theorem sub_zsmul_one_decouple_eq_reindex_fromBlocks {ι : Type*} [Fintype ι]
    [DecidableEq ι] (B : Set ι) [DecidablePred (· ∈ B)] (H : Matrix ι ι ℂ) (z : ℂ) :
    decouple B H - z • (1 : Matrix ι ι ℂ) =
      Matrix.reindex (Equiv.Set.sumCompl B) (Equiv.Set.sumCompl B)
        (Matrix.fromBlocks
          (H.submatrix (↑) (↑) - z • (1 : Matrix B B ℂ)) 0 0
          (H.submatrix (↑) (↑) - z •
            (1 : Matrix (Bᶜ : Set ι) (Bᶜ : Set ι) ℂ))) := by
  classical
  let e := Equiv.Set.sumCompl B
  let A : Matrix B B ℂ := H.submatrix Subtype.val Subtype.val
  let C : Matrix (Bᶜ : Set ι) (Bᶜ : Set ι) ℂ :=
    H.submatrix Subtype.val Subtype.val
  let M := Matrix.fromBlocks A 0 0 C
  let M' := Matrix.fromBlocks
    (A - z • (1 : Matrix B B ℂ)) 0 0
    (C - z • (1 : Matrix (Bᶜ : Set ι) (Bᶜ : Set ι) ℂ))
  have hblocks : M - z • (1 : Matrix (B ⊕ (Bᶜ : Set ι)) (B ⊕ (Bᶜ : Set ι)) ℂ) = M' := by
    ext i j
    cases i <;> cases j <;>
      simp [M, M', Matrix.one_apply]
  have hshift : Matrix.reindex e e (M - z •
      (1 : Matrix (B ⊕ (Bᶜ : Set ι)) (B ⊕ (Bᶜ : Set ι)) ℂ)) =
      Matrix.reindex e e M - z • (1 : Matrix ι ι ℂ) := by
    let ρ := Matrix.reindexAlgEquiv ℂ ℂ e
    change ρ (M - z • (1 : Matrix (B ⊕ (Bᶜ : Set ι)) (B ⊕ (Bᶜ : Set ι)) ℂ)) =
      ρ M - z • (1 : Matrix ι ι ℂ)
    have hscalar : ρ (z •
        (1 : Matrix (B ⊕ (Bᶜ : Set ι)) (B ⊕ (Bᶜ : Set ι)) ℂ)) =
        z • (1 : Matrix ι ι ℂ) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using ρ.commutes z
    rw [map_sub, hscalar]
  calc
    decouple B H - z • (1 : Matrix ι ι ℂ) = Matrix.reindex e e M - z • 1 := by
      rw [decouple_eq_reindex_fromBlocks]
    _ = Matrix.reindex e e (M - z •
        (1 : Matrix (B ⊕ (Bᶜ : Set ι)) (B ⊕ (Bᶜ : Set ι)) ℂ)) := hshift.symm
    _ = Matrix.reindex e e M' := by rw [hblocks]

/-- The resolvent of a decoupled Hermitian matrix is the direct sum of its two principal
resolvents. -/
theorem decoupled_resolvent_eq_reindex_fromBlocks {ι : Type*} [Fintype ι]
    [DecidableEq ι] (B : Set ι) [DecidablePred (· ∈ B)] (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    (decouple B H - z • (1 : Matrix ι ι ℂ))⁻¹ =
      Matrix.reindex (Equiv.Set.sumCompl B) (Equiv.Set.sumCompl B)
        (Matrix.fromBlocks
          ((H.submatrix (↑) (↑) - z • (1 : Matrix B B ℂ))⁻¹) 0 0
          ((H.submatrix (↑) (↑) - z •
            (1 : Matrix (Bᶜ : Set ι) (Bᶜ : Set ι) ℂ))⁻¹)) := by
  classical
  let A : Matrix B B ℂ := H.submatrix Subtype.val Subtype.val
  let C : Matrix (Bᶜ : Set ι) (Bᶜ : Set ι) ℂ :=
    H.submatrix Subtype.val Subtype.val
  let A₀ : Matrix B B ℂ := A - z • 1
  let C₀ : Matrix (Bᶜ : Set ι) (Bᶜ : Set ι) ℂ := C - z • 1
  let M := Matrix.fromBlocks A₀ 0 0 C₀
  let e := Equiv.Set.sumCompl B
  have hHA : A.IsHermitian := hH.submatrix Subtype.val
  have hHC : C.IsHermitian := hH.submatrix Subtype.val
  have huA : IsUnit A₀ :=
    FroehlichSpencer.Matrix.IsHermitian.isUnit_sub_zsmul_one_of_im_ne_zero A hHA z hz
  have huC : IsUnit C₀ :=
    FroehlichSpencer.Matrix.IsHermitian.isUnit_sub_zsmul_one_of_im_ne_zero C hHC z hz
  have hA₀Inv : Invertible A₀ := Classical.choice huA.nonempty_invertible
  have hC₀Inv : Invertible C₀ := Classical.choice huC.nonempty_invertible
  have hMInv : Invertible M := Matrix.fromBlocksZero₂₁Invertible A₀ 0 C₀
  have hdec : decouple B H - z • (1 : Matrix ι ι ℂ) = Matrix.reindex e e M := by
    simpa [e, M, A₀, C₀, A, C] using
      sub_zsmul_one_decouple_eq_reindex_fromBlocks B H z
  have hM : M⁻¹ = Matrix.fromBlocks (A₀⁻¹) 0 0 (C₀⁻¹) := by
    calc
      M⁻¹ = ⅟M := (Matrix.invOf_eq_nonsing_inv M).symm
      _ = Matrix.fromBlocks (⅟A₀) (-(⅟A₀ * 0 * ⅟C₀)) 0 (⅟C₀) :=
        Matrix.invOf_fromBlocks_zero₂₁_eq A₀ 0 C₀
      _ = Matrix.fromBlocks (A₀⁻¹) 0 0 (C₀⁻¹) := by simp
  calc
    (decouple B H - z • (1 : Matrix ι ι ℂ))⁻¹ = (Matrix.reindex e e M)⁻¹ := by
      rw [hdec]
    _ = Matrix.reindex e e (M⁻¹) := by rw [Matrix.inv_reindex]
    _ = Matrix.reindex e e (Matrix.fromBlocks (A₀⁻¹) 0 0 (C₀⁻¹)) := by rw [hM]

/-- Entries of the decoupled resolvent vanish between the two blocks. -/
theorem decoupled_resolvent_apply_eq_zero_of_mem_iff {ι : Type*} [Fintype ι]
    [DecidableEq ι] (B : Set ι) [DecidablePred (· ∈ B)] (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (i j : ι)
    (hside : (i ∈ B) ≠ (j ∈ B)) :
    ((decouple B H - z • (1 : Matrix ι ι ℂ))⁻¹) i j = 0 := by
  rw [decoupled_resolvent_eq_reindex_fromBlocks B H hH z hz]
  by_cases hi : i ∈ B <;> by_cases hj : j ∈ B
  · exact False.elim (hside (propext ⟨fun _ => hj, fun _ => hi⟩))
  · simp [Matrix.reindex_apply, Equiv.Set.sumCompl_symm_apply_of_mem hi,
      Equiv.Set.sumCompl_symm_apply_of_notMem hj]
  · simp [Matrix.reindex_apply, Equiv.Set.sumCompl_symm_apply_of_notMem hi,
      Equiv.Set.sumCompl_symm_apply_of_mem hj]
  · have heq : (i ∈ B) = (j ∈ B) :=
      propext ⟨fun hip => (hi hip).elim, fun hjp => (hj hjp).elim⟩
    exact False.elim (hside heq)

/-- Within `B`, the decoupled resolvent is the resolvent of the principal submatrix. -/
theorem decoupled_resolvent_apply_eq_submatrix_of_mem {ι : Type*} [Fintype ι]
    [DecidableEq ι] (B : Set ι) [DecidablePred (· ∈ B)] (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) {i j : ι}
    (hi : i ∈ B) (hj : j ∈ B) :
    ((decouple B H - z • (1 : Matrix ι ι ℂ))⁻¹) i j =
      (((H.submatrix (Subtype.val : B → ι) (Subtype.val : B → ι) : Matrix B B ℂ) -
        z • (1 : Matrix B B ℂ))⁻¹) ⟨i, hi⟩ ⟨j, hj⟩ := by
  rw [decoupled_resolvent_eq_reindex_fromBlocks B H hH z hz]
  simp [Matrix.reindex_apply, Equiv.Set.sumCompl_symm_apply_of_mem hi,
    Equiv.Set.sumCompl_symm_apply_of_mem hj]

/-- On the complement of `B`, the decoupled resolvent is the resolvent of the complementary
principal submatrix. -/
theorem decoupled_resolvent_apply_eq_submatrix_of_not_mem {ι : Type*} [Fintype ι]
    [DecidableEq ι] (B : Set ι) [DecidablePred (· ∈ B)] (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) {i j : ι}
    (hi : i ∉ B) (hj : j ∉ B) :
    ((decouple B H - z • (1 : Matrix ι ι ℂ))⁻¹) i j =
      (((H.submatrix (Subtype.val : (Bᶜ : Set ι) → ι)
        (Subtype.val : (Bᶜ : Set ι) → ι) : Matrix (Bᶜ : Set ι) (Bᶜ : Set ι) ℂ) - z •
        (1 : Matrix (Bᶜ : Set ι) (Bᶜ : Set ι) ℂ))⁻¹) ⟨i, hi⟩ ⟨j, hj⟩ := by
  rw [decoupled_resolvent_eq_reindex_fromBlocks B H hH z hz]
  simp [Matrix.reindex_apply, Equiv.Set.sumCompl_symm_apply_of_notMem hi,
    Equiv.Set.sumCompl_symm_apply_of_notMem hj]

private theorem mul_mul_apply_eq_sum_pair {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A B C : Matrix ι ι ℂ) (i j : ι) :
    (A * B * C) i j =
      ∑ p ∈ (Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset ι),
        A i p.1 * B p.1 p.2 * C p.2 j := by
  calc
    (A * B * C) i j = (A * (B * C)) i j := by rw [mul_assoc]
    _ = ∑ p ∈ (Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset ι),
        A i p.1 * B p.1 p.2 * C p.2 j := by
      simp only [Matrix.mul_apply, Finset.mul_sum]
      rw [← Finset.sum_product']
      simp [mul_assoc]

private theorem coupling_apply_eq_if_cross {ι : Type*} (B : Set ι)
    [DecidablePred (· ∈ B)] (H : Matrix ι ι ℂ) (i j : ι) :
    coupling B H i j = if (i ∈ B) ≠ (j ∈ B) then H i j else 0 := by
  by_cases hi : i ∈ B <;> by_cases hj : j ∈ B <;>
    simp [coupling_apply, decouple_apply, hi, hj]

private theorem coupling_product_apply_eq_sum_filtered {ι : Type*} [Fintype ι]
    [DecidableEq ι] (B : Set ι) [DecidablePred (· ∈ B)] (H R R₀ : Matrix ι ι ℂ)
    (i j : ι) :
    (R₀ * coupling B H * R) i j =
      ∑ p ∈ ((Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset ι)).filter
          (fun p => ((p.1 ∈ B) ≠ (p.2 ∈ B)) ∧ H p.1 p.2 ≠ 0),
        R₀ i p.1 * H p.1 p.2 * R p.2 j := by
  classical
  rw [mul_mul_apply_eq_sum_pair]
  let s : Finset (ι × ι) := (Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset ι)
  let cross : (ι × ι) → Prop := fun p => (p.1 ∈ B) ≠ (p.2 ∈ B)
  let term : (ι × ι) → ℂ := fun p => R₀ i p.1 * H p.1 p.2 * R p.2 j
  change (∑ p ∈ s, R₀ i p.1 * coupling B H p.1 p.2 * R p.2 j) =
    ∑ p ∈ s.filter (fun p => cross p ∧ H p.1 p.2 ≠ 0), term p
  calc
    (∑ p ∈ s, R₀ i p.1 * coupling B H p.1 p.2 * R p.2 j) =
        ∑ p ∈ s, if cross p ∧ H p.1 p.2 ≠ 0 then term p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [coupling_apply_eq_if_cross]
      by_cases hp1 : p.1 ∈ B <;> by_cases hp2 : p.2 ∈ B
      all_goals
        by_cases hHne : H p.1 p.2 ≠ 0
        · simp [term, cross, hp1, hp2, hHne, mul_assoc]
        · have hHzero : H p.1 p.2 = 0 := by
            by_contra hHne'
            exact hHne hHne'
          simp [term, cross, hp1, hp2, hHzero]
    _ = ∑ p ∈ s.filter (fun p => cross p ∧ H p.1 p.2 ≠ 0), term p := by
      symm
      exact Finset.sum_filter (fun p => cross p ∧ H p.1 p.2 ≠ 0) term

/-- Entrywise first resolvent identity for `coupling = H - decouple`. The minus sign is forced by
the stated coupling convention: `H = decouple + coupling`. -/
theorem resolvent_apply_eq_decoupled_sub_coupling_sum {ι : Type*} [Fintype ι]
    [DecidableEq ι] (B : Set ι) [DecidablePred (· ∈ B)] (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (i j : ι) :
    ((H - z • (1 : Matrix ι ι ℂ))⁻¹) i j =
      ((decouple B H - z • (1 : Matrix ι ι ℂ))⁻¹) i j -
        ∑ p ∈ ((Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset ι)).filter
            (fun p => ((p.1 ∈ B) ≠ (p.2 ∈ B)) ∧ H p.1 p.2 ≠ 0),
          ((decouple B H - z • (1 : Matrix ι ι ℂ))⁻¹) i p.1 *
            H p.1 p.2 * ((H - z • (1 : Matrix ι ι ℂ))⁻¹) p.2 j := by
  classical
  let A := H - z • (1 : Matrix ι ι ℂ)
  let A₀ := decouple B H - z • (1 : Matrix ι ι ℂ)
  have hA : IsUnit A := by
    exact Matrix.IsHermitian.isUnit_sub_zsmul_one_of_im_ne_zero H hH z hz
  have hD : (decouple B H).IsHermitian := decouple_isHermitian B hH
  have hA₀ : IsUnit A₀ := by
    exact Matrix.IsHermitian.isUnit_sub_zsmul_one_of_im_ne_zero (decouple B H) hD z hz
  have hdiff : A - A₀ = coupling B H := by
    ext k k'
    simp [A, A₀, coupling, sub_eq_add_neg]
  have hid := FroehlichSpencer.ringInverse_resolvent_identity A A₀ hA hA₀
  have hid' : A⁻¹ = A₀⁻¹ - A₀⁻¹ * coupling B H * A⁻¹ := by
    simpa [Matrix.nonsing_inv_eq_ringInverse, hdiff] using hid
  calc
    ((H - z • (1 : Matrix ι ι ℂ))⁻¹) i j =
        (A₀⁻¹ - A₀⁻¹ * coupling B H * A⁻¹) i j := by
      simpa [A, A₀] using congrArg (fun M : Matrix ι ι ℂ => M i j) hid'
    _ = A₀⁻¹ i j -
        ∑ p ∈ ((Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset ι)).filter
            (fun p => ((p.1 ∈ B) ≠ (p.2 ∈ B)) ∧ H p.1 p.2 ≠ 0),
          A₀⁻¹ i p.1 * H p.1 p.2 * A⁻¹ p.2 j := by
      rw [Matrix.sub_apply, coupling_product_apply_eq_sum_filtered]
    _ = _ := by rfl

/-- The same identity for a starting point in `B`, with the first decoupled resolvent factor
written as the resolvent of the principal submatrix. Terms whose first pair index lies outside
`B` vanish by block diagonality. -/
theorem resolvent_apply_eq_submatrix_sub_coupling_sum_of_mem {ι : Type*} [Fintype ι]
    [DecidableEq ι] (B : Set ι) [DecidablePred (· ∈ B)] (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) {i j : ι} (hi : i ∈ B) :
    ((H - z • (1 : Matrix ι ι ℂ))⁻¹) i j =
      ((decouple B H - z • (1 : Matrix ι ι ℂ))⁻¹) i j -
        ∑ p ∈ ((Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset ι)).filter
            (fun p => ((p.1 ∈ B) ≠ (p.2 ∈ B)) ∧ H p.1 p.2 ≠ 0),
          (if hp : p.1 ∈ B then
            (((H.submatrix (Subtype.val : B → ι) (Subtype.val : B → ι) :
              Matrix B B ℂ) - z • (1 : Matrix B B ℂ))⁻¹) ⟨i, hi⟩ ⟨p.1, hp⟩ else 0) *
            H p.1 p.2 * ((H - z • (1 : Matrix ι ι ℂ))⁻¹) p.2 j := by
  classical
  have hbase := resolvent_apply_eq_decoupled_sub_coupling_sum B H hH z hz i j
  have hentry : ∀ p : ι × ι,
      ((decouple B H - z • (1 : Matrix ι ι ℂ))⁻¹) i p.1 =
        (if hp : p.1 ∈ B then
          (((H.submatrix (Subtype.val : B → ι) (Subtype.val : B → ι) :
            Matrix B B ℂ) - z • (1 : Matrix B B ℂ))⁻¹) ⟨i, hi⟩ ⟨p.1, hp⟩ else 0) := by
    intro p
    by_cases hpB : p.1 ∈ B
    · rw [dite_eq_left hpB]
      exact decoupled_resolvent_apply_eq_submatrix_of_mem B H hH z hz hi hpB
    · have hzero : ((decouple B H - z • (1 : Matrix ι ι ℂ))⁻¹) i p.1 = 0 :=
        decoupled_resolvent_apply_eq_zero_of_mem_iff B H hH z hz i p.1 (by
          intro heq
          exact hpB (heq ▸ hi))
      simpa [hpB] using hzero
  rw [hbase]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [hentry p]

end Matrix
end FroehlichSpencer
