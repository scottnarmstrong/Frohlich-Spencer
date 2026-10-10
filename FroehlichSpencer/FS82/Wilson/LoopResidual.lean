/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.LoopShift
public import FroehlichSpencer.FS82.Wilson.LatticeCurl

/-!
# The loop residual `σ - dα` on lattice cells

The Wilson sheet `σ` and the explicit shift `α` of `LoopShift` as lattice-oriented functions on
the cells of `ℤ⁴` (C1 coordinates), and the residual `σ - dα` computed with the lattice
coboundary. The sum of its squares over any finite set of cells whose base points lie in a box
`B⁴` is at most `loopEnergy L T B`, hence at most `6 (L + T)`.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open Finset

/-- The explicit shift `α^{L,T}` as a lattice-oriented function on lattice cells: nonzero only
on links along the axes 2 and 3. -/
@[expose] noncomputable def loopShiftCell (L T : ℕ) : LatticeCell 4 → ℝ :=
  linkField23 (loopShiftTwo L T) (loopShiftThree L T)

/-- The Wilson sheet `σ` as a lattice-oriented function on lattice cells: one on the `2–3`
plaquettes based at `(y₀, y₁, 0, 0)`, `1 ≤ y₀ ≤ L`, `1 ≤ y₁ ≤ T`. -/
@[expose] noncomputable def sheetCell (L T : ℕ) : LatticeCell 4 → ℝ :=
  plaquetteField23 (sheetCoeff L T)

/-- The residual `σ - dα` on lattice cells. -/
@[expose] noncomputable def loopResidualCell (L T : ℕ) (p : LatticeCell 4) : ℝ :=
  sheetCell L T p - latticeCurl (loopShiftCell L T) p

/-- Summed over the sixteen axis patterns at one base point, the squares of the residual give
the energy density of `LoopShift`. -/
theorem sum_pattern_loopResidualCell_sq (L T : ℕ) (y₀ y₁ y₂ y₃ : ℤ) :
    ∑ a : Bool × Bool × Bool × Bool,
        loopResidualCell L T (latticeCellOf a (y₀, y₁, y₂, y₃)) ^ 2 =
      loopEnergyDensity L T y₀ y₁ y₂ y₃ := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, loopResidualCell, sheetCell, loopShiftCell,
    latticeCurl_linkField23, plaquetteField23_latticeCellOf]
  simp [curlPattern23, loopEnergyDensity, loopEps23, loopEps02, loopEps03, loopEps12, loopEps13]
  ring

/-- The squared residual over any finite set of cells with base points in `B⁴` is bounded by
the box energy. -/
theorem sum_loopResidualCell_sq_le_loopEnergy (L T : ℕ) (B : Finset ℤ)
    (S : Finset (LatticeCell 4)) (hS : ∀ p ∈ S, ∀ i, latticeCoordBase (p i) ∈ B) :
    ∑ p ∈ S, loopResidualCell L T p ^ 2 ≤ loopEnergy L T B := by
  classical
  let φ : (Bool × Bool × Bool × Bool) × (ℤ × ℤ × ℤ × ℤ) → LatticeCell 4 :=
    fun x => latticeCellOf x.1 x.2
  have hsub : S ⊆
      ((univ : Finset (Bool × Bool × Bool × Bool)) ×ˢ (B ×ˢ B ×ˢ B ×ˢ B)).image φ := by
    intro p hp
    refine mem_image.mpr ⟨(((p 0).isRight, (p 1).isRight, (p 2).isRight, (p 3).isRight),
      (latticeCoordBase (p 0), latticeCoordBase (p 1), latticeCoordBase (p 2),
        latticeCoordBase (p 3))), ?_, latticeCellOf_pattern_base p⟩
    simp only [mem_product, mem_univ, true_and]
    exact ⟨hS p hp 0, hS p hp 1, hS p hp 2, hS p hp 3⟩
  calc ∑ p ∈ S, loopResidualCell L T p ^ 2
      ≤ ∑ p ∈ ((univ : Finset (Bool × Bool × Bool × Bool)) ×ˢ (B ×ˢ B ×ˢ B ×ˢ B)).image φ,
          loopResidualCell L T p ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    _ ≤ ∑ x ∈ (univ : Finset (Bool × Bool × Bool × Bool)) ×ˢ (B ×ˢ B ×ˢ B ×ˢ B),
          loopResidualCell L T (φ x) ^ 2 :=
        sum_image_le_of_nonneg fun _ _ => sq_nonneg _
    _ = loopEnergy L T B := by
        rw [sum_product, sum_comm]
        simp only [sum_product, φ]
        unfold loopEnergy
        refine sum_congr rfl fun y₀ _ => sum_congr rfl fun y₁ _ => sum_congr rfl fun y₂ _ =>
          sum_congr rfl fun y₃ _ => ?_
        exact sum_pattern_loopResidualCell_sq L T y₀ y₁ y₂ y₃

/-- **Perimeter bound on lattice cells**: `Σ (σ - dα)(p)² ≤ 6 (L + T)` over every finite set of
cells. -/
theorem sum_loopResidualCell_sq_le (L T : ℕ) (S : Finset (LatticeCell 4)) :
    ∑ p ∈ S, loopResidualCell L T p ^ 2 ≤ 6 * ((L : ℝ) + T) := by
  classical
  let B : Finset ℤ := (S.biUnion fun p => (univ : Finset (Fin 4)).image fun i =>
    latticeCoordBase (p i))
  refine (sum_loopResidualCell_sq_le_loopEnergy L T B S ?_).trans (loopEnergy_le L T B)
  intro p hp i
  exact mem_biUnion.mpr ⟨p, hp, mem_image.mpr ⟨i, mem_univ i, rfl⟩⟩

/-! ### Supports -/

/-- The explicit shift lives on links along the axes 2 and 3 over columns strictly inside the
sheet, with transverse coordinates between `0` and the depth. -/
theorem loopShiftCell_ne_zero {L T : ℕ} {c : LatticeCell 4} (h : loopShiftCell L T c ≠ 0) :
    ∃ y₀ y₁ y₂ y₃ : ℤ,
      (c = latticeCellOf (false, false, true, false) (y₀, y₁, y₂, y₃) ∨
        c = latticeCellOf (false, false, false, true) (y₀, y₁, y₂, y₃)) ∧
      (2 ≤ y₀ ∧ y₀ + 1 ≤ (L : ℤ)) ∧ (2 ≤ y₁ ∧ y₁ + 1 ≤ (T : ℤ)) ∧
      (0 ≤ y₂ ∧ y₂ ≤ (L : ℤ)) ∧ (0 ≤ y₃ ∧ y₃ ≤ (L : ℤ)) := by
  have hc := latticeCellOf_pattern_base c
  rw [← hc, loopShiftCell, linkField23_latticeCellOf] at h
  refine ⟨latticeCoordBase (c 0), latticeCoordBase (c 1), latticeCoordBase (c 2),
    latticeCoordBase (c 3), ?_⟩
  have hle := loopDepth_le L T (latticeCoordBase (c 0)) (latticeCoordBase (c 1))
  split_ifs at h with h1 h2
  · rw [h1] at hc
    have hs := shiftTwo_ne_zero h
    have hpos := loopDepth_pos (L := L) (T := T) (y₀ := latticeCoordBase (c 0))
      (y₁ := latticeCoordBase (c 1)) (by omega)
    exact ⟨Or.inl hc.symm, hpos.1, hpos.2, by omega, by omega⟩
  · rw [h2] at hc
    have hs := shiftThree_ne_zero h
    have hpos := loopDepth_pos (L := L) (T := T) (y₀ := latticeCoordBase (c 0))
      (y₁ := latticeCoordBase (c 1)) (by omega)
    exact ⟨Or.inr hc.symm, hpos.1, hpos.2, by omega, by omega⟩
  · exact absurd rfl h

/-- The sheet lives on the `2–3` plaquettes based at `(y₀, y₁, 0, 0)`, `1 ≤ y₀ ≤ L`,
`1 ≤ y₁ ≤ T`. -/
theorem sheetCell_ne_zero {L T : ℕ} {c : LatticeCell 4} (h : sheetCell L T c ≠ 0) :
    ∃ y₀ y₁ : ℤ, c = latticeCellOf (false, false, true, true) (y₀, y₁, 0, 0) ∧
      (1 ≤ y₀ ∧ y₀ ≤ (L : ℤ)) ∧ (1 ≤ y₁ ∧ y₁ ≤ (T : ℤ)) := by
  have hc := latticeCellOf_pattern_base c
  rw [← hc, sheetCell, plaquetteField23_latticeCellOf] at h
  split_ifs at h with h1
  · rw [h1] at hc
    unfold sheetCoeff at h
    split_ifs at h with h2
    · rw [h2.2.2.2.2.1, h2.2.2.2.2.2] at hc
      exact ⟨latticeCoordBase (c 0), latticeCoordBase (c 1), hc.symm, ⟨h2.1, h2.2.1⟩,
        ⟨h2.2.2.1, h2.2.2.2.1⟩⟩
    · exact absurd rfl h
  · exact absurd rfl h

theorem sheetCell_latticeCellOf {L T : ℕ} {y₀ y₁ : ℤ} (h₀ : 1 ≤ y₀ ∧ y₀ ≤ (L : ℤ))
    (h₁ : 1 ≤ y₁ ∧ y₁ ≤ (T : ℤ)) :
    sheetCell L T (latticeCellOf (false, false, true, true) (y₀, y₁, 0, 0)) = 1 := by
  rw [sheetCell, plaquetteField23_latticeCellOf, ite_eq_left rfl, sheetCoeff,
    ite_eq_left ⟨h₀.1, h₀.2, h₁.1, h₁.2, rfl, rfl⟩]

/-- Where the sheet is nonzero, it is one and the C2 orientation sign of the cell is `-1`. -/
theorem sheetCell_ne_zero_sign {L T : ℕ} {c : LatticeCell 4} (h : sheetCell L T c ≠ 0) :
    sheetCell L T c = 1 ∧ latticeCellOrientationSign c = -1 := by
  obtain ⟨y₀, y₁, rfl, h₀, h₁⟩ := sheetCell_ne_zero h
  exact ⟨sheetCell_latticeCellOf h₀ h₁, latticeCellOrientationSign_plaquette₂₃ _⟩

end FroehlichSpencer.FS82.Wilson

end
