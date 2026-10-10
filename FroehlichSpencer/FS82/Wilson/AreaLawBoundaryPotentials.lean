/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.AreaLawLocalPotential
public import FroehlichSpencer.FS82.Wilson.AreaLawSource

/-!
# Plaquette tests from the two coordinate directions

The existing step potential detects a plaquette by a vertical ray. These two
horizontal step potentials give the same unit curl and let us compare adjacent
rows of a rectangular sheet.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

@[expose] noncomputable def areaLawHorizontalPotentialBottom {B : Box 4}
    (a : Fin (B 0)) (b : Fin (B 1)) (c : Cell 4 B) : ℤ :=
  if cellDegree c = 1 ∧ (0 : Fin 4) ∈ cellAxes c ∧
      coordBase (c 0) = a.val ∧ coordBase (c 1) ≤ b.val then 1 else 0

@[expose] noncomputable def areaLawHorizontalPotentialTop {B : Box 4}
    (a : Fin (B 0)) (b : Fin (B 1)) (c : Cell 4 B) : ℤ :=
  if cellDegree c = 1 ∧ (0 : Fin 4) ∈ cellAxes c ∧
      coordBase (c 0) = a.val ∧ b.val < coordBase (c 1) then -1 else 0

@[expose] noncomputable def areaLawVerticalPotentialLeft {B : Box 4}
    (a : Fin (B 0)) (b : Fin (B 1)) (c : Cell 4 B) : ℤ :=
  if cellDegree c = 1 ∧ (1 : Fin 4) ∈ cellAxes c ∧
      coordBase (c 1) = b.val ∧ coordBase (c 0) ≤ a.val then -1 else 0

private theorem areaLawHorizontalPotentialBottom_axis1_pairing {B : Box 4}
    (c : Cell 4 B) (e₀ : Fin (B 0)) (e₁ : Fin (B 1))
    (a : Fin (B 0)) (b : Fin (B 1))
    (hc : cellDegree c = 2)
    (h0 : (0 : Fin 4) ∈ cellAxes c) (h1 : (1 : Fin 4) ∈ cellAxes c)
    (hc0 : c 0 = Sum.inr e₀) (hc1 : c 1 = Sum.inr e₁) :
    integerCellPairing (areaLawHorizontalPotentialBottom a b)
      (axisBoundaryBasis c 1) =
      if e₀.val = a.val ∧ e₁.val = b.val then 1 else 0 := by
  classical
  rw [integerCellPairing_axisBoundaryBasis]
  have hsign : cellRankBefore c 1 = 1 := by
    unfold cellRankBefore
    have hs : Finset.univ.filter (fun i : Fin 4 =>
        i < 1 ∧ coordIsEdge (c i)) = {0} := by
      ext i
      fin_cases i <;> simp [coordIsEdge, hc0, hc1]
    rw [hs]
    simp
  rw [hc1, hsign]
  norm_num
  have haxesU : cellAxes (upperFace c 1 e₁) = (cellAxes c).erase 1 :=
    cellAxes_upperFace c 1 e₁
  have haxesL : cellAxes (lowerFace c 1 e₁) = (cellAxes c).erase 1 :=
    cellAxes_lowerFace c 1 e₁
  have hdegU : cellDegree (upperFace c 1 e₁) = 1 := by
    rw [cellDegree, haxesU, Finset.card_erase_of_mem h1]
    unfold cellDegree at hc
    omega
  have hdegL : cellDegree (lowerFace c 1 e₁) = 1 := by
    rw [cellDegree, haxesL, Finset.card_erase_of_mem h1]
    unfold cellDegree at hc
    omega
  have h0U : (0 : Fin 4) ∈ cellAxes (upperFace c 1 e₁) := by
    rw [haxesU]
    exact Finset.mem_erase.mpr ⟨by decide, h0⟩
  have h0L : (0 : Fin 4) ∈ cellAxes (lowerFace c 1 e₁) := by
    rw [haxesL]
    exact Finset.mem_erase.mpr ⟨by decide, h0⟩
  have hcoord0U : coordBase (upperFace c 1 e₁ 0) = e₀.val := by
    rw [upperFace_apply_of_ne c 1 0 e₁ (by decide), hc0]
    rfl
  have hcoord0L : coordBase (lowerFace c 1 e₁ 0) = e₀.val := by
    rw [lowerFace_apply_of_ne c 1 0 e₁ (by decide), hc0]
    rfl
  have hcoord1U : coordBase (upperFace c 1 e₁ 1) = e₁.val + 1 := by
    simp [upperFace, vertexUpdate, coordBase]
  have hcoord1L : coordBase (lowerFace c 1 e₁ 1) = e₁.val := by
    simp [lowerFace, vertexUpdate, coordBase]
  simp only [areaLawHorizontalPotentialBottom, hdegU, hdegL, h0U, h0L,
    hcoord0U, hcoord0L, hcoord1U, hcoord1L]
  by_cases hx : e₀.val = a.val <;> by_cases hy : e₁.val = b.val
  all_goals simp [hx, hy] <;> omega

private theorem areaLawHorizontalPotentialTop_axis1_pairing {B : Box 4}
    (c : Cell 4 B) (e₀ : Fin (B 0)) (e₁ : Fin (B 1))
    (a : Fin (B 0)) (b : Fin (B 1))
    (hc : cellDegree c = 2)
    (h0 : (0 : Fin 4) ∈ cellAxes c) (h1 : (1 : Fin 4) ∈ cellAxes c)
    (hc0 : c 0 = Sum.inr e₀) (hc1 : c 1 = Sum.inr e₁) :
    integerCellPairing (areaLawHorizontalPotentialTop a b)
      (axisBoundaryBasis c 1) =
      if e₀.val = a.val ∧ e₁.val = b.val then 1 else 0 := by
  classical
  rw [integerCellPairing_axisBoundaryBasis]
  have hsign : cellRankBefore c 1 = 1 := by
    unfold cellRankBefore
    have hs : Finset.univ.filter (fun i : Fin 4 =>
        i < 1 ∧ coordIsEdge (c i)) = {0} := by
      ext i
      fin_cases i <;> simp [coordIsEdge, hc0, hc1]
    rw [hs]
    simp
  rw [hc1, hsign]
  norm_num
  have haxesU : cellAxes (upperFace c 1 e₁) = (cellAxes c).erase 1 :=
    cellAxes_upperFace c 1 e₁
  have haxesL : cellAxes (lowerFace c 1 e₁) = (cellAxes c).erase 1 :=
    cellAxes_lowerFace c 1 e₁
  have hdegU : cellDegree (upperFace c 1 e₁) = 1 := by
    rw [cellDegree, haxesU, Finset.card_erase_of_mem h1]
    unfold cellDegree at hc
    omega
  have hdegL : cellDegree (lowerFace c 1 e₁) = 1 := by
    rw [cellDegree, haxesL, Finset.card_erase_of_mem h1]
    unfold cellDegree at hc
    omega
  have h0U : (0 : Fin 4) ∈ cellAxes (upperFace c 1 e₁) := by
    rw [haxesU]
    exact Finset.mem_erase.mpr ⟨by decide, h0⟩
  have h0L : (0 : Fin 4) ∈ cellAxes (lowerFace c 1 e₁) := by
    rw [haxesL]
    exact Finset.mem_erase.mpr ⟨by decide, h0⟩
  have hcoord0U : coordBase (upperFace c 1 e₁ 0) = e₀.val := by
    rw [upperFace_apply_of_ne c 1 0 e₁ (by decide), hc0]
    rfl
  have hcoord0L : coordBase (lowerFace c 1 e₁ 0) = e₀.val := by
    rw [lowerFace_apply_of_ne c 1 0 e₁ (by decide), hc0]
    rfl
  have hcoord1U : coordBase (upperFace c 1 e₁ 1) = e₁.val + 1 := by
    simp [upperFace, vertexUpdate, coordBase]
  have hcoord1L : coordBase (lowerFace c 1 e₁ 1) = e₁.val := by
    simp [lowerFace, vertexUpdate, coordBase]
  simp only [areaLawHorizontalPotentialTop, hdegU, hdegL, h0U, h0L,
    hcoord0U, hcoord0L, hcoord1U, hcoord1L]
  by_cases hx : e₀.val = a.val <;> by_cases hy : e₁.val = b.val
  all_goals simp [hx, hy] <;> omega

private theorem areaLawVerticalPotentialLeft_axis0_pairing {B : Box 4}
    (c : Cell 4 B) (e₀ : Fin (B 0)) (e₁ : Fin (B 1))
    (a : Fin (B 0)) (b : Fin (B 1))
    (hc : cellDegree c = 2)
    (h0 : (0 : Fin 4) ∈ cellAxes c) (h1 : (1 : Fin 4) ∈ cellAxes c)
    (hc0 : c 0 = Sum.inr e₀) (hc1 : c 1 = Sum.inr e₁) :
    integerCellPairing (areaLawVerticalPotentialLeft a b)
      (axisBoundaryBasis c 0) =
      if e₀.val = a.val ∧ e₁.val = b.val then 1 else 0 := by
  classical
  rw [integerCellPairing_axisBoundaryBasis]
  have hsign : cellRankBefore c 0 = 0 := by simp [cellRankBefore]
  rw [hc0, hsign]
  norm_num
  have haxesU : cellAxes (upperFace c 0 e₀) = (cellAxes c).erase 0 :=
    cellAxes_upperFace c 0 e₀
  have haxesL : cellAxes (lowerFace c 0 e₀) = (cellAxes c).erase 0 :=
    cellAxes_lowerFace c 0 e₀
  have hdegU : cellDegree (upperFace c 0 e₀) = 1 := by
    rw [cellDegree, haxesU, Finset.card_erase_of_mem h0]
    unfold cellDegree at hc
    omega
  have hdegL : cellDegree (lowerFace c 0 e₀) = 1 := by
    rw [cellDegree, haxesL, Finset.card_erase_of_mem h0]
    unfold cellDegree at hc
    omega
  have h1U : (1 : Fin 4) ∈ cellAxes (upperFace c 0 e₀) := by
    rw [haxesU]
    exact Finset.mem_erase.mpr ⟨by decide, h1⟩
  have h1L : (1 : Fin 4) ∈ cellAxes (lowerFace c 0 e₀) := by
    rw [haxesL]
    exact Finset.mem_erase.mpr ⟨by decide, h1⟩
  have hcoord0U : coordBase (upperFace c 0 e₀ 0) = e₀.val + 1 := by
    simp [upperFace, vertexUpdate, coordBase]
  have hcoord0L : coordBase (lowerFace c 0 e₀ 0) = e₀.val := by
    simp [lowerFace, vertexUpdate, coordBase]
  have hcoord1U : coordBase (upperFace c 0 e₀ 1) = e₁.val := by
    rw [upperFace_apply_of_ne c 0 1 e₀ (by decide), hc1]
    rfl
  have hcoord1L : coordBase (lowerFace c 0 e₀ 1) = e₁.val := by
    rw [lowerFace_apply_of_ne c 0 1 e₀ (by decide), hc1]
    rfl
  simp only [areaLawVerticalPotentialLeft, hdegU, hdegL, h1U, h1L,
    hcoord0U, hcoord0L, hcoord1U, hcoord1L]
  by_cases hx : e₀.val = a.val <;> by_cases hy : e₁.val = b.val
  all_goals simp [hx, hy] <;> omega

private theorem areaLawHorizontalPotentialBottom_otherAxis_eq {B : Box 4}
    (c : Cell 4 B) (i : Fin 4) (e : Fin (B i)) (a : Fin (B 0))
    (b : Fin (B 1)) (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    areaLawHorizontalPotentialBottom a b (upperFace c i e) =
      areaLawHorizontalPotentialBottom a b (lowerFace c i e) := by
  have haxesU := cellAxes_upperFace c i e
  have haxesL := cellAxes_lowerFace c i e
  have hcoord0 : coordBase (upperFace c i e 0) = coordBase (lowerFace c i e 0) := by
    rw [upperFace_apply_of_ne c i 0 e (Ne.symm hi0),
      lowerFace_apply_of_ne c i 0 e (Ne.symm hi0)]
  have hcoord1 : coordBase (upperFace c i e 1) = coordBase (lowerFace c i e 1) := by
    rw [upperFace_apply_of_ne c i 1 e (Ne.symm hi1),
      lowerFace_apply_of_ne c i 1 e (Ne.symm hi1)]
  simp only [areaLawHorizontalPotentialBottom, cellDegree, haxesU, haxesL,
    hcoord0, hcoord1]

private theorem areaLawHorizontalPotentialTop_otherAxis_eq {B : Box 4}
    (c : Cell 4 B) (i : Fin 4) (e : Fin (B i)) (a : Fin (B 0))
    (b : Fin (B 1)) (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    areaLawHorizontalPotentialTop a b (upperFace c i e) =
      areaLawHorizontalPotentialTop a b (lowerFace c i e) := by
  have haxesU := cellAxes_upperFace c i e
  have haxesL := cellAxes_lowerFace c i e
  have hcoord0 : coordBase (upperFace c i e 0) = coordBase (lowerFace c i e 0) := by
    rw [upperFace_apply_of_ne c i 0 e (Ne.symm hi0),
      lowerFace_apply_of_ne c i 0 e (Ne.symm hi0)]
  have hcoord1 : coordBase (upperFace c i e 1) = coordBase (lowerFace c i e 1) := by
    rw [upperFace_apply_of_ne c i 1 e (Ne.symm hi1),
      lowerFace_apply_of_ne c i 1 e (Ne.symm hi1)]
  simp only [areaLawHorizontalPotentialTop, cellDegree, haxesU, haxesL,
    hcoord0, hcoord1]

private theorem areaLawVerticalPotentialLeft_otherAxis_eq {B : Box 4}
    (c : Cell 4 B) (i : Fin 4) (e : Fin (B i)) (a : Fin (B 0))
    (b : Fin (B 1)) (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    areaLawVerticalPotentialLeft a b (upperFace c i e) =
      areaLawVerticalPotentialLeft a b (lowerFace c i e) := by
  have haxesU := cellAxes_upperFace c i e
  have haxesL := cellAxes_lowerFace c i e
  have hcoord0 : coordBase (upperFace c i e 0) = coordBase (lowerFace c i e 0) := by
    rw [upperFace_apply_of_ne c i 0 e (Ne.symm hi0),
      lowerFace_apply_of_ne c i 0 e (Ne.symm hi0)]
  have hcoord1 : coordBase (upperFace c i e 1) = coordBase (lowerFace c i e 1) := by
    rw [upperFace_apply_of_ne c i 1 e (Ne.symm hi1),
      lowerFace_apply_of_ne c i 1 e (Ne.symm hi1)]
  simp only [areaLawVerticalPotentialLeft, cellDegree, haxesU, haxesL,
    hcoord0, hcoord1]

private theorem coordEdge_mem_cellAxes {B : Box 4} (c : Cell 4 B)
    (i : Fin 4) (e : Fin (B i)) (h : c i = Sum.inr e) :
    i ∈ cellAxes c := by
  classical
  classical
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_univ _
  · change (c i).isRight = true
    simp [h]

theorem areaLawHorizontalPotentialBottom_curl {B : Box 4}
    (p : PrimalPlaquettes B) (a : Fin (B 0)) (b : Fin (B 1)) :
    integerCellPairing (areaLawHorizontalPotentialBottom a b)
      (boundary (basisChain p.1)) =
      if (0 : Fin 4) ∈ cellAxes p.1 ∧ (1 : Fin 4) ∈ cellAxes p.1 ∧
          coordBase (p.1 0) = a.val ∧ coordBase (p.1 1) = b.val
        then 1 else 0 := by
  classical
  rw [integerCellPairing_boundary_basis]
  rw [Finset.sum_eq_single 1]
  · by_cases h0 : (0 : Fin 4) ∈ cellAxes p.1
    · by_cases h1 : (1 : Fin 4) ∈ cellAxes p.1
      · cases hc0 : p.1 0 with
        | inl v =>
            have hn : (0 : Fin 4) ∉ cellAxes p.1 := by
              intro hm
              have he := (Finset.mem_filter.mp hm).2
              simp [coordIsEdge, hc0] at he
            exact (hn h0).elim
        | inr e₀ =>
            cases hc1 : p.1 1 with
            | inl v =>
                have hn : (1 : Fin 4) ∉ cellAxes p.1 := by
                  intro hm
                  have he := (Finset.mem_filter.mp hm).2
                  simp [coordIsEdge, hc1] at he
                exact (hn h1).elim
            | inr e₁ =>
                simpa [coordBase, hc0, hc1, h0, h1] using
                  areaLawHorizontalPotentialBottom_axis1_pairing
                    p.1 e₀ e₁ a b p.2 h0 h1 hc0 hc1
      · rw [integerCellPairing_axisBoundaryBasis]
        cases hc1 : p.1 1 with
        | inl v => simp [h1]
        | inr e =>
            have h1mem := coordEdge_mem_cellAxes p.1 1 e hc1
            exact (h1 h1mem).elim
    · rw [integerCellPairing_axisBoundaryBasis]
      cases hc1 : p.1 1 with
      | inl v => simp [h0]
      | inr e =>
          simp [areaLawHorizontalPotentialBottom, cellAxes_upperFace,
            cellAxes_lowerFace, h0, Finset.mem_erase]
  · intro i hi hne
    by_cases hi0 : i = 0
    · subst i
      rw [integerCellPairing_axisBoundaryBasis]
      cases hc0 : p.1 0 with
      | inl v => simp
      | inr e =>
          have haxesU := cellAxes_upperFace p.1 0 e
          have haxesL := cellAxes_lowerFace p.1 0 e
          have h0U : (0 : Fin 4) ∉ cellAxes (upperFace p.1 0 e) := by
            rw [haxesU]
            simp
          have h0L : (0 : Fin 4) ∉ cellAxes (lowerFace p.1 0 e) := by
            rw [haxesL]
            simp
          simp [areaLawHorizontalPotentialBottom, h0U, h0L]
    · by_cases hi1 : i = 1
      · exact False.elim (hne hi1)
      · cases hci : p.1 i with
        | inl v => simp [axisBoundaryBasis, hci]
        | inr e =>
            rw [integerCellPairing_axisBoundaryBasis]
            simp only [hci]
            rw [areaLawHorizontalPotentialBottom_otherAxis_eq
              p.1 i e a b hi0 hi1]
            ring
  · simp

theorem areaLawHorizontalPotentialTop_curl {B : Box 4}
    (p : PrimalPlaquettes B) (a : Fin (B 0)) (b : Fin (B 1)) :
    integerCellPairing (areaLawHorizontalPotentialTop a b)
      (boundary (basisChain p.1)) =
      if (0 : Fin 4) ∈ cellAxes p.1 ∧ (1 : Fin 4) ∈ cellAxes p.1 ∧
          coordBase (p.1 0) = a.val ∧ coordBase (p.1 1) = b.val
        then 1 else 0 := by
  classical
  rw [integerCellPairing_boundary_basis]
  rw [Finset.sum_eq_single 1]
  · by_cases h0 : (0 : Fin 4) ∈ cellAxes p.1
    · by_cases h1 : (1 : Fin 4) ∈ cellAxes p.1
      · cases hc0 : p.1 0 with
        | inl v =>
            have hn : (0 : Fin 4) ∉ cellAxes p.1 := by
              intro hm
              have he := (Finset.mem_filter.mp hm).2
              simp [coordIsEdge, hc0] at he
            exact (hn h0).elim
        | inr e₀ =>
            cases hc1 : p.1 1 with
            | inl v =>
                have hn : (1 : Fin 4) ∉ cellAxes p.1 := by
                  intro hm
                  have he := (Finset.mem_filter.mp hm).2
                  simp [coordIsEdge, hc1] at he
                exact (hn h1).elim
            | inr e₁ =>
                simpa [coordBase, hc0, hc1, h0, h1] using
                  areaLawHorizontalPotentialTop_axis1_pairing
                    p.1 e₀ e₁ a b p.2 h0 h1 hc0 hc1
      · rw [integerCellPairing_axisBoundaryBasis]
        cases hc1 : p.1 1 with
        | inl v => simp [h1]
        | inr e =>
            have h1mem := coordEdge_mem_cellAxes p.1 1 e hc1
            exact (h1 h1mem).elim
    · rw [integerCellPairing_axisBoundaryBasis]
      cases hc1 : p.1 1 with
      | inl v => simp [h0]
      | inr e =>
          simp [areaLawHorizontalPotentialTop, cellAxes_upperFace,
            cellAxes_lowerFace, h0, Finset.mem_erase]
  · intro i hi hne
    by_cases hi0 : i = 0
    · subst i
      rw [integerCellPairing_axisBoundaryBasis]
      cases hc0 : p.1 0 with
      | inl v => simp
      | inr e =>
          have haxesU := cellAxes_upperFace p.1 0 e
          have haxesL := cellAxes_lowerFace p.1 0 e
          have h0U : (0 : Fin 4) ∉ cellAxes (upperFace p.1 0 e) := by
            rw [haxesU]
            simp
          have h0L : (0 : Fin 4) ∉ cellAxes (lowerFace p.1 0 e) := by
            rw [haxesL]
            simp
          simp [areaLawHorizontalPotentialTop, h0U, h0L]
    · by_cases hi1 : i = 1
      · exact False.elim (hne hi1)
      · cases hci : p.1 i with
        | inl v => simp [axisBoundaryBasis, hci]
        | inr e =>
            rw [integerCellPairing_axisBoundaryBasis]
            simp only [hci]
            rw [areaLawHorizontalPotentialTop_otherAxis_eq
              p.1 i e a b hi0 hi1]
            ring
  · simp

theorem areaLawVerticalPotentialLeft_curl {B : Box 4}
    (p : PrimalPlaquettes B) (a : Fin (B 0)) (b : Fin (B 1)) :
    integerCellPairing (areaLawVerticalPotentialLeft a b)
      (boundary (basisChain p.1)) =
      if (0 : Fin 4) ∈ cellAxes p.1 ∧ (1 : Fin 4) ∈ cellAxes p.1 ∧
          coordBase (p.1 0) = a.val ∧ coordBase (p.1 1) = b.val
        then 1 else 0 := by
  classical
  rw [integerCellPairing_boundary_basis]
  rw [Finset.sum_eq_single 0]
  · by_cases h0 : (0 : Fin 4) ∈ cellAxes p.1
    · by_cases h1 : (1 : Fin 4) ∈ cellAxes p.1
      · cases hc0 : p.1 0 with
        | inl v =>
            have hn : (0 : Fin 4) ∉ cellAxes p.1 := by
              intro hm
              have he := (Finset.mem_filter.mp hm).2
              simp [coordIsEdge, hc0] at he
            exact (hn h0).elim
        | inr e₀ =>
            cases hc1 : p.1 1 with
            | inl v =>
                have hn : (1 : Fin 4) ∉ cellAxes p.1 := by
                  intro hm
                  have he := (Finset.mem_filter.mp hm).2
                  simp [coordIsEdge, hc1] at he
                exact (hn h1).elim
            | inr e₁ =>
                simpa [coordBase, hc0, hc1, h0, h1] using
                  areaLawVerticalPotentialLeft_axis0_pairing
                    p.1 e₀ e₁ a b p.2 h0 h1 hc0 hc1
      · rw [integerCellPairing_axisBoundaryBasis]
        cases hc0 : p.1 0 with
        | inl v =>
            have hn : (0 : Fin 4) ∉ cellAxes p.1 := by
              intro hm
              have he := (Finset.mem_filter.mp hm).2
              simp [coordIsEdge, hc0] at he
            exact (hn h0).elim
        | inr e =>
            simp [areaLawVerticalPotentialLeft, cellAxes_upperFace,
              cellAxes_lowerFace, h1, Finset.mem_erase]
    · rw [integerCellPairing_axisBoundaryBasis]
      cases hc0 : p.1 0 with
      | inl v => simp [h0]
      | inr e =>
          have h0mem := coordEdge_mem_cellAxes p.1 0 e hc0
          exact (h0 h0mem).elim
  · intro i hi hne
    by_cases hi1 : i = 1
    · subst i
      cases hc1 : p.1 1 with
      | inl v => simp [axisBoundaryBasis, hc1]
      | inr e =>
          have haxesU := cellAxes_upperFace p.1 1 e
          have haxesL := cellAxes_lowerFace p.1 1 e
          have h1U : (1 : Fin 4) ∉ cellAxes (upperFace p.1 1 e) := by
            rw [haxesU]
            simp
          have h1L : (1 : Fin 4) ∉ cellAxes (lowerFace p.1 1 e) := by
            rw [haxesL]
            simp
          rw [integerCellPairing_axisBoundaryBasis]
          simp [hc1, areaLawVerticalPotentialLeft, h1U, h1L]
    · have hi0 : i ≠ 0 := by
        intro h
        exact hne h
      cases hci : p.1 i with
      | inl v => simp [axisBoundaryBasis, hci]
      | inr e =>
          rw [integerCellPairing_axisBoundaryBasis]
          simp only [hci]
          rw [areaLawVerticalPotentialLeft_otherAxis_eq
            p.1 i e a b hi0 hi1]
          ring
  · simp


end FroehlichSpencer.FS82.Wilson

end
