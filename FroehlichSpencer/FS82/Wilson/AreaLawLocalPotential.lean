/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.AreaLawEnergy

/-!
# Local plaquette tests

A step-function link potential whose curl tests one planar plaquette.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

/-- A step-function link potential whose curl tests the plaquette at coordinates a and b. -/
@[expose] noncomputable def areaLocalPotential {B : Box 4} (a : Fin (B 0)) (b : Fin (B 1))
    (c : Cell 4 B) : ℤ :=
  if cellDegree c = 1 ∧ (1 : Fin 4) ∈ cellAxes c ∧
      coordBase (c 1) = b.val ∧ a.val < coordBase (c 0) then 1 else 0

theorem areaLocalPotential_axis0_difference {B : Box 4}
    (c : Cell 4 B) (e₀ : Fin (B 0)) (e₁ : Fin (B 1))
    (a : Fin (B 0)) (b : Fin (B 1))
    (hc : cellDegree c = 2)
    (h0 : (0 : Fin 4) ∈ cellAxes c) (h1 : (1 : Fin 4) ∈ cellAxes c)
    (hc1 : c 1 = Sum.inr e₁) :
    areaLocalPotential a b (upperFace c 0 e₀) -
      areaLocalPotential a b (lowerFace c 0 e₀) =
        if e₀.val = a.val ∧ e₁.val = b.val then 1 else 0 := by
  have haxesU : cellAxes (upperFace c 0 e₀) = (cellAxes c).erase 0 :=
    cellAxes_upperFace c 0 e₀
  have haxesL : cellAxes (lowerFace c 0 e₀) = (cellAxes c).erase 0 :=
    cellAxes_lowerFace c 0 e₀
  have hcardU : cellDegree (upperFace c 0 e₀) = 1 := by
    rw [cellDegree, haxesU, Finset.card_erase_of_mem h0]
    unfold cellDegree at hc
    omega
  have hcardL : cellDegree (lowerFace c 0 e₀) = 1 := by
    rw [cellDegree, haxesL, Finset.card_erase_of_mem h0]
    unfold cellDegree at hc
    omega
  have h1U : (1 : Fin 4) ∈ cellAxes (upperFace c 0 e₀) := by
    rw [haxesU]
    exact Finset.mem_erase.mpr ⟨by decide, h1⟩
  have h1L : (1 : Fin 4) ∈ cellAxes (lowerFace c 0 e₀) := by
    rw [haxesL]
    exact Finset.mem_erase.mpr ⟨by decide, h1⟩
  have hcoordU : coordBase (upperFace c 0 e₀ 0) = e₀.val + 1 := by
    simp [upperFace, vertexUpdate, coordBase]
  have hcoordL : coordBase (lowerFace c 0 e₀ 0) = e₀.val := by
    simp [lowerFace, vertexUpdate, coordBase]
  have hcoord1U : coordBase (upperFace c 0 e₀ 1) = e₁.val := by
    rw [upperFace_apply_of_ne c 0 1 e₀ (by decide), hc1]
    rfl
  have hcoord1L : coordBase (lowerFace c 0 e₀ 1) = e₁.val := by
    rw [lowerFace_apply_of_ne c 0 1 e₀ (by decide), hc1]
    rfl
  simp only [areaLocalPotential, hcardU, hcardL, h1U, h1L,
    hcoordU, hcoordL, hcoord1U, hcoord1L]
  by_cases hy : e₁.val = b.val <;> by_cases hx : e₀.val = a.val
  all_goals simp [hy, hx] <;> omega

theorem areaLocalPotential_other_axis_difference {B : Box 4}
    (c : Cell 4 B) (i : Fin 4) (e : Fin (B i))
    (a : Fin (B 0)) (b : Fin (B 1))
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    areaLocalPotential a b (upperFace c i e) =
      areaLocalPotential a b (lowerFace c i e) := by
  have haxesU := cellAxes_upperFace c i e
  have haxesL := cellAxes_lowerFace c i e
  have hcoord0 : coordBase (upperFace c i e 0) = coordBase (lowerFace c i e 0) := by
    rw [upperFace_apply_of_ne c i 0 e (Ne.symm hi0),
      lowerFace_apply_of_ne c i 0 e (Ne.symm hi0)]
  have hcoord1 : coordBase (upperFace c i e 1) = coordBase (lowerFace c i e 1) := by
    rw [upperFace_apply_of_ne c i 1 e (Ne.symm hi1),
      lowerFace_apply_of_ne c i 1 e (Ne.symm hi1)]
  simp only [areaLocalPotential, cellDegree, haxesU, haxesL, hcoord0, hcoord1]

theorem areaLocalPotential_axis1_face_zero {B : Box 4}
    (c : Cell 4 B) (e : Fin (B 1)) (a : Fin (B 0)) (b : Fin (B 1)) :
    areaLocalPotential a b (upperFace c 1 e) = 0 ∧
      areaLocalPotential a b (lowerFace c 1 e) = 0 := by
  constructor <;> simp [areaLocalPotential, cellDegree,
    cellAxes_upperFace, cellAxes_lowerFace]

theorem areaLocalPotential_axis0_pairing {B : Box 4}
    (c : Cell 4 B) (e₀ : Fin (B 0)) (e₁ : Fin (B 1))
    (a : Fin (B 0)) (b : Fin (B 1))
    (hc : cellDegree c = 2)
    (h0 : (0 : Fin 4) ∈ cellAxes c) (h1 : (1 : Fin 4) ∈ cellAxes c)
    (hc0 : c 0 = Sum.inr e₀) (hc1 : c 1 = Sum.inr e₁) :
    integerCellPairing (areaLocalPotential a b) (axisBoundaryBasis c 0) =
      if e₀.val = a.val ∧ e₁.val = b.val then 1 else 0 := by
  rw [integerCellPairing_axisBoundaryBasis]
  have hsign : cellRankBefore c 0 = 0 := by simp [cellRankBefore]
  rw [hc0, hsign]
  norm_num
  exact areaLocalPotential_axis0_difference c e₀ e₁ a b hc h0 h1 hc1

theorem areaLocalPotential_curl {B : Box 4} (p : PrimalPlaquettes B)
    (a : Fin (B 0)) (b : Fin (B 1)) :
    integerCellPairing (areaLocalPotential a b) (boundary (basisChain p.1)) =
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
              have hr : coordIsEdge (p.1 0) := (Finset.mem_filter.mp hm).2
              simp [coordIsEdge, hc0] at hr
            exact (hn h0).elim
        | inr e₀ =>
            cases hc1 : p.1 1 with
            | inl v =>
                have hn : (1 : Fin 4) ∉ cellAxes p.1 := by
                  intro hm
                  have hr : coordIsEdge (p.1 1) := (Finset.mem_filter.mp hm).2
                  simp [coordIsEdge, hc1] at hr
                exact (hn h1).elim
            | inr e₁ =>
                have hp := areaLocalPotential_axis0_pairing p.1 e₀ e₁ a b
                  p.2 h0 h1 hc0 hc1
                simpa [hc0, hc1, coordBase, h0, h1] using hp
      · rw [integerCellPairing_axisBoundaryBasis]
        cases hc0 : p.1 0 with
        | inl v =>
            have hn : (0 : Fin 4) ∉ cellAxes p.1 := by
              intro hm
              have hr : coordIsEdge (p.1 0) := (Finset.mem_filter.mp hm).2
              simp [coordIsEdge, hc0] at hr
            exact (hn h0).elim
        | inr e =>
            have haxesU := cellAxes_upperFace p.1 0 e
            have haxesL := cellAxes_lowerFace p.1 0 e
            simp [areaLocalPotential, haxesU, haxesL, h1]
    · rw [integerCellPairing_axisBoundaryBasis]
      cases hc0 : p.1 0 with
      | inl v => simp [h0]
      | inr e =>
          have hfalse : False := h0 (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, by simp [coordIsEdge, hc0]⟩)
          exact hfalse.elim
  · intro i hi hne
    by_cases hi1 : i = 1
    · subst i
      cases hc1 : p.1 1 with
      | inl v =>
          have hzero : axisBoundaryBasis p.1 1 = 0 := by
            simp [axisBoundaryBasis, hc1]
          rw [hzero]
          simp
      | inr e =>
          rcases areaLocalPotential_axis1_face_zero p.1 e a b with ⟨hu, hl⟩
          rw [integerCellPairing_axisBoundaryBasis]
          simp only [hc1, hu, hl, sub_self, mul_zero]
    · have hi0 : i ≠ 0 := by
        intro h
        exact hne h
      cases hci : p.1 i with
      | inl v => simp [axisBoundaryBasis, hci]
      | inr e =>
          rw [integerCellPairing_axisBoundaryBasis]
          simp only [hci]
          rw [areaLocalPotential_other_axis_difference p.1 i e a b hi0 hi1]
          ring
  · simp

end FroehlichSpencer.FS82.Wilson

end
