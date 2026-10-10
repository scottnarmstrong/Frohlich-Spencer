/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Cubical.IntegerPrism
public import FroehlichSpencer.FS82.Wilson.DualityFinite

/-!
# An area lower bound for source fields

Pairing with the linear coordinate potential bounds the integer `ℓ¹` mass of
any plaquette field with rectangular boundary by the rectangle's area. The
potential has unit curl on `0–1` plaquettes and zero curl on the other faces.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

/-- The coordinate potential on primal links: it is the first coordinate on
links parallel to axis `1`, and zero on the other links. -/
@[expose] noncomputable def areaTestPotential {B : Box 4} (c : Cell 4 B) : ℤ :=
  if cellDegree c = 1 ∧ (1 : Fin 4) ∈ cellAxes c then
    (coordBase (c 0) : ℤ)
  else 0

/-- Integer pairing of a cell cochain with a finite cubical chain. -/
@[expose] noncomputable def integerCellPairing {B : Box 4}
    (f : Cell 4 B → ℤ) (q : Chain 4 B) : ℤ :=
  ∑ c : Cell 4 B, q c * f c

@[simp] theorem integerCellPairing_zero {B : Box 4} (f : Cell 4 B → ℤ) :
    integerCellPairing f (0 : Chain 4 B) = 0 := by
  simp [integerCellPairing]

theorem integerCellPairing_add {B : Box 4} (f : Cell 4 B → ℤ)
    (q r : Chain 4 B) :
    integerCellPairing f (q + r) = integerCellPairing f q + integerCellPairing f r := by
  simp [integerCellPairing, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]

theorem integerCellPairing_smul {B : Box 4} (f : Cell 4 B → ℤ)
    (n : ℤ) (q : Chain 4 B) :
    integerCellPairing f (n • q) = n * integerCellPairing f q := by
  simp only [integerCellPairing, Finsupp.smul_apply, zsmul_eq_mul]
  calc
    (∑ c : Cell 4 B, n * q c * f c) =
        ∑ c : Cell 4 B, n * (q c * f c) := by
          apply Finset.sum_congr rfl
          intro c hc
          ring
    _ = n * ∑ c : Cell 4 B, q c * f c := by rw [← Finset.mul_sum]

@[simp] theorem integerCellPairing_basis {B : Box 4} (f : Cell 4 B → ℤ)
    (c : Cell 4 B) :
    integerCellPairing f (basisChain c) = f c := by
  simp [integerCellPairing, basisChain, Finsupp.single_apply]

@[expose] noncomputable def integerCellPairingLinear {B : Box 4}
    (f : Cell 4 B → ℤ) : Chain 4 B →ₗ[ℤ] ℤ where
  toFun := integerCellPairing f
  map_add' := integerCellPairing_add f
  map_smul' := by
    intro n q
    rw [integerCellPairing_smul]
    rfl


theorem integerCellPairing_axisBoundaryBasis {B : Box 4}
    (f : Cell 4 B → ℤ) (c : Cell 4 B) (i : Fin 4) :
    integerCellPairing f (axisBoundaryBasis c i) =
      match c i with
      | Sum.inl _ => 0
      | Sum.inr e =>
          (-1 : ℤ) ^ cellRankBefore c i *
            (f (upperFace c i e) - f (lowerFace c i e)) := by
  cases hci : c i with
  | inl v => simp [axisBoundaryBasis, hci]
  | inr e =>
      rw [axisBoundaryBasis, hci]
      rw [integerCellPairing_smul]
      rw [sub_eq_add_neg, integerCellPairing_add]
      rw [show -basisChain (lowerFace c i e) = (-1 : ℤ) •
        basisChain (lowerFace c i e) by simp, integerCellPairing_smul,
        integerCellPairing_basis, integerCellPairing_basis]
      ring

theorem axisBoundary_basis {B : Box 4} (i : Fin 4) (c : Cell 4 B) :
    axisBoundary i (basisChain c) = axisBoundaryBasis c i := by
  simp [axisBoundary, basisChain, Finsupp.linearCombination_single]

theorem integerCellPairing_boundary_basis {B : Box 4}
    (f : Cell 4 B → ℤ) (c : Cell 4 B) :
    integerCellPairing f (boundary (basisChain c)) =
      ∑ i : Fin 4, integerCellPairing f (axisBoundaryBasis c i) := by
  calc
    integerCellPairing f (boundary (basisChain c)) =
        integerCellPairingLinear f (boundary (basisChain c)) := rfl
    _ = ∑ i : Fin 4, integerCellPairingLinear f (axisBoundary i (basisChain c)) := by
        change integerCellPairingLinear f
          (∑ i : Fin 4, axisBoundary i (basisChain c)) = _
        rw [map_sum]
    _ = ∑ i : Fin 4, integerCellPairing f (axisBoundaryBasis c i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [axisBoundary_basis]
        rfl

theorem areaTestPotential_upper_eq_lower {B : Box 4} (c : Cell 4 B)
    (i : Fin 4) (e : Fin (B i)) (hi0 : i ≠ 0) :
    areaTestPotential (upperFace c i e) = areaTestPotential (lowerFace c i e) := by
  have haxesU := cellAxes_upperFace c i e
  have haxesL := cellAxes_lowerFace c i e
  have hcoord : coordBase (upperFace c i e 0) = coordBase (lowerFace c i e 0) := by
    calc
      coordBase (upperFace c i e 0) = coordBase (c 0) :=
        congrArg coordBase (upperFace_apply_of_ne c i 0 e (Ne.symm hi0))
      _ = coordBase (lowerFace c i e 0) :=
        (congrArg coordBase (lowerFace_apply_of_ne c i 0 e (Ne.symm hi0))).symm
  simp only [areaTestPotential]
  rw [cellDegree, haxesU, cellDegree, haxesL, hcoord]

theorem areaTestPotential_faces_axis1_zero {B : Box 4} (c : Cell 4 B)
    (e : Fin (B 1)) :
    areaTestPotential (upperFace c 1 e) = 0 ∧
      areaTestPotential (lowerFace c 1 e) = 0 := by
  constructor <;> simp [areaTestPotential, cellDegree, cellAxes_upperFace,
    cellAxes_lowerFace]

theorem areaTestPotential_axis0_face_difference {B : Box 4}
    (c : Cell 4 B) (e : Fin (B 0)) (hc : cellDegree c = 2)
    (h0 : (0 : Fin 4) ∈ cellAxes c) :
    areaTestPotential (upperFace c 0 e) -
      areaTestPotential (lowerFace c 0 e) =
        if (1 : Fin 4) ∈ cellAxes c then 1 else 0 := by
  have haxes : cellAxes (upperFace c 0 e) = (cellAxes c).erase 0 :=
    cellAxes_upperFace c 0 e
  have hcard : (cellAxes (upperFace c 0 e)).card = 1 := by
    rw [haxes, Finset.card_erase_of_mem h0]
    unfold cellDegree at hc
    omega
  have hcoordU : coordBase (upperFace c 0 e 0) = e.val + 1 := by
    simp [upperFace, vertexUpdate, coordBase]
  have hcoordL : coordBase (lowerFace c 0 e 0) = e.val := by
    simp [lowerFace, vertexUpdate, coordBase]
  by_cases h1 : (1 : Fin 4) ∈ cellAxes c
  · have h1U : (1 : Fin 4) ∈ cellAxes (upperFace c 0 e) := by
      rw [haxes]
      exact Finset.mem_erase.mpr ⟨by decide, h1⟩
    have h1L : (1 : Fin 4) ∈ cellAxes (lowerFace c 0 e) := by
      rw [cellAxes_lowerFace]
      exact Finset.mem_erase.mpr ⟨by decide, h1⟩
    have hcardL : cellDegree (lowerFace c 0 e) = 1 := by
      rw [cellDegree, cellAxes_lowerFace, Finset.card_erase_of_mem h0]
      unfold cellDegree at hc
      omega
    have hdegU : cellDegree (upperFace c 0 e) = 1 := by
      simpa [cellDegree] using hcard
    simp [areaTestPotential, hdegU, hcardL, h1U, h1L, hcoordU, hcoordL, h1]
  · have h1U : (1 : Fin 4) ∉ cellAxes (upperFace c 0 e) := by
      rw [haxes]
      simp [Finset.mem_erase, h1]
    have h1L : (1 : Fin 4) ∉ cellAxes (lowerFace c 0 e) := by
      rw [cellAxes_lowerFace]
      simp [Finset.mem_erase, h1]
    simp [areaTestPotential, h1U, h1L, h1]

theorem areaTestPotential_axis0_face_pairing {B : Box 4}
    (c : Cell 4 B) (hc : cellDegree c = 2)
    (h0 : (0 : Fin 4) ∈ cellAxes c) :
    integerCellPairing areaTestPotential (axisBoundaryBasis c 0) =
      if (1 : Fin 4) ∈ cellAxes c then 1 else 0 := by
  classical
  rw [integerCellPairing_axisBoundaryBasis]
  have hsign : cellRankBefore c 0 = 0 := by
    simp [cellRankBefore]
  cases hc0 : c 0 with
  | inl v =>
      have : (0 : Fin 4) ∉ cellAxes c := by
        intro hmem
        have hright : coordIsEdge (c 0) := (Finset.mem_filter.mp hmem).2
        simp [coordIsEdge, hc0] at hright
      exact False.elim (this h0)
  | inr e' =>
      rw [hsign]
      norm_num
      exact areaTestPotential_axis0_face_difference c e' hc h0

theorem areaTestPotential_axisOther_face_pairing {B : Box 4}
    (c : Cell 4 B) (i : Fin 4)
    (hi0 : i ≠ 0) :
    integerCellPairing areaTestPotential (axisBoundaryBasis c i) = 0 := by
  rw [integerCellPairing_axisBoundaryBasis]
  cases hci : c i with
  | inl v => simp
  | inr e' =>
      simp only
      rw [areaTestPotential_upper_eq_lower c i e' hi0]
      ring

theorem areaTestPotential_axis1_face_pairing {B : Box 4}
    (c : Cell 4 B) :
    integerCellPairing areaTestPotential (axisBoundaryBasis c 1) = 0 := by
  rw [integerCellPairing_axisBoundaryBasis]
  cases hci : c 1 with
  | inl v => simp
  | inr e' =>
      simp only
      rcases areaTestPotential_faces_axis1_zero c e' with ⟨hu, hl⟩
      rw [hu, hl]
      ring

/-- The curl of the coordinate potential on one plaquette. -/
@[expose] noncomputable def areaTestPlaquetteCurl {B : Box 4}
    (p : PrimalPlaquettes B) : ℤ :=
  integerCellPairing areaTestPotential (boundary (basisChain p.1))

theorem areaTestPlaquetteCurl_eq_axes {B : Box 4} (p : PrimalPlaquettes B) :
    areaTestPlaquetteCurl p =
      if (0 : Fin 4) ∈ cellAxes p.1 ∧ (1 : Fin 4) ∈ cellAxes p.1 then 1 else 0 := by
  classical
  rw [areaTestPlaquetteCurl, integerCellPairing_boundary_basis]
  rw [Finset.sum_eq_single 0]
  · cases hc0 : p.1 0 with
    | inl v =>
        have h0 : (0 : Fin 4) ∉ cellAxes p.1 := by
          intro hmem
          have hright : coordIsEdge (p.1 0) := (Finset.mem_filter.mp hmem).2
          simp [coordIsEdge, hc0] at hright
        rw [integerCellPairing_axisBoundaryBasis]
        simp [hc0, h0]
    | inr e =>
        have h0 : (0 : Fin 4) ∈ cellAxes p.1 := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            simp [coordIsEdge, hc0]⟩
        rw [areaTestPotential_axis0_face_pairing p.1 p.2 h0]
        simp [h0]
  · intro i hi hne
    by_cases hi1 : i = 1
    · subst i
      exact areaTestPotential_axis1_face_pairing p.1
    · exact areaTestPotential_axisOther_face_pairing p.1 i (by
        intro h
        exact hne h)
  · simp

end FroehlichSpencer.FS82.Wilson

end
