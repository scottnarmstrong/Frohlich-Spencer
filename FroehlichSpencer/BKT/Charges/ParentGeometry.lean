/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.ScaleMonotonicity

/-! # Explicit containing parents for separated squares

This module implements the first geometric part of  For a source square
of side `2^k` and ancestor offset `j ∈ {1,2,3,4}`, its target side is
`2^(k+j)` and its centering radius is `(2^j - 1)2^(k-1)`, equal to KP's
`(2^j - 1)2^k/2` for `k ≥ 1`. -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- Source scales in the parent-selector construction are positive. -/
abbrev PositiveSquareScale := {k : ℕ // 1 ≤ k}

/-- The first four ancestor offsets. -/
abbrev ParentOffset := {j : ℕ // 1 ≤ j ∧ j ≤ 4}

/-- The target scale for the `j`th parent of a scale-`k` square. -/
def ancestorScale (k : PositiveSquareScale) (j : ParentOffset) : ℕ := k.val + j.val

/-- The side of the `j`th ancestor square. -/
def ancestorSide (k : PositiveSquareScale) (j : ParentOffset) : ℕ :=
  squareSide (ancestorScale k j)

/-- The centering radius for the `j`th ancestor, in the equivalent integral
form `(2^j - 1) 2^(k-1)`. -/
def ancestorRadius (k : PositiveSquareScale) (j : ParentOffset) : ℕ :=
  (2 ^ j.val - 1) * 2 ^ (k.val - 1)

/-- The radius agrees with the formula `(2^j - 1) 2^k / 2` in  -/
theorem ancestorRadius_eq_outline (k : PositiveSquareScale) (j : ParentOffset) :
    ancestorRadius k j = ((2 ^ j.val - 1) * squareSide k.val) / 2 := by
  have hk' : k.val - 1 + 1 = k.val := by omega
  have hdiv : 2 ∣ 2 ^ (k.val - 1) * 2 :=
    ⟨2 ^ (k.val - 1), by rw [Nat.mul_comm]⟩
  have hpow : 2 ^ k.val = 2 ^ (k.val - 1) * 2 := by
    calc
      2 ^ k.val = 2 ^ (k.val - 1 + 1) :=
        congrArg (fun n : ℕ => 2 ^ n) hk'.symm
      _ = 2 ^ (k.val - 1) * 2 := by rw [pow_succ]
  change (2 ^ j.val - 1) * 2 ^ (k.val - 1) =
    ((2 ^ j.val - 1) * 2 ^ k.val) / 2
  rw [hpow]
  rw [Nat.mul_div_assoc _ hdiv]
  simp

/-- The target side is the child side plus twice the centering radius. -/
theorem ancestorSide_eq (k : PositiveSquareScale) (j : ParentOffset) :
    ancestorSide k j = squareSide k.val + 2 * ancestorRadius k j := by
  have hk : k.val = k.val - 1 + 1 := by omega
  have hj : (2 : ℕ) ^ j.val - 1 + 1 = 2 ^ j.val :=
    Nat.sub_add_cancel (by exact Nat.one_le_pow j.val 2 (by decide))
  calc
    ancestorSide k j = 2 ^ k.val * 2 ^ j.val := by
      simp [ancestorSide, ancestorScale, squareSide, Nat.pow_add]
    _ = 2 ^ k.val * ((2 ^ j.val - 1) + 1) := by
      exact congrArg (fun n : ℕ => 2 ^ k.val * n) hj.symm
    _ = 2 ^ k.val + (2 ^ j.val - 1) * 2 ^ k.val := by ring
    _ = 2 ^ k.val + 2 * ((2 ^ j.val - 1) * 2 ^ (k.val - 1)) := by
      have hpow : 2 ^ k.val = 2 ^ (k.val - 1) * 2 := by
        have hk' : k.val - 1 + 1 = k.val := by omega
        calc
          2 ^ k.val = 2 ^ (k.val - 1 + 1) :=
            congrArg (fun n : ℕ => 2 ^ n) hk'.symm
          _ = 2 ^ (k.val - 1) * 2 := by rw [pow_succ]
      rw [hpow]
      ring
    _ = squareSide k.val + 2 * ancestorRadius k j := rfl

/-- Clamp a free-boundary parent lower coordinate to the allowed statement
interval `[0, L-q]`; natural subtraction implements the lower clamp at zero. -/
def freeParentCoordinate (L q r a : ℕ) : ℕ := min (a - r) (L - q)

/-- The lower-corner statement of an allowed ancestor square. -/
def ancestorAnchor (boundary : SquareBoundary) (L : ℕ) (k : PositiveSquareScale)
    (j : ParentOffset) (hL : 0 < L) (a : Fin L × Fin L) : Fin L × Fin L :=
  match boundary with
  | .free =>
      let q := ancestorSide k j
      let r := ancestorRadius k j
      (⟨freeParentCoordinate L q r a.1.val,
          by
            have hq : 0 < q := Nat.pow_pos (by decide)
            have hsub : L - q < L := by omega
            exact (Nat.min_le_right _ _).trans_lt hsub⟩,
       ⟨freeParentCoordinate L q r a.2.val,
          by
            have hq : 0 < q := Nat.pow_pos (by decide)
            have hsub : L - q < L := by omega
            exact (Nat.min_le_right _ _).trans_lt hsub⟩)
  | .periodic =>
      let r := ancestorRadius k j
      (⟨(a.1.val + L - r) % L, Nat.mod_lt _ hL⟩,
       ⟨(a.2.val + L - r) % L, Nat.mod_lt _ hL⟩)

/-- The explicit parent based at a given lower-corner statement. -/
def parentFromAnchor (boundary : SquareBoundary) (L : ℕ) (k : PositiveSquareScale)
    (j : ParentOffset) (hL : 0 < L) (a : Fin L × Fin L) : Finset (Fin L × Fin L) :=
  kpSquare boundary L (ancestorScale k j) (ancestorAnchor boundary L k j hL a)

/-- The explicit parent `P_j(s)` of a source square, using its selected
lower-corner statement. -/
noncomputable def ancestorParent (boundary : SquareBoundary) (L : ℕ)
    (k : PositiveSquareScale) (j : ParentOffset) (hL : 0 < L)
    (s : Finset (Fin L × Fin L)) : Finset (Fin L × Fin L) :=
  parentFromAnchor boundary L k j hL (squareAnchor boundary L k.val hL s)

/-- Every explicit parent is an allowed square at its target scale. -/
theorem parentFromAnchor_mem_kpSquares (boundary : SquareBoundary) (L : ℕ)
    (k : PositiveSquareScale) (j : ParentOffset) (hL : 0 < L)
    (a : Fin L × Fin L) :
    parentFromAnchor boundary L k j hL a ∈ kpSquares boundary L (ancestorScale k j) := by
  exact Finset.mem_image.mpr
    ⟨ancestorAnchor boundary L k j hL a, Finset.mem_univ _, rfl⟩

/-- The selected parent of a square is an allowed square at the target scale. -/
theorem ancestorParent_mem_kpSquares (boundary : SquareBoundary) (L : ℕ)
    (k : PositiveSquareScale) (j : ParentOffset) (hL : 0 < L)
    (s : Finset (Fin L × Fin L)) :
    ancestorParent boundary L k j hL s ∈ kpSquares boundary L (ancestorScale k j) := by
  exact parentFromAnchor_mem_kpSquares boundary L k j hL
    (squareAnchor boundary L k.val hL s)

/-- Membership in a free square when its side fits in the domain. -/
theorem mem_kpSquare_free_iff (L k : ℕ) (hside : squareSide k ≤ L)
    (a x : Fin L × Fin L) :
    x ∈ kpSquare .free L k a ↔
      a.1.val ≤ x.1.val ∧ x.1.val < a.1.val + squareSide k ∧
        a.2.val ≤ x.2.val ∧ x.2.val < a.2.val + squareSide k := by
  simp [kpSquare, Nat.not_lt.mpr hside]

/-- Membership in a periodic square when its side is below the period. -/
theorem mem_kpSquare_periodic_iff (L k : ℕ) (hside : squareSide k < L)
    (a x : Fin L × Fin L) :
    x ∈ kpSquare .periodic L k a ↔
      ∃ i ∈ Finset.range (squareSide k), ∃ m ∈ Finset.range (squareSide k),
        x.1.val = (a.1.val + i) % L ∧ x.2.val = (a.2.val + m) % L := by
  simp [kpSquare, Nat.not_le_of_gt hside]

/-- The centered expansion of a free square, clipped to the domain, or its
periodic quotient image. -/
noncomputable def centeredExpansion (boundary : SquareBoundary) (L : ℕ)
    (k : PositiveSquareScale) (j : ParentOffset) (a : Fin L × Fin L) :
    Finset (Fin L × Fin L) := by
  classical
  let q := ancestorSide k j
  let r := ancestorRadius k j
  exact match boundary with
  | .free => Finset.univ.filter fun x =>
      a.1.val ≤ x.1.val + r ∧ x.1.val < a.1.val + squareSide k.val + r ∧
      a.2.val ≤ x.2.val + r ∧ x.2.val < a.2.val + squareSide k.val + r
  | .periodic =>
      if q ≥ L then Finset.univ else
        Finset.univ.filter fun x =>
          ∃ i ∈ Finset.range q, ∃ m ∈ Finset.range q,
            x.1.val = ((a.1.val + L - r) % L + i) % L ∧
            x.2.val = ((a.2.val + L - r) % L + m) % L

/-- A free square lies in its coordinatewise clipped centered expansion. -/
theorem kpSquare_free_subset_centeredExpansion (L k : ℕ)
    (hkpos : 1 ≤ k) (hk : squareSide k ≤ L) (j : ParentOffset)
    (a : Fin L × Fin L) :
    kpSquare .free L k a ⊆ centeredExpansion .free L ⟨k, hkpos⟩ j a := by
  intro x hx
  have hx' := (mem_kpSquare_free_iff L k hk a x).1 hx
  simp only [centeredExpansion, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hx' with ⟨hleft1, hright1, hleft2, hright2⟩
  have hr : 0 ≤ ancestorRadius ⟨k, hkpos⟩ j := Nat.zero_le _
  exact ⟨by omega, by omega, by omega, by omega⟩

private theorem periodicCenteredIndex (a L r i : ℕ) (hrL : r ≤ L) :
    ((a + L - r) % L + (i + r)) % L = (a + i) % L := by
  have h1 : (a + L - r) % L + (i + r) ≡ a + L - r + (i + r) [MOD L] :=
    (Nat.mod_modEq (a + L - r) L).add_right (i + r)
  have h2 : a + L - r + (i + r) ≡ a + i [MOD L] := by
    change (a + L - r + (i + r)) % L = (a + i) % L
    rw [show a + L - r + (i + r) = a + i + L by omega]
    simp
  change ((a + L - r) % L + (i + r)) % L = (a + i) % L
  exact h1.trans h2

/-- A periodic square lies in its quotient centered expansion. The offset
indices are shifted by the centering radius; the quotient arithmetic is kept
explicit in `periodicCenteredIndex`. -/
theorem kpSquare_periodic_subset_centeredExpansion (L : ℕ)
    (k : PositiveSquareScale) (j : ParentOffset) (a : Fin L × Fin L) :
    kpSquare .periodic L k.val a ⊆ centeredExpansion .periodic L k j a := by
  by_cases hq : ancestorSide k j ≥ L
  · intro x hx
    simp [centeredExpansion, hq]
  · have hqLt : ancestorSide k j < L := Nat.lt_of_not_ge hq
    have hside_le : squareSide k.val ≤ ancestorSide k j := by
      change 2 ^ k.val ≤ 2 ^ (k.val + j.val)
      rw [pow_add]
      have hj : 1 ≤ 2 ^ j.val := Nat.one_le_pow j.val 2 (by decide)
      calc
        2 ^ k.val = 2 ^ k.val * 1 := by simp
        _ ≤ 2 ^ k.val * 2 ^ j.val := Nat.mul_le_mul_left _ hj
    have hkLt : squareSide k.val < L := lt_of_le_of_lt hside_le hqLt
    intro x hx
    have hx' := (mem_kpSquare_periodic_iff L k.val hkLt a x).1 hx
    rcases hx' with ⟨i, hi, m, hm, hxy⟩
    have hwidth := ancestorSide_eq k j
    have hrL : ancestorRadius k j ≤ L := by omega
    have hi_lt : i < squareSide k.val := Finset.mem_range.mp hi
    have hm_lt : m < squareSide k.val := Finset.mem_range.mp hm
    have hi' : i + ancestorRadius k j < ancestorSide k j := by omega
    have hm' : m + ancestorRadius k j < ancestorSide k j := by omega
    have hxy' :
        x.1.val = ((a.1.val + L - ancestorRadius k j) % L +
          (i + ancestorRadius k j)) % L ∧
        x.2.val = ((a.2.val + L - ancestorRadius k j) % L +
          (m + ancestorRadius k j)) % L := by
      constructor
      · calc
          x.1.val = (a.1.val + i) % L := hxy.1
          _ = ((a.1.val + L - ancestorRadius k j) % L +
            (i + ancestorRadius k j)) % L :=
              (periodicCenteredIndex a.1.val L (ancestorRadius k j) i hrL).symm
      · calc
          x.2.val = (a.2.val + m) % L := hxy.2
          _ = ((a.2.val + L - ancestorRadius k j) % L +
            (m + ancestorRadius k j)) % L :=
              (periodicCenteredIndex a.2.val L (ancestorRadius k j) m hrL).symm
    have hqnot : ¬ L ≤ ancestorSide k j := by omega
    simp only [centeredExpansion, hqnot, ↓reduceIte,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i + ancestorRadius k j, Finset.mem_range.mpr hi',
      m + ancestorRadius k j, Finset.mem_range.mpr hm', hxy'⟩

/-- Every centered expansion is contained in the explicit parent square. -/
theorem centeredExpansion_subset_parentFromAnchor (boundary : SquareBoundary)
    (L : ℕ) (k : PositiveSquareScale) (j : ParentOffset) (hL : 0 < L)
    (a : Fin L × Fin L) :
    centeredExpansion boundary L k j a ⊆ parentFromAnchor boundary L k j hL a := by
  classical
  cases boundary with
  | free =>
      intro x hx
      let q := ancestorSide k j
      let r := ancestorRadius k j
      by_cases hq : q > L
      · have hs : squareSide (ancestorScale k j) > L := by
          change squareSide (ancestorScale k j) > L at hq
          exact hq
        simp [parentFromAnchor, kpSquare, hs]
      · have hq' : q ≤ L := Nat.le_of_not_gt hq
        have hx' : a.1.val ≤ x.1.val + r ∧
            x.1.val < a.1.val + squareSide k.val + r ∧
            a.2.val ≤ x.2.val + r ∧
            x.2.val < a.2.val + squareSide k.val + r := by
          simpa [centeredExpansion, q, r] using hx
        have hwidth := ancestorSide_eq k j
        have hleft1 : freeParentCoordinate L q r a.1.val ≤ x.1.val := by
          dsimp [freeParentCoordinate]
          omega
        have hleft2 : freeParentCoordinate L q r a.2.val ≤ x.2.val := by
          dsimp [freeParentCoordinate]
          omega
        have hright1 : x.1.val < freeParentCoordinate L q r a.1.val + q := by
          dsimp [freeParentCoordinate]
          by_cases hc : a.1.val - r ≤ L - q
          · rw [min_eq_left hc]
            have hqeq : q = squareSide k.val + 2 * r := by
              simpa [q, r] using hwidth
            omega
          · rw [min_eq_right (le_of_not_ge hc)]
            have hxlt := x.1.isLt
            omega
        have hright2 : x.2.val < freeParentCoordinate L q r a.2.val + q := by
          dsimp [freeParentCoordinate]
          by_cases hc : a.2.val - r ≤ L - q
          · rw [min_eq_left hc]
            have hqeq : q = squareSide k.val + 2 * r := by
              simpa [q, r] using hwidth
            omega
          · rw [min_eq_right (le_of_not_ge hc)]
            have hxlt := x.2.isLt
            omega
        have hs : squareSide (ancestorScale k j) ≤ L := by
          change squareSide (ancestorScale k j) ≤ L at hq'
          exact hq'
        have hcoords :
            (ancestorAnchor .free L k j hL a).1.val ≤ x.1.val ∧
              x.1.val < (ancestorAnchor .free L k j hL a).1.val +
                squareSide (ancestorScale k j) ∧
              (ancestorAnchor .free L k j hL a).2.val ≤ x.2.val ∧
              x.2.val < (ancestorAnchor .free L k j hL a).2.val +
                squareSide (ancestorScale k j) := by
          simpa [ancestorAnchor, Fin.val_mk, q, r, ancestorSide] using
            (show freeParentCoordinate L q r a.1.val ≤ x.1.val ∧
                x.1.val < freeParentCoordinate L q r a.1.val + q ∧
                freeParentCoordinate L q r a.2.val ≤ x.2.val ∧
                x.2.val < freeParentCoordinate L q r a.2.val + q from
              ⟨hleft1, hright1, hleft2, hright2⟩)
        have htarget := (mem_kpSquare_free_iff L (ancestorScale k j) hs
          (ancestorAnchor .free L k j hL a) x).2 hcoords
        simpa [parentFromAnchor] using htarget
  | periodic =>
      intro x hx
      let q := ancestorSide k j
      let r := ancestorRadius k j
      by_cases hq : q ≥ L
      · have hs : squareSide (ancestorScale k j) ≥ L := by
          change squareSide (ancestorScale k j) ≥ L at hq
          exact hq
        simp [parentFromAnchor, kpSquare, hs]
      · have hx' : ∃ i ∈ Finset.range q, ∃ m ∈ Finset.range q,
            x.1.val = ((a.1.val + L - r) % L + i) % L ∧
            x.2.val = ((a.2.val + L - r) % L + m) % L := by
          simpa [centeredExpansion, q, r, hq] using hx
        rcases hx' with ⟨i, hi, m, hm, hxy⟩
        have hs : squareSide (ancestorScale k j) < L := by
          change ¬ ancestorSide k j ≥ L at hq
          exact Nat.lt_of_not_ge hq
        have hcoords :
            ∃ i ∈ Finset.range (squareSide (ancestorScale k j)),
              ∃ m ∈ Finset.range (squareSide (ancestorScale k j)),
                x.1.val = ((ancestorAnchor .periodic L k j hL a).1.val + i) % L ∧
                x.2.val = ((ancestorAnchor .periodic L k j hL a).2.val + m) % L := by
          simpa [ancestorAnchor, Fin.val_mk, q, r, ancestorSide] using
            (show ∃ i ∈ Finset.range q, ∃ m ∈ Finset.range q,
                x.1.val = ((a.1.val + L - r) % L + i) % L ∧
                x.2.val = ((a.2.val + L - r) % L + m) % L from
              ⟨i, hi, m, hm, hxy⟩)
        have htarget := (mem_kpSquare_periodic_iff L (ancestorScale k j) hs
          (ancestorAnchor .periodic L k j hL a) x).2 hcoords
        simpa [parentFromAnchor] using htarget

/-- The selected parent contains the centered expansion at the selected
lower-corner statement of the source square. -/
theorem centeredExpansion_subset_ancestorParent (boundary : SquareBoundary)
    (L : ℕ) (k : PositiveSquareScale) (j : ParentOffset) (hL : 0 < L)
    (s : Finset (Fin L × Fin L)) :
    centeredExpansion boundary L k j (squareAnchor boundary L k.val hL s) ⊆
      ancestorParent boundary L k j hL s := by
  exact centeredExpansion_subset_parentFromAnchor boundary L k j hL
    (squareAnchor boundary L k.val hL s)

/-- At every positive source scale, its square is contained in the selected
explicit parent in either boundary convention. -/
theorem square_subset_ancestorParent (boundary : SquareBoundary) (L : ℕ)
    (k : PositiveSquareScale) (j : ParentOffset) (hL : 0 < L)
    (s : Finset (Fin L × Fin L)) (hs : s ∈ kpSquares boundary L k.val)
    (hsourceSide : squareSide k.val ≤ L) :
    s ⊆ ancestorParent boundary L k j hL s := by
  have hrepr := kpSquare_eq_of_squareAnchor boundary L k.val hL s hs
  cases boundary with
  | free =>
      calc
        s = kpSquare .free L k.val (squareAnchor .free L k.val hL s) := hrepr.symm
        _ ⊆ centeredExpansion .free L k j (squareAnchor .free L k.val hL s) :=
          kpSquare_free_subset_centeredExpansion L k.val k.property hsourceSide j
            (squareAnchor .free L k.val hL s)
        _ ⊆ ancestorParent .free L k j hL s :=
          centeredExpansion_subset_ancestorParent .free L k j hL s
  | periodic =>
      calc
        s = kpSquare .periodic L k.val (squareAnchor .periodic L k.val hL s) := hrepr.symm
        _ ⊆ centeredExpansion .periodic L k j (squareAnchor .periodic L k.val hL s) :=
          kpSquare_periodic_subset_centeredExpansion L k j
            (squareAnchor .periodic L k.val hL s)
        _ ⊆ ancestorParent .periodic L k j hL s :=
          centeredExpansion_subset_ancestorParent .periodic L k j hL s

end FroehlichSpencer.BKT

end
