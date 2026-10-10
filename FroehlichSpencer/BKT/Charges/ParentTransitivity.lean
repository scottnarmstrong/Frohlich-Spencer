/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.ParentGeometry

/-! # Transitivity of explicit square parents

The lower-corner clamping in the free construction composes across dyadic
ancestors. Periodic lower-corner offsets compose modulo the period while the
parent sides remain strictly below the period. -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- Nested upper clamping commutes with shifting both endpoints by the same
amount. This is the scalar identity behind free-parent transitivity. -/
theorem min_sub_clamp_trans (b U t : ℕ) (htU : 2 * t ≤ U) :
    min (min b U - t) (U - 2 * t) = min (b - t) (U - 2 * t) := by
  by_cases hb : b ≤ U
  · rw [min_eq_left hb]
  · have hUb : U ≤ b := by omega
    rw [min_eq_right hUb]
    have h1 : U - 2 * t ≤ U - t := by omega
    have h2 : U - 2 * t ≤ b - t := by omega
    rw [min_eq_right h1, min_eq_right h2]

/-- The remaining ancestor offset after taking the `i`th parent. -/
def parentOffsetDiff (i j : ParentOffset) (hij : i.val < j.val) :
    ParentOffset := ⟨j.val - i.val, by constructor <;> omega⟩

/-- The scale reached after taking the `i`th parent. -/
def parentScaleShift (k : PositiveSquareScale) (i : ParentOffset) :
    PositiveSquareScale := ⟨k.val + i.val, by omega⟩

private theorem parentScale_same (k : PositiveSquareScale) (i j : ParentOffset)
    (hij : i.val < j.val) :
    ancestorScale (parentScaleShift k i) (parentOffsetDiff i j hij) =
      ancestorScale k j := by
  change k.val + i.val + (j.val - i.val) = k.val + j.val
  omega

/-- The target side obtained by taking an `i` ancestor and then a `j-i`
ancestor is the direct `j` ancestor side. -/
theorem ancestorSide_trans (k : PositiveSquareScale) (i j : ParentOffset)
    (hij : i.val < j.val) :
    ancestorSide (parentScaleShift k i) (parentOffsetDiff i j hij) =
      ancestorSide k j := by
  change squareSide
      (ancestorScale (parentScaleShift k i) (parentOffsetDiff i j hij)) =
    squareSide (ancestorScale k j)
  rw [parentScale_same k i j hij]

/-- The radii of two successive centered enlargements add to the direct
enlargement radius. -/
theorem ancestorRadius_trans (k : PositiveSquareScale) (i j : ParentOffset)
    (hij : i.val < j.val) :
    ancestorRadius k j = ancestorRadius k i +
      ancestorRadius (parentScaleShift k i) (parentOffsetDiff i j hij) := by
  have hside := ancestorSide_trans k i j hij
  have hi := ancestorSide_eq k i
  have hj := ancestorSide_eq k j
  have hd := ancestorSide_eq (parentScaleShift k i) (parentOffsetDiff i j hij)
  have hbase : squareSide (parentScaleShift k i).val = ancestorSide k i := by
    change 2 ^ (k.val + i.val) = 2 ^ (k.val + i.val)
    rfl
  omega

private theorem freeParentCoordinate_trans (L : ℕ) (k : PositiveSquareScale)
    (i j : ParentOffset) (hij : i.val < j.val) (hLi : ancestorSide k i ≤ L)
    (hLj : ancestorSide k j ≤ L) (a : ℕ) :
    freeParentCoordinate L (ancestorSide (parentScaleShift k i)
      (parentOffsetDiff i j hij))
      (ancestorRadius (parentScaleShift k i) (parentOffsetDiff i j hij))
      (freeParentCoordinate L (ancestorSide k i) (ancestorRadius k i) a) =
    freeParentCoordinate L (ancestorSide k j) (ancestorRadius k j) a := by
  have hside := ancestorSide_trans k i j hij
  have hrad := ancestorRadius_trans k i j hij
  have hq : ancestorSide k j = ancestorSide k i +
      2 * ancestorRadius (parentScaleShift k i) (parentOffsetDiff i j hij) := by
    rw [← hside, ancestorSide_eq]
    have hb : squareSide (parentScaleShift k i).val = ancestorSide k i := by
      change 2 ^ (k.val + i.val) = 2 ^ (k.val + i.val)
      rfl
    rw [hb]
  have hU : L - ancestorSide k j =
      (L - ancestorSide k i) -
        2 * ancestorRadius (parentScaleShift k i) (parentOffsetDiff i j hij) := by
    omega
  have htU : 2 * ancestorRadius (parentScaleShift k i)
      (parentOffsetDiff i j hij) ≤ L - ancestorSide k i := by
    omega
  have hsub : a - (ancestorRadius k i +
      ancestorRadius (parentScaleShift k i) (parentOffsetDiff i j hij)) =
      a - ancestorRadius k i -
        ancestorRadius (parentScaleShift k i) (parentOffsetDiff i j hij) := by
    omega
  unfold freeParentCoordinate
  rw [hside, hrad, hU, hsub]
  exact min_sub_clamp_trans (a - ancestorRadius k i)
    (L - ancestorSide k i)
    (ancestorRadius (parentScaleShift k i) (parentOffsetDiff i j hij)) htU

/-- The explicitly clamped free lower-corner statement composes for all
intermediate parents whose sides fit in the domain. -/
theorem ancestorAnchor_free_trans (L : ℕ) (k : PositiveSquareScale)
    (i j : ParentOffset) (hij : i.val < j.val) (hL : 0 < L)
    (hLi : ancestorSide k i ≤ L) (hLj : ancestorSide k j ≤ L)
    (a : Fin L × Fin L) :
    ancestorAnchor .free L (parentScaleShift k i) (parentOffsetDiff i j hij) hL
      (ancestorAnchor .free L k i hL a) =
    ancestorAnchor .free L k j hL a := by
  apply Prod.ext
  · apply Fin.ext
    change freeParentCoordinate L
        (ancestorSide (parentScaleShift k i) (parentOffsetDiff i j hij))
        (ancestorRadius (parentScaleShift k i) (parentOffsetDiff i j hij))
        (freeParentCoordinate L (ancestorSide k i) (ancestorRadius k i) a.1.val) =
      freeParentCoordinate L (ancestorSide k j) (ancestorRadius k j) a.1.val
    exact freeParentCoordinate_trans L k i j hij hLi hLj a.1.val
  · apply Fin.ext
    change freeParentCoordinate L
        (ancestorSide (parentScaleShift k i) (parentOffsetDiff i j hij))
        (ancestorRadius (parentScaleShift k i) (parentOffsetDiff i j hij))
        (freeParentCoordinate L (ancestorSide k i) (ancestorRadius k i) a.2.val) =
      freeParentCoordinate L (ancestorSide k j) (ancestorRadius k j) a.2.val
    exact freeParentCoordinate_trans L k i j hij hLi hLj a.2.val

/-- The corresponding free parent squares are equal. -/
theorem parentFromAnchor_free_trans (L : ℕ) (k : PositiveSquareScale)
    (i j : ParentOffset) (hij : i.val < j.val) (hL : 0 < L)
    (hLi : ancestorSide k i ≤ L) (hLj : ancestorSide k j ≤ L)
    (a : Fin L × Fin L) :
    parentFromAnchor .free L (parentScaleShift k i) (parentOffsetDiff i j hij) hL
      (ancestorAnchor .free L k i hL a) = parentFromAnchor .free L k j hL a := by
  simp only [parentFromAnchor, parentScale_same k i j hij,
    ancestorAnchor_free_trans L k i j hij hL hLi hLj a]

/-- Free parent squares compose without a fit hypothesis: before side `L` this
is the clamping identity above, and after side `L` both parents are universal. -/
theorem parentFromAnchor_free_trans_total (L : ℕ) (k : PositiveSquareScale)
    (i j : ParentOffset) (hij : i.val < j.val) (hL : 0 < L)
    (a : Fin L × Fin L) :
    parentFromAnchor .free L (parentScaleShift k i) (parentOffsetDiff i j hij) hL
      (ancestorAnchor .free L k i hL a) = parentFromAnchor .free L k j hL a := by
  have hside := ancestorSide_trans k i j hij
  by_cases hj : ancestorSide k j ≤ L
  · have hbase : squareSide (parentScaleShift k i).val = ancestorSide k i := by
      change 2 ^ (k.val + i.val) = 2 ^ (k.val + i.val)
      rfl
    have hq : ancestorSide k j = ancestorSide k i +
        2 * ancestorRadius (parentScaleShift k i) (parentOffsetDiff i j hij) := by
      rw [← hside, ancestorSide_eq, hbase]
    have hi : ancestorSide k i ≤ L := by omega
    exact parentFromAnchor_free_trans L k i j hij hL hi hj a
  · have hj' : squareSide (ancestorScale k j) > L := by
      change ancestorSide k j > L
      omega
    have hmid' : squareSide
        (ancestorScale (parentScaleShift k i) (parentOffsetDiff i j hij)) > L := by
      change ancestorSide (parentScaleShift k i) (parentOffsetDiff i j hij) > L
      rw [hside]
      omega
    simp [parentFromAnchor, kpSquare, hj', hmid']

/-- A quotient translation followed by a further backward offset is the
direct quotient translation, provided the combined parent side is still
strictly below the period. -/
private theorem periodic_mod_shift (x L t : ℕ) (htL : t < L)
    (htx : t ≤ x) :
    (x % L + L - t) % L = (x - t) % L := by
  have hsum : x % L + L ≡ x + L [MOD L] :=
    (Nat.mod_modEq x L).add_right L
  have hsub : x % L + L - t ≡ x + L - t [MOD L] :=
    Nat.ModEq.sub (by omega) (by omega) hsum Nat.ModEq.rfl
  have hshift : x + L - t ≡ x - t [MOD L] := by
    change (x + L - t) % L = (x - t) % L
    rw [show x + L - t = x - t + L by omega]
    simp
  change (x % L + L - t) % L = (x - t) % L
  exact hsub.trans hshift

private theorem periodicParentCoordinate_trans (L : ℕ) (k : PositiveSquareScale)
    (i j : ParentOffset) (hij : i.val < j.val)
    (hLj : ancestorSide k j < L) (a : Fin L) :
    (((((a.val + L - ancestorRadius k i) % L) + L -
        ancestorRadius (parentScaleShift k i) (parentOffsetDiff i j hij)) % L)) =
      (a.val + L - ancestorRadius k j) % L := by
  let t := ancestorRadius (parentScaleShift k i) (parentOffsetDiff i j hij)
  let ri := ancestorRadius k i
  let rj := ancestorRadius k j
  have hrad := ancestorRadius_trans k i j hij
  have hsumRadius : rj = ri + t := by exact hrad
  have hside := ancestorSide_eq k j
  have hrjL : rj < L := by dsimp [rj] at *; omega
  have htL : t < L := by dsimp [t]; omega
  have htx : t ≤ a.val + L - ri := by dsimp [t, ri]; omega
  have hsub : a.val + L - ri - t = a.val + L - rj := by omega
  calc
    (((a.val + L - ri) % L) + L - t) % L =
        (a.val + L - ri - t) % L :=
      periodic_mod_shift (a.val + L - ri) L t htL htx
    _ = (a.val + L - rj) % L := by rw [hsub]

/-- The periodic lower-corner statement composes modulo `L` while all target
parents involved still have side strictly smaller than `L`. -/
theorem ancestorAnchor_periodic_trans (L : ℕ) (k : PositiveSquareScale)
    (i j : ParentOffset) (hij : i.val < j.val) (hL : 0 < L)
    (hLj : ancestorSide k j < L) (a : Fin L × Fin L) :
    ancestorAnchor .periodic L (parentScaleShift k i) (parentOffsetDiff i j hij) hL
      (ancestorAnchor .periodic L k i hL a) =
    ancestorAnchor .periodic L k j hL a := by
  apply Prod.ext
  · apply Fin.ext
    change (((a.1.val + L - ancestorRadius k i) % L) + L -
        ancestorRadius (parentScaleShift k i) (parentOffsetDiff i j hij)) % L =
      (a.1.val + L - ancestorRadius k j) % L
    exact periodicParentCoordinate_trans L k i j hij hLj a.1
  · apply Fin.ext
    change (((a.2.val + L - ancestorRadius k i) % L) + L -
        ancestorRadius (parentScaleShift k i) (parentOffsetDiff i j hij)) % L =
      (a.2.val + L - ancestorRadius k j) % L
    exact periodicParentCoordinate_trans L k i j hij hLj a.2

/-- Periodic parent squares compose as quotient boxes below the period and
coincide with the universal parent once the direct side reaches the period. -/
theorem parentFromAnchor_periodic_trans (L : ℕ) (k : PositiveSquareScale)
    (i j : ParentOffset) (hij : i.val < j.val) (hL : 0 < L)
    (a : Fin L × Fin L) :
    parentFromAnchor .periodic L (parentScaleShift k i) (parentOffsetDiff i j hij) hL
      (ancestorAnchor .periodic L k i hL a) = parentFromAnchor .periodic L k j hL a := by
  have hside := ancestorSide_trans k i j hij
  by_cases hj : ancestorSide k j < L
  · simp only [parentFromAnchor, parentScale_same k i j hij,
      ancestorAnchor_periodic_trans L k i j hij hL hj a]
  · have hj' : L ≤ ancestorSide k j := by omega
    have hmid : L ≤ ancestorSide (parentScaleShift k i) (parentOffsetDiff i j hij) := by
      rw [hside]
      exact hj'
    have htarget : squareSide (ancestorScale k j) ≥ L := by
      exact hj'
    have hmid' : squareSide
        (ancestorScale (parentScaleShift k i) (parentOffsetDiff i j hij)) ≥ L := by
      exact hmid
    simp [parentFromAnchor, kpSquare, htarget, hmid']

end FroehlichSpencer.BKT

end
