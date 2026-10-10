/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.SquareZero
public import Mathlib.Data.Fin.Rev

/-!
# Square symmetries of the wired square

The coordinate actions and boundary-depth bookkeeping used to reduce KP's wired-square
observable to the right side of the box (KP pp. 2, 4;
-/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- Reflect the first coordinate and leave the wired vertex fixed. -/
def wiredSquareReflection (L : ℕ) :
    Equiv (Option (Fin L × Fin L)) (Option (Fin L × Fin L)) where
  toFun
    | none => none
    | some x => some (x.1.rev, x.2)
  invFun
    | none => none
    | some x => some (x.1.rev, x.2)
  left_inv := by
    intro j
    cases j with
    | none => rfl
    | some x => simp
  right_inv := by
    intro j
    cases j with
    | none => rfl
    | some x => simp

/-- Swap the coordinates and leave the wired vertex fixed. -/
def wiredSquareSwap (L : ℕ) :
    Equiv (Option (Fin L × Fin L)) (Option (Fin L × Fin L)) where
  toFun
    | none => none
    | some x => some (x.2, x.1)
  invFun
    | none => none
    | some x => some (x.2, x.1)
  left_inv := by
    intro j
    cases j <;> simp
  right_inv := by
    intro j
    cases j <;> simp

/-- The graph distance from a free square vertex to its nearest side, before adjoining the
single edge to the wired root. -/
def wiredBoundaryDepth (L : ℕ) (x : Fin L × Fin L) : ℕ :=
  min (min x.1.val x.2.val)
    (min (L - 1 - x.1.val) (L - 1 - x.2.val))

/-- A free vertex is on the right-side nearest-point class when its distance to the wired root
is `L - x.1`; the `+1` in the equivalent boundary-depth formula is essential. -/
def wiredRightSide (L : ℕ) (x : Fin L × Fin L) : Prop :=
  L - x.1.val = wiredBoundaryDepth L x + 1

@[simp]
theorem wiredSquareReflection_none (L : ℕ) : wiredSquareReflection L none = none := rfl

@[simp]
theorem wiredSquareReflection_some (L : ℕ) (x : Fin L × Fin L) :
    wiredSquareReflection L (some x) = some (x.1.rev, x.2) := rfl

@[simp]
theorem wiredSquareSwap_none (L : ℕ) : wiredSquareSwap L none = none := rfl

@[simp]
theorem wiredSquareSwap_some (L : ℕ) (x : Fin L × Fin L) :
    wiredSquareSwap L (some x) = some (x.2, x.1) := rfl

theorem wiredBoundaryDepth_reflection (L : ℕ) (x : Fin L × Fin L) :
    wiredBoundaryDepth L (x.1.rev, x.2) = wiredBoundaryDepth L x := by
  simp only [wiredBoundaryDepth, Fin.val_rev]
  have hx : x.1.val < L := x.1.isLt
  omega

theorem wiredBoundaryDepth_swap (L : ℕ) (x : Fin L × Fin L) :
    wiredBoundaryDepth L (x.2, x.1) = wiredBoundaryDepth L x := by
  simp only [wiredBoundaryDepth]
  simp only [Nat.min_comm (x.1.val) (x.2.val), Nat.min_comm (L - 1 - x.1.val)
    (L - 1 - x.2.val), Nat.min_left_comm, Nat.min_assoc]

/-- The minimum of four natural numbers is one of them, in nested-`min` form. -/
private theorem min_min_attained (a b c d : ℕ) :
    min (min a b) (min c d) = a ∨ min (min a b) (min c d) = b ∨
      min (min a b) (min c d) = c ∨ min (min a b) (min c d) = d := by
  have hab : min a b = a ∨ min a b = b := by
    rcases le_total a b with h | h
    · exact Or.inl (min_eq_left h)
    · exact Or.inr (min_eq_right h)
  have hcd : min c d = c ∨ min c d = d := by
    rcases le_total c d with h | h
    · exact Or.inl (min_eq_left h)
    · exact Or.inr (min_eq_right h)
  have hout : min (min a b) (min c d) = min a b ∨
      min (min a b) (min c d) = min c d := by
    rcases le_total (min a b) (min c d) with h | h
    · exact Or.inl (min_eq_left h)
    · exact Or.inr (min_eq_right h)
  rcases hout with hout | hout
  · rcases hab with hab | hab
    · exact Or.inl (hout.trans hab)
    · exact Or.inr (Or.inl (hout.trans hab))
  · rcases hcd with hcd | hcd
    · exact Or.inr (Or.inr (Or.inl (hout.trans hcd)))
    · exact Or.inr (Or.inr (Or.inr (hout.trans hcd)))

/-- The nearest boundary depth is attained by one of the four coordinate sides. -/
theorem wiredBoundaryDepth_eq_one_side (L : ℕ) (x : Fin L × Fin L) :
    wiredBoundaryDepth L x = x.1.val ∨
    wiredBoundaryDepth L x = x.2.val ∨
    wiredBoundaryDepth L x = L - 1 - x.1.val ∨
    wiredBoundaryDepth L x = L - 1 - x.2.val := by
  exact min_min_attained x.1.val x.2.val
    (L - 1 - x.1.val) (L - 1 - x.2.val)

/-- Every free vertex can be sent to the right-side nearest-point class by a coordinate swap,
the first-coordinate reflection, or their composition. -/
theorem exists_wiredRightSide_representative (L : ℕ) (x : Fin L × Fin L)
    :
    wiredRightSide L x ∨
      wiredRightSide L (x.1.rev, x.2) ∨
      wiredRightSide L (x.2, x.1) ∨
      wiredRightSide L (x.2.rev, x.1) := by
  rcases wiredBoundaryDepth_eq_one_side L x with h | h | h | h
  · right; left
    change L - (x.1.rev).val = wiredBoundaryDepth L (x.1.rev, x.2) + 1
    rw [wiredBoundaryDepth_reflection L x]
    rw [Fin.val_rev]
    omega
  · right; right; right
    change L - (x.2.rev).val = wiredBoundaryDepth L (x.2.rev, x.1) + 1
    rw [wiredBoundaryDepth_reflection L (x.2, x.1), wiredBoundaryDepth_swap L x]
    rw [Fin.val_rev]
    omega
  · left
    change L - x.1.val = wiredBoundaryDepth L x + 1
    omega
  · right; right; left
    change L - x.2.val = wiredBoundaryDepth L (x.2, x.1) + 1
    rw [wiredBoundaryDepth_swap]
    omega

end FroehlichSpencer.BKT

end
