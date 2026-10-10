/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.FreeBox

/-!
# Divergence-free free-box currents and zero-exterior face heights

The current on an oriented spin bond is the height on its source face minus the height on its
target face.  The exterior face is included and pinned to zero.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Rotator

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Duality
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Villain

variable {L : ℕ}

/-- The current on a horizontal spin bond indexed by its lower endpoint. -/
def rotatorHorizontalCurrent (q : RotatorInternalBond L → ℤ)
    (i : Fin L) (j : Fin (L + 1)) : ℤ :=
  q (.inl (horizontalDualEdgeData i j))

/-- The current on a vertical spin bond indexed by its lower endpoint. -/
def rotatorVerticalCurrent (q : RotatorInternalBond L → ℤ)
    (i : Fin (L + 1)) (j : Fin L) : ℤ :=
  q (.inr (verticalDualEdgeData i j))

private theorem sum_if_unique_index {α M : Type*} [Fintype α] [DecidableEq α]
    [AddCommMonoid M] (P : α → Prop) [DecidablePred P] (a : α) (ha : P a)
    (hunique : ∀ b, P b → b = a) (f : α → M) :
    (∑ b, if P b then f b else 0) = f a := by
  classical
  rw [Fintype.sum_eq_single a]
  · simp [ha]
  · intro b hba
    by_cases hb : P b
    · exact (hba (hunique b hb)).elim
    · simp [hb]

private theorem rotatorHorizontalSourceSum (q : RotatorInternalBond L → ℤ)
    (x y : Fin (L + 1)) (hx : x.val < L) :
    (∑ e : SquareFreeHorizontalEdge (L + 1),
      if (rotatorFreeGraph L).src (.inl e) = (x,y) then q (.inl e) else 0) =
      rotatorHorizontalCurrent q ⟨x.val,hx⟩ y := by
  classical
  apply sum_if_unique_index
    (fun e : SquareFreeHorizontalEdge (L + 1) =>
      (rotatorFreeGraph L).src (.inl e) = (x,y))
    (horizontalDualEdgeData ⟨x.val,hx⟩ y)
  · simp [rotatorFreeGraph, squareFreeGraph, horizontalDualEdgeData]
  · intro e he
    rcases e with ⟨⟨i, hi⟩, y'⟩
    simp only [rotatorFreeGraph, squareFreeGraph, Prod.mk.injEq] at he
    rcases he with ⟨hix, hiy⟩
    subst y'
    apply Prod.ext
    · apply Subtype.ext
      apply Fin.ext
      have hv := congrArg Fin.val hix
      simpa [horizontalDualEdgeData, Fin.val_castLE] using hv
    · rfl

private theorem rotatorHorizontalSourceSum_absent (q : RotatorInternalBond L → ℤ)
    (x y : Fin (L + 1)) (hx : ¬ x.val < L) :
    (∑ e : SquareFreeHorizontalEdge (L + 1),
      if (rotatorFreeGraph L).src (.inl e) = (x,y) then q (.inl e) else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro e he
  change (if (rotatorFreeGraph L).src (.inl e) = (x,y) then q (.inl e) else 0) = 0
  split_ifs with hs
  · rcases e with ⟨⟨i, hi⟩, y'⟩
    simp only [rotatorFreeGraph, squareFreeGraph, Prod.mk.injEq] at hs
    have hv := congrArg Fin.val hs.1
    have hi' := i.isLt
    omega
  · rfl

private theorem rotatorHorizontalTargetSum (q : RotatorInternalBond L → ℤ)
    (x y : Fin (L + 1)) (hx : 0 < x.val) :
    (∑ e : SquareFreeHorizontalEdge (L + 1),
      if (rotatorFreeGraph L).tgt (.inl e) = (x,y) then q (.inl e) else 0) =
      rotatorHorizontalCurrent q ⟨x.val - 1, by have _h := x.isLt; omega⟩ y := by
  classical
  apply sum_if_unique_index
    (fun e : SquareFreeHorizontalEdge (L + 1) =>
      (rotatorFreeGraph L).tgt (.inl e) = (x,y))
    (horizontalDualEdgeData ⟨x.val - 1, by have h := x.isLt; omega⟩ y)
  · simp only [rotatorFreeGraph, squareFreeGraph, Prod.mk.injEq]
    constructor
    · apply Fin.ext
      simp [horizontalDualEdgeData]
      omega
    · rfl
  · intro e he
    rcases e with ⟨⟨i, hi⟩, y'⟩
    simp only [rotatorFreeGraph, squareFreeGraph, Prod.mk.injEq] at he
    rcases he with ⟨hix, hiy⟩
    subst y'
    apply Prod.ext
    · apply Subtype.ext
      apply Fin.ext
      have hv := congrArg Fin.val hix
      simp [horizontalDualEdgeData] at hv ⊢
      omega
    · rfl

private theorem rotatorHorizontalTargetSum_absent (q : RotatorInternalBond L → ℤ)
    (x y : Fin (L + 1)) (hx : ¬ 0 < x.val) :
    (∑ e : SquareFreeHorizontalEdge (L + 1),
      if (rotatorFreeGraph L).tgt (.inl e) = (x,y) then q (.inl e) else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro e he
  change (if (rotatorFreeGraph L).tgt (.inl e) = (x,y) then q (.inl e) else 0) = 0
  split_ifs with hs
  · rcases e with ⟨⟨i, hi⟩, y'⟩
    simp only [rotatorFreeGraph, squareFreeGraph, Prod.mk.injEq] at hs
    have hv : i.val + 1 = x.val := by simpa using congrArg Fin.val hs.1
    have hix := i.isLt
    have hxzero : x.val = 0 := Nat.eq_zero_of_not_pos hx
    rw [hxzero] at hv
    omega
  · rfl

private theorem rotatorVerticalSourceSum (q : RotatorInternalBond L → ℤ)
    (x y : Fin (L + 1)) (hy : y.val < L) :
    (∑ e : SquareFreeVerticalEdge (L + 1),
      if (rotatorFreeGraph L).src (.inr e) = (x,y) then q (.inr e) else 0) =
      rotatorVerticalCurrent q x ⟨y.val,hy⟩ := by
  classical
  apply sum_if_unique_index
    (fun e : SquareFreeVerticalEdge (L + 1) =>
      (rotatorFreeGraph L).src (.inr e) = (x,y))
    (verticalDualEdgeData x ⟨y.val,hy⟩)
  · simp only [rotatorFreeGraph, squareFreeGraph, Prod.mk.injEq]
    constructor
    · rfl
    · apply Fin.ext
      simp [verticalDualEdgeData]
  · intro e he
    rcases e with ⟨x', ⟨j, hj⟩⟩
    simp only [rotatorFreeGraph, squareFreeGraph, Prod.mk.injEq] at he
    rcases he with ⟨hix, hjy⟩
    subst x'
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Fin.ext
      have hv := congrArg Fin.val hjy
      simp [verticalDualEdgeData] at hv ⊢
      exact hv

private theorem rotatorVerticalSourceSum_absent (q : RotatorInternalBond L → ℤ)
    (x y : Fin (L + 1)) (hy : ¬ y.val < L) :
    (∑ e : SquareFreeVerticalEdge (L + 1),
      if (rotatorFreeGraph L).src (.inr e) = (x,y) then q (.inr e) else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro e he
  change (if (rotatorFreeGraph L).src (.inr e) = (x,y) then q (.inr e) else 0) = 0
  split_ifs with hs
  · rcases e with ⟨x', ⟨j, hj⟩⟩
    simp only [rotatorFreeGraph, squareFreeGraph, Prod.mk.injEq] at hs
    have hv : j.val = y.val := by simpa using congrArg Fin.val hs.2
    have hybound := j.isLt
    have hyge : L ≤ y.val := Nat.le_of_not_gt hy
    omega
  · rfl

private theorem rotatorVerticalTargetSum (q : RotatorInternalBond L → ℤ)
    (x y : Fin (L + 1)) (hy : 0 < y.val) :
    (∑ e : SquareFreeVerticalEdge (L + 1),
      if (rotatorFreeGraph L).tgt (.inr e) = (x,y) then q (.inr e) else 0) =
      rotatorVerticalCurrent q x ⟨y.val - 1, by have _h := y.isLt; omega⟩ := by
  classical
  apply sum_if_unique_index
    (fun e : SquareFreeVerticalEdge (L + 1) =>
      (rotatorFreeGraph L).tgt (.inr e) = (x,y))
    (verticalDualEdgeData x ⟨y.val - 1, by have h := y.isLt; omega⟩)
  · simp only [rotatorFreeGraph, squareFreeGraph, Prod.mk.injEq]
    constructor
    · rfl
    · apply Fin.ext
      simp [verticalDualEdgeData]
      omega
  · intro e he
    rcases e with ⟨x', ⟨j, hj⟩⟩
    simp only [rotatorFreeGraph, squareFreeGraph, Prod.mk.injEq] at he
    rcases he with ⟨hix, hjy⟩
    subst x'
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Fin.ext
      have hv := congrArg Fin.val hjy
      simp [verticalDualEdgeData] at hv ⊢
      omega

private theorem rotatorVerticalTargetSum_absent (q : RotatorInternalBond L → ℤ)
    (x y : Fin (L + 1)) (hy : ¬ 0 < y.val) :
    (∑ e : SquareFreeVerticalEdge (L + 1),
      if (rotatorFreeGraph L).tgt (.inr e) = (x,y) then q (.inr e) else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro e he
  change (if (rotatorFreeGraph L).tgt (.inr e) = (x,y) then q (.inr e) else 0) = 0
  split_ifs with hs
  · rcases e with ⟨x', ⟨j, hj⟩⟩
    simp only [rotatorFreeGraph, squareFreeGraph, Prod.mk.injEq] at hs
    have hv : j.val + 1 = y.val := by simpa using congrArg Fin.val hs.2
    have hyzero : y.val = 0 := Nat.eq_zero_of_not_pos hy
    rw [hyzero] at hv
    omega
  · rfl

/-- Coordinate form of the free-box divergence.  Missing boundary bonds are zero. -/
theorem rotatorCurrentDivergence_formula (q : RotatorInternalBond L → ℤ)
    (x y : Fin (L + 1)) :
    rotatorCurrentDivergence q (x,y) =
      (if hx : x.val < L then rotatorHorizontalCurrent q ⟨x.val,hx⟩ y else 0) +
      (if hy : y.val < L then rotatorVerticalCurrent q x ⟨y.val,hy⟩ else 0) -
      (if hx : 0 < x.val then
        rotatorHorizontalCurrent q ⟨x.val - 1, by have _h := x.isLt; omega⟩ y else 0) -
      (if hy : 0 < y.val then
        rotatorVerticalCurrent q x ⟨y.val - 1, by have _h := y.isLt; omega⟩ else 0) := by
  classical
  unfold rotatorCurrentDivergence currentDivergence rotatorFreeGraph
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  rw [show (∑ e : SquareFreeHorizontalEdge (L + 1),
      if (squareFreeGraph (L + 1)).src (.inl e) = (x,y) then q (.inl e) else 0) =
        if hx : x.val < L then rotatorHorizontalCurrent q ⟨x.val,hx⟩ y else 0 by
      by_cases hx : x.val < L
      · simp only [dite_eq_left hx]
        exact rotatorHorizontalSourceSum q x y hx
      · simp only [dite_eq_right hx]
        exact rotatorHorizontalSourceSum_absent q x y hx]
  rw [show (∑ e : SquareFreeVerticalEdge (L + 1),
      if (squareFreeGraph (L + 1)).src (.inr e) = (x,y) then q (.inr e) else 0) =
        if hy : y.val < L then rotatorVerticalCurrent q x ⟨y.val,hy⟩ else 0 by
      by_cases hy : y.val < L
      · simp only [dite_eq_left hy]
        exact rotatorVerticalSourceSum q x y hy
      · simp only [dite_eq_right hy]
        exact rotatorVerticalSourceSum_absent q x y hy]
  rw [show (∑ e : SquareFreeHorizontalEdge (L + 1),
      if (squareFreeGraph (L + 1)).tgt (.inl e) = (x,y) then q (.inl e) else 0) =
        if hx : 0 < x.val then
          rotatorHorizontalCurrent q ⟨x.val - 1, by have _h := x.isLt; omega⟩ y else 0 by
      by_cases hx : 0 < x.val
      · simp only [dite_eq_left hx]
        exact rotatorHorizontalTargetSum q x y hx
      · simp only [dite_eq_right hx]
        exact rotatorHorizontalTargetSum_absent q x y hx]
  rw [show (∑ e : SquareFreeVerticalEdge (L + 1),
      if (squareFreeGraph (L + 1)).tgt (.inr e) = (x,y) then q (.inr e) else 0) =
        if hy : 0 < y.val then
          rotatorVerticalCurrent q x ⟨y.val - 1, by have _h := y.isLt; omega⟩ else 0 by
      by_cases hy : 0 < y.val
      · simp only [dite_eq_left hy]
        exact rotatorVerticalTargetSum q x y hy
      · simp only [dite_eq_right hy]
        exact rotatorVerticalTargetSum_absent q x y hy]
  ring

/-- Horizontal current extended by zero beyond the left-face range. -/
def rotatorHorizontalCurrentNat (q : RotatorInternalBond L → ℤ)
    (i : Fin L) (k : ℕ) : ℤ :=
  if hk : k < L then rotatorHorizontalCurrent q i ⟨k, by omega⟩ else 0

/-- A path-sum height on bounded faces, obtained by summing horizontal currents up from the
bottom exterior face. -/
def rotatorHeightPotential (q : RotatorInternalBond L → ℤ)
    (i j : Fin L) : ℤ :=
  ∑ k ∈ Finset.range (j.val + 1), rotatorHorizontalCurrentNat q i k

/-- The zero-exterior height reconstructed from a current. -/
def rotatorHeightFromCurrent (q : RotatorInternalBond L → ℤ) : RotatorFaceHeight L :=
  ⟨fun f => match f with
    | none => 0
    | some p => rotatorHeightPotential q p.1 p.2, rfl⟩

/-- The last horizontal current is the last summand in the path-sum height. -/
theorem rotatorHeightPotential_eq_sum_range_succ (q : RotatorInternalBond L → ℤ)
    (i j : Fin L) :
    rotatorHeightPotential q i j =
      (∑ k ∈ Finset.range j.val,
        rotatorHorizontalCurrentNat q i k) +
        rotatorHorizontalCurrentNat q i j := by
  unfold rotatorHeightPotential
  rw [show j.val + 1 = Nat.succ j.val by omega, Finset.sum_range_succ]

private theorem sum_range_pred_sub {α : Type*} [AddCommGroup α]
    (f : ℕ → α) (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range n, f k) -
        (∑ k ∈ Finset.range (n - 1), f k) = f (n - 1) := by
  have hsum : (∑ k ∈ Finset.range n, f k) =
      (∑ k ∈ Finset.range (n - 1), f k) + f (n - 1) := by
    rw [← Nat.sub_add_cancel hn, Finset.sum_range_succ]
    congr 1
  rw [hsum]
  abel

/-- An interior horizontal current is the vertical difference of its adjacent reconstructed face
heights. -/
theorem rotatorHeightPotential_horizontal_step (q : RotatorInternalBond L → ℤ)
    (i j : Fin L) (hj : 0 < j.val) :
    rotatorHeightPotential q i j -
        rotatorHeightPotential q i ⟨j.val - 1, by have _h := j.isLt; omega⟩ =
      rotatorHorizontalCurrent q i ⟨j.val, by omega⟩ := by
  have hsum := rotatorHeightPotential_eq_sum_range_succ q i j
  let jprev : Fin L := ⟨j.val - 1, by have _h := j.isLt; omega⟩
  have hprev := rotatorHeightPotential_eq_sum_range_succ q i jprev
  have hprev' : rotatorHeightPotential q i jprev =
      (∑ k ∈ Finset.range (j.val - 1), rotatorHorizontalCurrentNat q i k) +
        rotatorHorizontalCurrentNat q i (j.val - 1) := by
    simpa only [jprev, Fin.val_mk] using hprev
  have hlast : rotatorHorizontalCurrentNat q i j.val =
      rotatorHorizontalCurrent q i ⟨j.val, by omega⟩ := by
    simp [rotatorHorizontalCurrentNat, j.isLt]
  have hsumrange := sum_range_pred_sub
    (fun k => rotatorHorizontalCurrentNat q i k) j.val hj
  rw [hsum, hprev']
  calc
    (∑ k ∈ Finset.range j.val, rotatorHorizontalCurrentNat q i k) +
        rotatorHorizontalCurrentNat q i j.val -
        ((∑ k ∈ Finset.range (j.val - 1), rotatorHorizontalCurrentNat q i k) +
          rotatorHorizontalCurrentNat q i (j.val - 1)) =
        rotatorHorizontalCurrentNat q i j.val := by
          calc
            _ = ((∑ k ∈ Finset.range j.val, rotatorHorizontalCurrentNat q i k) -
                ∑ k ∈ Finset.range (j.val - 1), rotatorHorizontalCurrentNat q i k) +
                (rotatorHorizontalCurrentNat q i j.val -
                  rotatorHorizontalCurrentNat q i (j.val - 1)) := by abel
            _ = rotatorHorizontalCurrentNat q i j.val := by
              rw [hsumrange]
              abel
    _ = rotatorHorizontalCurrent q i ⟨j.val, by omega⟩ := hlast

def rotatorLeftHeight (q : RotatorInternalBond L → ℤ) (x : Fin (L + 1))
    (j : Fin L) : ℤ :=
  if hx : 0 < x.val then
    rotatorHeightPotential q ⟨x.val - 1, by have _h := x.isLt; omega⟩ j
  else 0

def rotatorRightHeight (q : RotatorInternalBond L → ℤ) (x : Fin (L + 1))
    (j : Fin L) : ℤ :=
  if hx : x.val < L then rotatorHeightPotential q ⟨x.val, hx⟩ j else 0

private theorem rotatorHorizontalOutgoing_height (q : RotatorInternalBond L → ℤ)
    (x : Fin (L + 1)) (y : Fin L) :
    (if hx : x.val < L then
      rotatorHorizontalCurrent q ⟨x.val,hx⟩ ⟨y.val, by omega⟩ else 0) =
      rotatorRightHeight q x y -
        (if hy : 0 < y.val then
          rotatorRightHeight q x ⟨y.val - 1, by omega⟩ else 0) := by
  by_cases hx : x.val < L
  · simp only [dite_eq_left hx]
    by_cases hy : 0 < y.val
    · simp only [dite_eq_left hy, rotatorRightHeight, dite_eq_left hx]
      exact (rotatorHeightPotential_horizontal_step q ⟨x.val,hx⟩ y hy).symm
    · have hy0 : y.val = 0 := by omega
      have hLpos : 0 < L := by omega
      have hyEq : y = (⟨0, hLpos⟩ : Fin L) := Fin.ext (by simpa using hy0)
      rw [hyEq]
      simp [rotatorRightHeight, hx, hLpos, rotatorHeightPotential, rotatorHorizontalCurrentNat,
        rotatorHorizontalCurrent]
  · simp only [dite_eq_right hx]
    simp [rotatorRightHeight, hx]

private theorem rotatorHorizontalIncoming_height (q : RotatorInternalBond L → ℤ)
    (x : Fin (L + 1)) (y : Fin L) :
    (if hx : 0 < x.val then
      rotatorHorizontalCurrent q ⟨x.val - 1, by have _h := x.isLt; omega⟩
        ⟨y.val, by omega⟩ else 0) =
      rotatorLeftHeight q x y -
        (if hy : 0 < y.val then
          rotatorLeftHeight q x ⟨y.val - 1, by omega⟩ else 0) := by
  by_cases hx : 0 < x.val
  · simp only [dite_eq_left hx]
    by_cases hy : 0 < y.val
    · simp only [dite_eq_left hy, rotatorLeftHeight, dite_eq_left hx]
      exact (rotatorHeightPotential_horizontal_step q
        ⟨x.val - 1, by have _h := x.isLt; omega⟩ y hy).symm
    · have hy0 : y.val = 0 := by omega
      have hLpos : 0 < L := by omega
      have hyEq : y = (⟨0, hLpos⟩ : Fin L) := Fin.ext (by simpa using hy0)
      rw [hyEq]
      simp [rotatorLeftHeight, hx, hLpos, rotatorHeightPotential, rotatorHorizontalCurrentNat,
        rotatorHorizontalCurrent]
  · simp only [dite_eq_right hx]
    simp [rotatorLeftHeight, hx]

/- The following recurrence reconstructs vertical edges from the path sum. -/
private theorem rotatorVerticalPathStep (q : RotatorInternalBond L → ℤ)
    (hq : ∀ v, rotatorCurrentDivergence q v = 0) (x : Fin (L + 1)) :
    ∀ n (hn : n < L),
      rotatorVerticalCurrent q x ⟨n, hn⟩ =
        rotatorLeftHeight q x ⟨n, hn⟩ - rotatorRightHeight q x ⟨n, hn⟩ := by
  intro n
  induction n with
  | zero =>
      intro hn
      let j : Fin L := ⟨0, hn⟩
      let y : Fin (L + 1) := ⟨0, by omega⟩
      have hdiv := rotatorCurrentDivergence_formula q x y
      have hz := hq (x, y)
      rw [hz] at hdiv
      simp [y, hn] at hdiv
      have hdiv' :
          (if hx : x.val < L then rotatorHorizontalCurrent q ⟨x.val,hx⟩ y else 0) +
            rotatorVerticalCurrent q x j -
            (if hx : 0 < x.val then
              rotatorHorizontalCurrent q ⟨x.val - 1, by have _h := x.isLt; omega⟩ y
            else 0) = 0 := by simpa [y, j] using hdiv.symm
      have hleft := rotatorHorizontalIncoming_height q x j
      have hright := rotatorHorizontalOutgoing_height q x j
      have hrec : rotatorVerticalCurrent q x j =
          (if hx : 0 < x.val then
            rotatorHorizontalCurrent q ⟨x.val - 1, by have _h := x.isLt; omega⟩ y
          else 0) -
          (if hx : x.val < L then rotatorHorizontalCurrent q ⟨x.val, hx⟩ y else 0) := by
        omega
      have hleft' :
          (if hx : 0 < x.val then
            rotatorHorizontalCurrent q ⟨x.val - 1, by have _h := x.isLt; omega⟩ y
          else 0) = rotatorLeftHeight q x j := by
        simpa [j, y] using hleft
      have hright' :
          (if hx : x.val < L then rotatorHorizontalCurrent q ⟨x.val,hx⟩ y else 0) =
            rotatorRightHeight q x j := by
        simpa [j, y] using hright
      calc
        rotatorVerticalCurrent q x j = _ := hrec
        _ = rotatorLeftHeight q x j - rotatorRightHeight q x j := by
          rw [hleft', hright']
  | succ n ih =>
      intro hn
      have hnprev : n < L := by omega
      let j : Fin L := ⟨n, hnprev⟩
      let jnext : Fin L := ⟨n + 1, hn⟩
      let y : Fin (L + 1) := ⟨n + 1, by omega⟩
      have hdiv := rotatorCurrentDivergence_formula q x y
      have hz := hq (x, y)
      rw [hz] at hdiv
      have hdiv' :
          (if hx : x.val < L then rotatorHorizontalCurrent q ⟨x.val,hx⟩ y else 0) +
            rotatorVerticalCurrent q x jnext -
            (if hx : 0 < x.val then
              rotatorHorizontalCurrent q ⟨x.val - 1, by have _h := x.isLt; omega⟩ y
            else 0) - rotatorVerticalCurrent q x j = 0 := by
        simpa [y, j, jnext, show n + 1 < L by omega] using hdiv.symm
      have hrec : rotatorVerticalCurrent q x jnext =
          rotatorVerticalCurrent q x j +
            (if hx : 0 < x.val then
              rotatorHorizontalCurrent q ⟨x.val - 1, by have _h := x.isLt; omega⟩ y
            else 0) -
            (if hx : x.val < L then rotatorHorizontalCurrent q ⟨x.val,hx⟩ y else 0) := by
        omega
      have hleft := rotatorHorizontalIncoming_height q x jnext
      have hright := rotatorHorizontalOutgoing_height q x jnext
      have hprev := ih hnprev
      have hleft' :
          (if hx : 0 < x.val then
            rotatorHorizontalCurrent q ⟨x.val - 1, by have _h := x.isLt; omega⟩ y
          else 0) = rotatorLeftHeight q x jnext - rotatorLeftHeight q x j := by
        simpa [y, j, jnext] using hleft
      have hright' :
          (if hx : x.val < L then rotatorHorizontalCurrent q ⟨x.val,hx⟩ y else 0) =
            rotatorRightHeight q x jnext - rotatorRightHeight q x j := by
        simpa [y, j, jnext] using hright
      calc
        rotatorVerticalCurrent q x jnext =
            rotatorVerticalCurrent q x j +
              (if hx : 0 < x.val then
                rotatorHorizontalCurrent q ⟨x.val - 1, by have _h := x.isLt; omega⟩ y
              else 0) -
              (if hx : x.val < L then rotatorHorizontalCurrent q ⟨x.val,hx⟩ y else 0) := hrec
        _ = rotatorLeftHeight q x jnext - rotatorRightHeight q x jnext := by
          rw [hprev, hleft', hright']
          abel

/-- A neutral current's vertical component is the left-minus-right height jump reconstructed by
the bottom-to-top path sum, including the two boundary columns. -/
theorem rotatorHeightPotential_vertical_step (q : RotatorInternalBond L → ℤ)
    (hq : ∀ v, rotatorCurrentDivergence q v = 0) (x : Fin (L + 1)) (j : Fin L) :
    rotatorVerticalCurrent q x j = rotatorLeftHeight q x j - rotatorRightHeight q x j :=
  rotatorVerticalPathStep q hq x j.val j.isLt

private theorem rotatorTopHorizontalPath (q : RotatorInternalBond L → ℤ)
    (hq : ∀ v, rotatorCurrentDivergence q v = 0) :
    ∀ n (hn : n < L),
      rotatorHorizontalCurrent q ⟨n, hn⟩ ⟨L, by omega⟩ =
        -rotatorHeightPotential q ⟨n, hn⟩ ⟨L - 1, by omega⟩ := by
  intro n
  induction n with
  | zero =>
      intro hn
      let i : Fin L := ⟨0, hn⟩
      let x : Fin (L + 1) := ⟨0, by omega⟩
      let y : Fin (L + 1) := ⟨L, by omega⟩
      let j : Fin L := ⟨L - 1, by omega⟩
      have hLpos : 0 < L := by omega
      have hdiv := rotatorCurrentDivergence_formula q x y
      have hz := hq (x,y)
      rw [hz] at hdiv
      have hdiv' :
          rotatorHorizontalCurrent q i y - rotatorVerticalCurrent q x j = 0 := by
        simpa [x, y, j, i, hn, hLpos] using hdiv.symm
      have hK := rotatorHeightPotential_vertical_step q hq x j
      have hK' : rotatorVerticalCurrent q x j =
          -rotatorHeightPotential q i j := by
        simpa [rotatorLeftHeight, rotatorRightHeight, x, i, hLpos] using hK
      have htop : rotatorHorizontalCurrent q i y =
          rotatorVerticalCurrent q x j := by omega
      simpa [i, y, j] using (by rw [htop, hK'])
  | succ n ih =>
      intro hn
      have hnprev : n < L := by omega
      let iPrev : Fin L := ⟨n, hnprev⟩
      let i : Fin L := ⟨n + 1, hn⟩
      let x : Fin (L + 1) := ⟨n + 1, by omega⟩
      let y : Fin (L + 1) := ⟨L, by omega⟩
      let j : Fin L := ⟨L - 1, by omega⟩
      have hLpos : 0 < L := by omega
      have hdiv := rotatorCurrentDivergence_formula q x y
      have hz := hq (x,y)
      rw [hz] at hdiv
      have hdiv' :
          rotatorHorizontalCurrent q i y -
            rotatorHorizontalCurrent q iPrev y -
            rotatorVerticalCurrent q x j = 0 := by
        simpa [x, y, j, i, iPrev, hn, hnprev, hLpos] using hdiv.symm
      have hK := rotatorHeightPotential_vertical_step q hq x j
      have hK' : rotatorVerticalCurrent q x j =
          rotatorHeightPotential q iPrev j - rotatorHeightPotential q i j := by
        simpa [rotatorLeftHeight, rotatorRightHeight, x, i, iPrev, hLpos, hn] using hK
      have hprev := ih hnprev
      calc
        rotatorHorizontalCurrent q i y =
            rotatorHorizontalCurrent q iPrev y +
              rotatorVerticalCurrent q x j := by omega
        _ = -rotatorHeightPotential q i j := by
          rw [hprev, hK']
          abel

/-- The horizontal current induced by a pinned face height, in grid coordinates. -/
theorem rotatorFaceHeightCurrent_horizontal (h : RotatorFaceHeight L)
    (i : Fin L) (j : Fin (L + 1)) :
    rotatorFaceHeightCurrent h (.inl (horizontalDualEdgeData i j)) =
      (if hj : j.val < L then h.1 (some (i, ⟨j.val, hj⟩)) else 0) -
        (if hj : 0 < j.val then
          h.1 (some (i, ⟨j.val - 1, by have _h := j.isLt; omega⟩)) else 0) := by
  have hLpos : 0 < L := by have hi := i.isLt; omega
  by_cases hj : j.val < L
  · by_cases hj0 : 0 < j.val
    · have hjne : j ≠ 0 := by
        intro he
        rw [he] at hj0
        simp at hj0
      simp [rotatorFaceHeightCurrent, rotatorDualGraph, wiredBoxGraph, wiredBoxSrc,
        wiredBoxTgt, horizontalPrimalSrc, horizontalPrimalTgt, horizontalFaceX,
        horizontalDualEdgeData, hj, hj0, hjne, Fin.val_castLE]
    · have hjz : j.val = 0 := by omega
      have hjEq : j = ⟨0, by omega⟩ := Fin.ext (by simpa using hjz)
      rw [hjEq]
      simp [rotatorFaceHeightCurrent, rotatorDualGraph, wiredBoxGraph, wiredBoxSrc,
        wiredBoxTgt, horizontalPrimalSrc, horizontalPrimalTgt, horizontalFaceX,
        horizontalDualEdgeData, h.2, hLpos]
  · have hjL : j.val = L := by have h := j.isLt; omega
    have hjEq : j = ⟨L, by omega⟩ := Fin.ext (by simpa using hjL)
    have hLne : L ≠ 0 := Nat.ne_of_gt hLpos
    rw [hjEq]
    simp [rotatorFaceHeightCurrent, rotatorDualGraph, wiredBoxGraph, wiredBoxSrc,
      wiredBoxTgt, horizontalPrimalSrc, horizontalPrimalTgt, horizontalFaceX,
      horizontalDualEdgeData, h.2, hLpos, hLne]

/-- The vertical current induced by a pinned face height, in grid coordinates. -/
theorem rotatorFaceHeightCurrent_vertical (h : RotatorFaceHeight L)
    (i : Fin (L + 1)) (j : Fin L) :
    rotatorFaceHeightCurrent h (.inr (verticalDualEdgeData i j)) =
      (if hi : 0 < i.val then
        h.1 (some (⟨i.val - 1, by have _h := i.isLt; omega⟩, j)) else 0) -
        (if hi : i.val < L then h.1 (some (⟨i.val, hi⟩, j)) else 0) := by
  have hLpos : 0 < L := by have hj := j.isLt; omega
  by_cases hi0 : 0 < i.val
  · by_cases hiL : i.val < L
    · have hine : i ≠ 0 := by
        intro he
        rw [he] at hi0
        simp at hi0
      simp [rotatorFaceHeightCurrent, rotatorDualGraph, wiredBoxGraph, wiredBoxSrc,
        wiredBoxTgt, verticalPrimalSrc, verticalPrimalTgt, verticalFaceY,
        verticalDualEdgeData, hi0, hiL, hine, Fin.val_castLE]
    · have hiEq : i.val = L := by have h := i.isLt; omega
      have hiFin : i = ⟨L, by omega⟩ := Fin.ext (by simpa using hiEq)
      have hLne : L ≠ 0 := Nat.ne_of_gt hLpos
      rw [hiFin]
      simp [rotatorFaceHeightCurrent, rotatorDualGraph, wiredBoxGraph, wiredBoxSrc,
        wiredBoxTgt, verticalPrimalSrc, verticalPrimalTgt, verticalFaceY,
        verticalDualEdgeData, h.2, hLpos, hLne]
  · have hiEq : i.val = 0 := by omega
    have hiFin : i = ⟨0, by omega⟩ := Fin.ext (by simpa using hiEq)
    rw [hiFin]
    simp [rotatorFaceHeightCurrent, rotatorDualGraph, wiredBoxGraph, wiredBoxSrc,
      wiredBoxTgt, verticalPrimalSrc, verticalPrimalTgt, verticalFaceY,
      verticalDualEdgeData, h.2, hLpos]

def rotatorFaceGridValue (h : RotatorFaceHeight L)
    (x y : Fin (L + 1)) : ℤ :=
  if hx : x.val < L then
    if hy : y.val < L then h.1 (some (⟨x.val, hx⟩, ⟨y.val, hy⟩)) else 0
  else 0

def rotatorFaceGridBelow (h : RotatorFaceHeight L)
    (x y : Fin (L + 1)) : ℤ :=
  if hy : 0 < y.val then
    rotatorFaceGridValue h x ⟨y.val - 1, by have _h := y.isLt; omega⟩
  else 0

def rotatorFaceGridLeft (h : RotatorFaceHeight L)
    (x y : Fin (L + 1)) : ℤ :=
  if hx : 0 < x.val then
    rotatorFaceGridValue h ⟨x.val - 1, by have _h := x.isLt; omega⟩ y
  else 0

private theorem rotatorFaceHeightCurrent_horizontal_grid (h : RotatorFaceHeight L)
    (i : Fin L) (j : Fin (L + 1)) :
    rotatorFaceHeightCurrent h (.inl (horizontalDualEdgeData i j)) =
      rotatorFaceGridValue h ⟨i.val, by omega⟩ j -
        rotatorFaceGridBelow h ⟨i.val, by omega⟩ j := by
  rw [rotatorFaceHeightCurrent_horizontal]
  by_cases hjL : j.val < L
  · by_cases hj0 : 0 < j.val
    · have hjprev : j.val - 1 < L := by omega
      simp [rotatorFaceGridValue, rotatorFaceGridBelow, hjL, hj0, hjprev]
    · have hjz : j.val = 0 := by omega
      simp [rotatorFaceGridValue, rotatorFaceGridBelow, hjz]
  · have hjz : j.val = L := by have h := j.isLt; omega
    have hLpos : 0 < L := by have hi := i.isLt; omega
    simp [rotatorFaceGridValue, rotatorFaceGridBelow, hjz, hLpos]

private theorem rotatorFaceHeightCurrent_vertical_grid (h : RotatorFaceHeight L)
    (i : Fin (L + 1)) (j : Fin L) :
    rotatorFaceHeightCurrent h (.inr (verticalDualEdgeData i j)) =
      rotatorFaceGridLeft h i ⟨j.val, by omega⟩ -
        rotatorFaceGridValue h i ⟨j.val, by omega⟩ := by
  rw [rotatorFaceHeightCurrent_vertical]
  by_cases hi0 : 0 < i.val
  · by_cases hiL : i.val < L
    · have hiprev : i.val - 1 < L := by omega
      simp [rotatorFaceGridValue, rotatorFaceGridLeft, hiprev]
    · have hix : i.val = L := by have h := i.isLt; omega
      have hLpos : 0 < L := by omega
      simp [rotatorFaceGridValue, rotatorFaceGridLeft, hix, hLpos]
  · have hix : i.val = 0 := by omega
    simp [rotatorFaceGridValue, rotatorFaceGridLeft, hix]

/-- A source-oriented face-height current has zero divergence at every free spin site. -/
theorem rotatorFaceHeightCurrent_neutral (h : RotatorFaceHeight L) :
    ∀ v, rotatorCurrentDivergence (rotatorFaceHeightCurrent h) v = 0 := by
  intro v
  rcases v with ⟨x, y⟩
  rw [rotatorCurrentDivergence_formula]
  simp only [rotatorHorizontalCurrent, rotatorVerticalCurrent,
    rotatorFaceHeightCurrent_horizontal_grid,
    rotatorFaceHeightCurrent_vertical_grid]
  unfold rotatorFaceGridValue rotatorFaceGridBelow rotatorFaceGridLeft
  by_cases hx0 : x.val = 0
  all_goals by_cases hxL : x.val < L
  all_goals by_cases hy0 : y.val = 0
  all_goals by_cases hyL : y.val < L
  all_goals try have hxpos : 0 < x.val := by omega
  all_goals try have hxprev : x.val - 1 < L := by omega
  all_goals try have hypos : 0 < y.val := by omega
  all_goals try have hyprev : y.val - 1 < L := by omega
  all_goals try have hLpos : 0 < L := by omega
  all_goals try have hxnot : ¬ x.val < L := by omega
  all_goals try have hynot : ¬ y.val < L := by omega
  all_goals split_ifs <;> simp_all [rotatorFaceGridValue] <;> abel

/-- The path sum starts with the lower boundary-crossing horizontal edge. -/
private theorem rotatorHeightPotential_bottom (q : RotatorInternalBond L → ℤ) (i : Fin L) :
    rotatorHeightPotential q i ⟨0, by have hi := i.isLt; omega⟩ =
      rotatorHorizontalCurrent q i (0 : Fin (L + 1)) := by
  have hLpos : 0 < L := by have hi := i.isLt; omega
  simp [rotatorHeightPotential, rotatorHorizontalCurrentNat,
    rotatorHorizontalCurrent, hLpos]

private theorem rotatorHeightFromCurrent_horizontal (q : RotatorInternalBond L → ℤ)
    (hq : ∀ v, rotatorCurrentDivergence q v = 0) (i : Fin L) (j : Fin (L + 1)) :
    rotatorFaceHeightCurrent (rotatorHeightFromCurrent q)
        (.inl (horizontalDualEdgeData i j)) =
      rotatorHorizontalCurrent q i j := by
  rw [rotatorFaceHeightCurrent_horizontal]
  by_cases hjtop : j.val = L
  · have hjEq : j = ⟨L, by omega⟩ := Fin.ext (by simpa using hjtop)
    rw [hjEq]
    have hLpos : 0 < L := by have hi := i.isLt; omega
    have htop := rotatorTopHorizontalPath q hq i.val i.isLt
    simpa [rotatorHeightFromCurrent, hLpos] using htop.symm
  · have hjlt : j.val < L := by have h := j.isLt; omega
    by_cases hjzero : j.val = 0
    · have hjEq : j = ⟨0, by omega⟩ := Fin.ext (by simpa using hjzero)
      rw [hjEq]
      have hLpos : 0 < L := by have hi := i.isLt; omega
      simpa [rotatorHeightFromCurrent, hjlt, hLpos] using
        rotatorHeightPotential_bottom q i
    · have hjpos : 0 < j.val := by omega
      let j' : Fin L := ⟨j.val, hjlt⟩
      have hstep := rotatorHeightPotential_horizontal_step q i j' hjpos
      simpa [rotatorHeightFromCurrent, hjlt, hjzero, hjpos] using hstep

private theorem rotatorHeightFromCurrent_vertical (q : RotatorInternalBond L → ℤ)
    (hq : ∀ v, rotatorCurrentDivergence q v = 0) (i : Fin (L + 1)) (j : Fin L) :
    rotatorFaceHeightCurrent (rotatorHeightFromCurrent q)
        (.inr (verticalDualEdgeData i j)) =
      rotatorVerticalCurrent q i j := by
  rw [rotatorFaceHeightCurrent_vertical]
  have hstep := rotatorHeightPotential_vertical_step q hq i j
  simpa [rotatorHeightFromCurrent, rotatorLeftHeight, rotatorRightHeight] using hstep.symm

/-- Every divergence-free current is the source-oriented difference of its reconstructed
zero-exterior dual-face height. -/
theorem rotatorHeightFromCurrent_current (q : RotatorInternalBond L → ℤ)
    (hq : ∀ v, rotatorCurrentDivergence q v = 0) :
    rotatorFaceHeightCurrent (rotatorHeightFromCurrent q) = q := by
  funext e
  cases e with
  | inl e =>
      let i : Fin L := ⟨e.1.1.val, by have he := e.1.2; omega⟩
      have he : horizontalDualEdgeData i e.2 = e := by
        apply Prod.ext
        · apply Subtype.ext
          apply Fin.ext
          rfl
        · rfl
      simpa [rotatorHorizontalCurrent, i, he] using
        rotatorHeightFromCurrent_horizontal q hq i e.2
  | inr e =>
      let j : Fin L := ⟨e.2.1.val, by have he := e.2.2; omega⟩
      have he : verticalDualEdgeData e.1 j = e := by
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          apply Fin.ext
          rfl
      simpa [rotatorVerticalCurrent, j, he] using
        rotatorHeightFromCurrent_vertical q hq e.1 j


/-- A pinned height is determined by its source-oriented edge differences. -/
theorem rotatorFaceHeightCurrent_injective :
    Function.Injective (rotatorFaceHeightCurrent (L := L)) := by
  intro h g heq
  apply Subtype.ext
  funext f
  cases f with
  | none => simp [h.2, g.2]
  | some p =>
      rcases p with ⟨i, j⟩
      have hrow : ∀ n (hn : n < L),
          h.1 (some (⟨n, hn⟩, j)) = g.1 (some (⟨n, hn⟩, j)) := by
        intro n
        induction n with
        | zero =>
            intro hn
            let x : Fin (L + 1) := ⟨0, by omega⟩
            have hcur := congrFun heq (.inr (verticalDualEdgeData x j))
            simp only [rotatorFaceHeightCurrent_vertical] at hcur
            have hLpos : 0 < L := by omega
            simp [x, hLpos] at hcur
            omega
        | succ n ih =>
            intro hn
            have hnprev : n < L := by omega
            let x : Fin (L + 1) := ⟨n + 1, by omega⟩
            have hcur := congrFun heq (.inr (verticalDualEdgeData x j))
            simp only [rotatorFaceHeightCurrent_vertical] at hcur
            have hprev := ih hnprev
            have hLpos : 0 < L := by omega
            have hcur' :
                h.1 (some (⟨n, hnprev⟩, j)) - h.1 (some (⟨n + 1, hn⟩, j)) =
                  g.1 (some (⟨n, hnprev⟩, j)) - g.1 (some (⟨n + 1, hn⟩, j)) := by
              simpa [x, rotatorLeftHeight, rotatorRightHeight, hLpos,
                show n + 1 < L by omega] using hcur
            omega
      have hface := hrow i.val i.isLt
      simpa using hface

/-- Reconstructing the face heights after applying the current-to-height map is the identity. -/
theorem rotatorHeightFromCurrent_faceHeight (h : RotatorFaceHeight L) :
    rotatorHeightFromCurrent (rotatorFaceHeightCurrent h) = h := by
  apply rotatorFaceHeightCurrent_injective
  exact rotatorHeightFromCurrent_current _ (rotatorFaceHeightCurrent_neutral h)

/-- The free-box planar current / pinned face-height bijection, with source orientation fixed by
wiredBoxGraph. -/
def rotatorNeutralCurrentHeightEquiv (L : ℕ) :
    RotatorNeutralCurrent L ≃ RotatorFaceHeight L where
  toFun q := rotatorHeightFromCurrent q.1
  invFun h := ⟨rotatorFaceHeightCurrent h, rotatorFaceHeightCurrent_neutral h⟩
  left_inv q := by
    apply Subtype.ext
    exact rotatorHeightFromCurrent_current q.1 q.2
  right_inv h := rotatorHeightFromCurrent_faceHeight h


/- The reconstructed heights are introduced below before the current/height equivalence. -/

end FroehlichSpencer.BKT.Rotator

end
