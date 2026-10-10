/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Peierls.Extension
import Mathlib.Tactic

/-! # Coordinates for edges touching the inner SOS square

The free edges in the side-`L + 2` square that touch the inner `L`-square are reindexed by the
edges of a side-`L + 1` square. Horizontal edges become vertical edges and conversely.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.SOS.Peierls

open FroehlichSpencer.BKT.Lattice2D

theorem expandedHorizontalBounds {L : ℕ}
    (i : {x : Fin (L + 2) // x.val + 1 < L + 2}) (j : Fin (L + 2))
    (h : isInnerVertex L ((squareFreeGraph (L + 2)).src (Sum.inl (i, j))) ∨
      isInnerVertex L ((squareFreeGraph (L + 2)).tgt (Sum.inl (i, j)))) :
    1 ≤ j.val ∧ j.val ≤ L ∧ i.1.val ≤ L := by
  rcases h with hs | ht
  · change 1 ≤ i.1.val ∧ i.1.val ≤ L ∧ 1 ≤ j.val ∧ j.val ≤ L at hs
    exact ⟨hs.2.2.1, hs.2.2.2, by omega⟩
  · change 1 ≤ i.1.val + 1 ∧ i.1.val + 1 ≤ L ∧ 1 ≤ j.val ∧ j.val ≤ L at ht
    exact ⟨ht.2.2.1, ht.2.2.2, by omega⟩

theorem expandedVerticalBounds {L : ℕ}
    (i : Fin (L + 2)) (j : {y : Fin (L + 2) // y.val + 1 < L + 2})
    (h : isInnerVertex L ((squareFreeGraph (L + 2)).src (Sum.inr (i, j))) ∨
      isInnerVertex L ((squareFreeGraph (L + 2)).tgt (Sum.inr (i, j)))) :
    1 ≤ i.val ∧ i.val ≤ L ∧ j.1.val ≤ L := by
  rcases h with hs | ht
  · change 1 ≤ i.val ∧ i.val ≤ L ∧ 1 ≤ j.1.val ∧ j.1.val ≤ L at hs
    exact ⟨hs.1, hs.2.1, by omega⟩
  · change 1 ≤ i.val ∧ i.val ≤ L ∧ 1 ≤ j.1.val + 1 ∧ j.1.val + 1 ≤ L at ht
    exact ⟨ht.1, ht.2.1, by omega⟩

/-- Reindex an expanded edge touching the inner square as an edge of the side-`L+1` square. -/
def expandedInnerEdgeToSquareFreeEdge {L : ℕ} (e : ExpandedInnerEdge L) :
    Lattice2D.SquareFreeEdge (L + 1) := by
  rcases e with ⟨e, he⟩
  cases e with
  | inl e =>
      rcases e with ⟨i, j⟩
      have hb := expandedHorizontalBounds i j he
      have hi : i.1.val < L + 1 := by omega
      have hj : j.val - 1 < L + 1 := by omega
      have hj' : (j.val - 1) + 1 < L + 1 := by omega
      exact .inr (⟨⟨i.1.val, hi⟩, ⟨⟨j.val - 1, hj⟩, hj'⟩⟩)
  | inr e =>
      rcases e with ⟨i, j⟩
      have hb := expandedVerticalBounds i j he
      have hi : i.val - 1 < L + 1 := by omega
      have hi' : (i.val - 1) + 1 < L + 1 := by omega
      have hj : j.1.val < L + 1 := by omega
      exact .inl (⟨⟨⟨i.val - 1, hi⟩, hi'⟩, ⟨j.1.val, hj⟩⟩)

/-- Expand an edge of the side-`L+1` square to the unique edge touching the inner `L`-square. -/
def squareFreeEdgeToExpandedInnerEdge {L : ℕ}
    (e : Lattice2D.SquareFreeEdge (L + 1)) : ExpandedInnerEdge L := by
  cases e with
  | inl e =>
      rcases e with ⟨i, j⟩
      have hi : i.1.val + 1 < L + 2 := by omega
      have hj : j.val < L + 2 := by omega
      have hj' : j.val + 1 < L + 2 := by omega
      let x : Fin (L + 2) := ⟨i.1.val + 1, hi⟩
      let y : Fin (L + 2) := ⟨j.val, hj⟩
      let yEdge : {y : Fin (L + 2) // y.val + 1 < L + 2} := ⟨y, hj'⟩
      refine ⟨.inr (x, yEdge), ?_⟩
      by_cases hzero : j.val = 0
      · right
        change 1 ≤ i.1.val + 1 ∧ i.1.val + 1 ≤ L ∧
          1 ≤ j.val + 1 ∧ j.val + 1 ≤ L
        omega
      · left
        change 1 ≤ i.1.val + 1 ∧ i.1.val + 1 ≤ L ∧
          1 ≤ j.val ∧ j.val ≤ L
        omega
  | inr e =>
      rcases e with ⟨i, j⟩
      have hi : i.val < L + 2 := by omega
      have hi' : i.val + 1 < L + 2 := by omega
      have hj : j.1.val + 1 < L + 2 := by omega
      let x : Fin (L + 2) := ⟨i.val, hi⟩
      let xEdge : {x : Fin (L + 2) // x.val + 1 < L + 2} := ⟨x, hi'⟩
      let y : Fin (L + 2) := ⟨j.1.val + 1, hj⟩
      refine ⟨.inl (xEdge, y), ?_⟩
      by_cases hzero : i.val = 0
      · right
        change 1 ≤ i.val + 1 ∧ i.val + 1 ≤ L ∧
          1 ≤ j.1.val + 1 ∧ j.1.val + 1 ≤ L
        omega
      · left
        change 1 ≤ i.val ∧ i.val ≤ L ∧
          1 ≤ j.1.val + 1 ∧ j.1.val + 1 ≤ L
        omega

theorem expandedInnerEdge_roundtrip {L : ℕ} (e : ExpandedInnerEdge L) :
    squareFreeEdgeToExpandedInnerEdge (expandedInnerEdgeToSquareFreeEdge e) = e := by
  apply Subtype.ext
  rcases e with ⟨e, he⟩
  cases e with
  | inl e =>
      rcases e with ⟨i, j⟩
      have hb := expandedHorizontalBounds i j he
      apply congrArg Sum.inl
      apply Prod.ext
      · apply Subtype.ext
        apply Fin.ext
        rfl
      · apply Fin.ext
        exact Nat.sub_add_cancel hb.1
  | inr e =>
      rcases e with ⟨i, j⟩
      have hb := expandedVerticalBounds i j he
      apply congrArg Sum.inr
      apply Prod.ext
      · apply Fin.ext
        exact Nat.sub_add_cancel hb.1
      · apply Subtype.ext
        apply Fin.ext
        rfl

theorem squareFreeEdge_roundtrip {L : ℕ}
    (e : Lattice2D.SquareFreeEdge (L + 1)) :
    expandedInnerEdgeToSquareFreeEdge (squareFreeEdgeToExpandedInnerEdge e) = e := by
  cases e with
  | inl e =>
      rcases e with ⟨i, j⟩
      apply congrArg Sum.inl
      apply Prod.ext
      · apply Subtype.ext
        apply Fin.ext
        change i.1.val + 1 - 1 = i.1.val
        omega
      · apply Fin.ext
        rfl
  | inr e =>
      rcases e with ⟨i, j⟩
      apply congrArg Sum.inr
      apply Prod.ext
      · apply Fin.ext
        rfl
      · apply Subtype.ext
        apply Fin.ext
        change j.1.val + 1 - 1 = j.1.val
        omega

/-- The target edges touching the inner box are exactly the edges of a side-`L+1` free square. -/
def expandedInnerEdgeEquiv (L : ℕ) : ExpandedInnerEdge L ≃
    Lattice2D.SquareFreeEdge (L + 1) where
  toFun := expandedInnerEdgeToSquareFreeEdge
  invFun := squareFreeEdgeToExpandedInnerEdge
  left_inv := expandedInnerEdge_roundtrip
  right_inv := squareFreeEdge_roundtrip

end FroehlichSpencer.BKT.SOS.Peierls

end
