/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Lattice2D.SquareFree
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # Discrete Poincare lemma for the free square -/

@[expose] public section

namespace FroehlichSpencer.BKT.Clock.Peierls

open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Multigraph

/-- The positively oriented horizontal edge based at the natural coordinates `(i,j)`. -/
def squareFreeHorizontalEdgeAt {L : ℕ} (i j : ℕ)
    (hi : i + 1 < L) (hj : j < L) : SquareFreeEdge L :=
  Sum.inl ((⟨⟨i, by omega⟩, hi⟩), ⟨j, hj⟩)

/-- The positively oriented vertical edge based at the natural coordinates `(i,j)`. -/
def squareFreeVerticalEdgeAt {L : ℕ} (i j : ℕ)
    (hi : i < L) (hj : j + 1 < L) : SquareFreeEdge L :=
  Sum.inr (⟨i, hi⟩, ⟨⟨j, by omega⟩, hj⟩)

/-- The horizontal component of an edge field, extended by zero outside the edge carrier. -/
def squareFreeHorizontalValue {L n : ℕ} (η : SquareFreeEdge L → ZMod n)
    (i j : ℕ) : ZMod n :=
  if hi : i + 1 < L then
    if hj : j < L then η (squareFreeHorizontalEdgeAt i j hi hj) else 0
  else 0

/-- The vertical component of an edge field, extended by zero outside the edge carrier. -/
def squareFreeVerticalValue {L n : ℕ} (η : SquareFreeEdge L → ZMod n)
    (i j : ℕ) : ZMod n :=
  if hi : i < L then
    if hj : j + 1 < L then η (squareFreeVerticalEdgeAt i j hi hj) else 0
  else 0

/-- A field has zero circulation around each unit square. In coordinates, this says that
bottom plus right equals left plus top. -/
def squareFreePlaquetteClosed {L n : ℕ} (η : SquareFreeEdge L → ZMod n) : Prop :=
  ∀ i j : ℕ, i + 1 < L → j + 1 < L →
    squareFreeHorizontalValue η i j + squareFreeVerticalValue η (i + 1) j =
      squareFreeVerticalValue η i j + squareFreeHorizontalValue η i (j + 1)

/-- Sum of a horizontal field along the first `i` edges of row `j`. -/
def squareFreeHorizontalPathSum {L n : ℕ} (η : SquareFreeEdge L → ZMod n)
    (j : ℕ) : ℕ → ZMod n
  | 0 => 0
  | i + 1 => squareFreeHorizontalPathSum η j i + squareFreeHorizontalValue η i j

/-- Sum of a vertical field along the first `j` edges of column `i`. -/
def squareFreeVerticalPathSum {L n : ℕ} (η : SquareFreeEdge L → ZMod n)
    (i : ℕ) : ℕ → ZMod n
  | 0 => 0
  | j + 1 => squareFreeVerticalPathSum η i j + squareFreeVerticalValue η i j

/-- Integrate a field along the path that first moves horizontally on the bottom row and then
vertically in the target column. The minus sign matches `Multigraph.grad`, whose convention is
source value minus target value. -/
def squareFreePathPotential {L n : ℕ} (η : SquareFreeEdge L → ZMod n)
    (x : SquareFreeVertex L) : ZMod n :=
  -(squareFreeHorizontalPathSum η 0 x.1.val +
    squareFreeVerticalPathSum η x.1.val x.2.val)

private theorem squareFreeVerticalPathSum_column_difference
    {L n : ℕ} (η : SquareFreeEdge L → ZMod n)
    (hclosed : squareFreePlaquetteClosed η) {i m : ℕ}
    (hi : i + 1 < L) (hm : m < L) :
    squareFreeVerticalPathSum η (i + 1) m - squareFreeVerticalPathSum η i m =
      squareFreeHorizontalValue η i m - squareFreeHorizontalValue η i 0 := by
  induction m with
  | zero =>
      simp [squareFreeVerticalPathSum, squareFreeHorizontalValue, hi]
  | succ m ih =>
      have hm' : m + 1 < L := hm
      have hc := hclosed i m hi hm'
      have hstep : squareFreeVerticalValue η (i + 1) m -
          squareFreeVerticalValue η i m =
          squareFreeHorizontalValue η i (m + 1) -
            squareFreeHorizontalValue η i m := by
        linear_combination hc
      calc
        _ = (squareFreeVerticalPathSum η (i + 1) m -
            squareFreeVerticalPathSum η i m) +
            (squareFreeVerticalValue η (i + 1) m -
              squareFreeVerticalValue η i m) := by
                simp only [squareFreeVerticalPathSum]
                abel
        _ = (squareFreeHorizontalValue η i m -
            squareFreeHorizontalValue η i 0) +
            (squareFreeVerticalValue η (i + 1) m -
              squareFreeVerticalValue η i m) := by rw [ih (by omega)]
        _ = squareFreeHorizontalValue η i (m + 1) -
            squareFreeHorizontalValue η i 0 := by rw [hstep]; abel

private theorem squareFreePathPotential_horizontal
    {L n : ℕ} (η : SquareFreeEdge L → ZMod n)
    (hclosed : squareFreePlaquetteClosed η) (i j : Fin L)
    (hi : i.val + 1 < L) :
    squareFreePathPotential η (i, j) -
      squareFreePathPotential η (⟨i.val + 1, hi⟩, j) =
        squareFreeHorizontalValue η i.val j.val := by
  have hhs : squareFreeHorizontalPathSum η 0 (i.val + 1) =
      squareFreeHorizontalPathSum η 0 i.val + squareFreeHorizontalValue η i.val 0 := rfl
  have hvs := squareFreeVerticalPathSum_column_difference η hclosed hi j.isLt
  change -(squareFreeHorizontalPathSum η 0 i.val +
      squareFreeVerticalPathSum η i.val j.val) -
    -(squareFreeHorizontalPathSum η 0 (i.val + 1) +
      squareFreeVerticalPathSum η (i.val + 1) j.val) = _
  rw [hhs]
  simp only [squareFreeHorizontalValue, hi, j.isLt, show 0 < L by omega,
    dite_true] at hvs ⊢
  linear_combination hvs

private theorem squareFreePathPotential_vertical
    {L n : ℕ} (η : SquareFreeEdge L → ZMod n)
    (i j : Fin L) (hj : j.val + 1 < L) :
    squareFreePathPotential η (i, j) -
      squareFreePathPotential η (i, ⟨j.val + 1, hj⟩) =
        squareFreeVerticalValue η i.val j.val := by
  have hvs : squareFreeVerticalPathSum η i.val (j.val + 1) =
      squareFreeVerticalPathSum η i.val j.val +
        squareFreeVerticalValue η i.val j.val := rfl
  change -(squareFreeHorizontalPathSum η 0 i.val +
      squareFreeVerticalPathSum η i.val j.val) -
    -(squareFreeHorizontalPathSum η 0 i.val +
      squareFreeVerticalPathSum η i.val (j.val + 1)) = _
  rw [hvs]
  simp [squareFreeVerticalValue, i.isLt, hj]

/-- Every `ZMod n` edge field on the finite free square with zero plaquette circulation is the
gradient of a vertex potential. -/
theorem squareFreeEdgeField_isGradient
    {L n : ℕ} (η : SquareFreeEdge L → ZMod n)
    (hclosed : squareFreePlaquetteClosed η) :
    ∃ f : SquareFreeVertex L → ZMod n,
      ∀ e : SquareFreeEdge L, (squareFreeGraph L).grad f e = η e := by
  refine ⟨squareFreePathPotential η, ?_⟩
  intro e
  cases e with
  | inl e =>
      rcases e with ⟨i, j⟩
      have hp := squareFreePathPotential_horizontal η hclosed i.1 j i.2
      change squareFreePathPotential η (i.1, j) -
        squareFreePathPotential η (⟨i.1.val + 1, i.2⟩, j) = _
      rw [hp]
      simp [squareFreeHorizontalValue, squareFreeHorizontalEdgeAt, i.2, j.isLt]
  | inr e =>
      rcases e with ⟨i, j⟩
      have hp := squareFreePathPotential_vertical η i j.1 j.2
      change squareFreePathPotential η (i, j.1) -
        squareFreePathPotential η (i, ⟨j.1.val + 1, j.2⟩) = _
      rw [hp]
      simp [squareFreeVerticalValue, squareFreeVerticalEdgeAt, i.isLt, j.2]

end FroehlichSpencer.BKT.Clock.Peierls

end
