/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Lattice2D.SquareFree
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # A coefficient-independent discrete Poincare lemma on the free square

For an edge field valued in any additive commutative group, vanishing circulation around every
unit square makes the field a graph gradient. The potential is obtained by integrating first along
the bottom row and then up the target column. Exactness also gives path independence for every
oriented edge path in the square.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Clock.Peierls.GenericGradient

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
def squareFreeHorizontalValue {L : ℕ} {G : Type*} [Zero G]
    (η : SquareFreeEdge L → G) (i j : ℕ) : G :=
  if hi : i + 1 < L then
    if hj : j < L then η (squareFreeHorizontalEdgeAt i j hi hj) else 0
  else 0

/-- The vertical component of an edge field, extended by zero outside the edge carrier. -/
def squareFreeVerticalValue {L : ℕ} {G : Type*} [Zero G]
    (η : SquareFreeEdge L → G) (i j : ℕ) : G :=
  if hi : i < L then
    if hj : j + 1 < L then η (squareFreeVerticalEdgeAt i j hi hj) else 0
  else 0

/-- A field has zero circulation around each unit square. In coordinates, this says that bottom
plus right equals left plus top. -/
def squareFreePlaquetteClosed {L : ℕ} {G : Type*} [AddCommGroup G]
    (η : SquareFreeEdge L → G) : Prop :=
  ∀ i j : ℕ, i + 1 < L → j + 1 < L →
    squareFreeHorizontalValue η i j + squareFreeVerticalValue η (i + 1) j =
      squareFreeVerticalValue η i j + squareFreeHorizontalValue η i (j + 1)

/-- Sum of a horizontal field along the first `i` edges of row `j`. -/
def squareFreeHorizontalPathSum {L : ℕ} {G : Type*} [AddCommGroup G]
    (η : SquareFreeEdge L → G) (j : ℕ) : ℕ → G
  | 0 => 0
  | i + 1 => squareFreeHorizontalPathSum η j i + squareFreeHorizontalValue η i j

/-- Sum of a vertical field along the first `j` edges of column `i`. -/
def squareFreeVerticalPathSum {L : ℕ} {G : Type*} [AddCommGroup G]
    (η : SquareFreeEdge L → G) (i : ℕ) : ℕ → G
  | 0 => 0
  | j + 1 => squareFreeVerticalPathSum η i j + squareFreeVerticalValue η i j

/-- Integrate a field along the path that first moves horizontally on the bottom row and then
vertically in the target column. The minus sign matches `Multigraph.grad`, whose convention is
source value minus target value. -/
def squareFreePathPotential {L : ℕ} {G : Type*} [AddCommGroup G]
    (η : SquareFreeEdge L → G) (x : SquareFreeVertex L) : G :=
  -(squareFreeHorizontalPathSum η 0 x.1.val +
    squareFreeVerticalPathSum η x.1.val x.2.val)

private theorem squareFreeVerticalPathSum_column_difference
    {L : ℕ} {G : Type*} [AddCommGroup G] (η : SquareFreeEdge L → G)
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
        calc
          _ = (squareFreeHorizontalValue η i m +
              squareFreeVerticalValue η (i + 1) m) -
                (squareFreeHorizontalValue η i m +
                  squareFreeVerticalValue η i m) := by abel
          _ = (squareFreeVerticalValue η i m +
              squareFreeHorizontalValue η i (m + 1)) -
                (squareFreeHorizontalValue η i m +
                  squareFreeVerticalValue η i m) := by rw [hc]
          _ = _ := by abel
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
    {L : ℕ} {G : Type*} [AddCommGroup G] (η : SquareFreeEdge L → G)
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
  calc
    _ = (squareFreeVerticalPathSum η (i.val + 1) j.val -
          squareFreeVerticalPathSum η i.val j.val) +
        squareFreeHorizontalValue η i.val 0 := by abel
    _ = (squareFreeHorizontalValue η i.val j.val -
          squareFreeHorizontalValue η i.val 0) +
        squareFreeHorizontalValue η i.val 0 := by rw [hvs]
    _ = squareFreeHorizontalValue η i.val j.val := by abel

private theorem squareFreePathPotential_vertical
    {L : ℕ} {G : Type*} [AddCommGroup G] (η : SquareFreeEdge L → G)
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

/-- Every square edge field in an additive commutative group with zero plaquette circulation is
the graph gradient of a vertex potential. -/
theorem squareFreeEdgeField_isGradient
    {L : ℕ} {G : Type*} [AddCommGroup G] (η : SquareFreeEdge L → G)
    (hclosed : squareFreePlaquetteClosed η) :
    ∃ f : SquareFreeVertex L → G,
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

/-- An oriented square path consists of forward and backward traversals of the represented
positively oriented edges. -/
inductive SquareFreePath (L : ℕ) : SquareFreeVertex L → SquareFreeVertex L → Type
  | nil (v : SquareFreeVertex L) : SquareFreePath L v v
  | forward {w : SquareFreeVertex L} (e : SquareFreeEdge L)
      (p : SquareFreePath L ((squareFreeGraph L).tgt e) w) :
      SquareFreePath L ((squareFreeGraph L).src e) w
  | backward {w : SquareFreeVertex L} (e : SquareFreeEdge L)
      (p : SquareFreePath L ((squareFreeGraph L).src e) w) :
      SquareFreePath L ((squareFreeGraph L).tgt e) w

/-- The signed sum of an edge field along an oriented edge path. -/
def squareFreePathIntegral {L : ℕ} {G : Type*} [AddCommGroup G]
    (η : SquareFreeEdge L → G) : {u v : SquareFreeVertex L} →
      SquareFreePath L u v → G
  | _, _, .nil _ => 0
  | _, _, .forward e p => η e + squareFreePathIntegral η p
  | _, _, .backward e p => -η e + squareFreePathIntegral η p

/-- The integral of a graph gradient along any oriented edge path is the potential drop between
its endpoints. -/
theorem squareFreePathIntegral_grad
    {L : ℕ} {G : Type*} [AddCommGroup G]
    (f : SquareFreeVertex L → G) {u v : SquareFreeVertex L}
    (p : SquareFreePath L u v) :
    squareFreePathIntegral ((squareFreeGraph L).grad f) p = f u - f v := by
  induction p with
  | nil w => simp [squareFreePathIntegral]
  | forward e p ih =>
      simp only [squareFreePathIntegral]
      rw [ih]
      simp only [Multigraph.grad]
      abel
  | backward e p ih =>
      simp only [squareFreePathIntegral]
      rw [ih]
      simp only [Multigraph.grad]
      abel

/-- Path integrals of a closed square edge field depend only on the endpoints. -/
theorem squareFreePathIntegral_path_independent
    {L : ℕ} {G : Type*} [AddCommGroup G] (η : SquareFreeEdge L → G)
    (hclosed : squareFreePlaquetteClosed η) {u v : SquareFreeVertex L}
    (p q : SquareFreePath L u v) :
    squareFreePathIntegral η p = squareFreePathIntegral η q := by
  obtain ⟨f, hf⟩ := squareFreeEdgeField_isGradient η hclosed
  have hp : squareFreePathIntegral η p = f u - f v := by
    have heq : η = (squareFreeGraph L).grad f := by
      funext e
      exact (hf e).symm
    rw [heq]
    exact squareFreePathIntegral_grad f p
  have hq : squareFreePathIntegral η q = f u - f v := by
    have heq : η = (squareFreeGraph L).grad f := by
      funext e
      exact (hf e).symm
    rw [heq]
    exact squareFreePathIntegral_grad f q
  exact hp.trans hq.symm

/-- Specialization of the coefficient-independent gradient theorem to `ZMod n` edge fields. -/
theorem zmod_squareFreeEdgeField_isGradient
    {L n : ℕ} (η : SquareFreeEdge L → ZMod n)
    (hclosed : squareFreePlaquetteClosed η) :
    ∃ f : SquareFreeVertex L → ZMod n,
      ∀ e : SquareFreeEdge L, (squareFreeGraph L).grad f e = η e :=
  squareFreeEdgeField_isGradient η hclosed

end FroehlichSpencer.BKT.Clock.Peierls.GenericGradient

end
