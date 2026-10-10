/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Lattice2D.SquareFree
public import FroehlichSpencer.BKT.Villain.CurrentFormula

/-!
# The wired square and its face dual

The wired box `Λ_L^zero` is represented by the free square `{0,…,L-1}²`, a wired root, and one
boundary edge for each side incidence. Its edge carrier is the edge carrier of the dual free
square of side `L+1`; each dual edge crosses exactly one wired primal edge. This is the planar
carrying convention in KP p. 2 and §6.1, pp. 32–33.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Duality

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Lattice2D

/-- Vertices of the wired square: a free square vertex or the single wired root. -/
abbrev WiredVertex (L : ℕ) := Option (SquareFreeVertex L)

/-- A wired edge is indexed by the unique dual edge it crosses. -/
abbrev WiredEdge (L : ℕ) := SquareFreeEdge (L + 1)

/-- The dual horizontal edge from `(i,j)` to `(i+1,j)`, where `i` is a free coordinate and `j`
may lie on the boundary row. -/
def horizontalDualEdgeData {L : ℕ} (i : Fin L) (j : Fin (L + 1)) :
    SquareFreeHorizontalEdge (L + 1) := by
  let i' := Fin.castLE (by omega : L ≤ L + 1) i
  have hi : i'.val + 1 < L + 1 := by rw [Fin.val_castLE]; omega
  exact ⟨⟨i', hi⟩, j⟩

/-- The horizontal dual edge from `(i,j)` to `(i+1,j)`, with its wired edge label. -/
def horizontalDualEdge {L : ℕ} (i : Fin L) (j : Fin (L + 1)) : WiredEdge L :=
  .inl (horizontalDualEdgeData i j)

/-- The dual vertical edge from `(i,j)` to `(i,j+1)`, where `j` is a free coordinate and `i`
may lie on the boundary column. -/
def verticalDualEdgeData {L : ℕ} (i : Fin (L + 1)) (j : Fin L) :
    SquareFreeVerticalEdge (L + 1) := by
  let j' := Fin.castLE (by omega : L ≤ L + 1) j
  have hj : j'.val + 1 < L + 1 := by rw [Fin.val_castLE]; omega
  exact ⟨i, ⟨j', hj⟩⟩

/-- The vertical dual edge from `(i,j)` to `(i,j+1)`, with its wired edge label. -/
def verticalDualEdge {L : ℕ} (i : Fin (L + 1)) (j : Fin L) : WiredEdge L :=
  .inr (verticalDualEdgeData i j)

/-- The horizontal coordinate of the face above a horizontal dual edge. -/
def horizontalFaceX {L : ℕ} (e : SquareFreeHorizontalEdge (L + 1)) : Fin L :=
  ⟨e.1.1.val, by have h := e.1.2; omega⟩

/-- The vertical coordinate of the face to the right of a vertical dual edge. -/
def verticalFaceY {L : ℕ} (e : SquareFreeVerticalEdge (L + 1)) : Fin L :=
  ⟨e.2.1.val, by have h := e.2.2; omega⟩

/-- The primal source face of a horizontal dual edge (the face on its left). -/
def horizontalPrimalSrc {L : ℕ} (e : SquareFreeHorizontalEdge (L + 1)) : WiredVertex L :=
  if h : e.2.val < L then some (horizontalFaceX e, ⟨e.2.val, h⟩) else none

/-- The primal target face of a horizontal dual edge (the face on its right). -/
def horizontalPrimalTgt {L : ℕ} (e : SquareFreeHorizontalEdge (L + 1)) : WiredVertex L :=
  if h : e.2.val = 0 then none
  else some (horizontalFaceX e, ⟨e.2.val - 1, by have h' := e.2.isLt; omega⟩)

/-- The primal source face of a vertical dual edge (the face on its left). -/
def verticalPrimalSrc {L : ℕ} (e : SquareFreeVerticalEdge (L + 1)) : WiredVertex L :=
  if h : e.1.val = 0 then none
  else some (⟨e.1.val - 1, by have h' := e.1.isLt; omega⟩, verticalFaceY e)

/-- The primal target face of a vertical dual edge (the face on its right). -/
def verticalPrimalTgt {L : ℕ} (e : SquareFreeVerticalEdge (L + 1)) : WiredVertex L :=
  if h : e.1.val < L then some (⟨e.1.val, h⟩, verticalFaceY e) else none

/-- Source endpoint in the wired primal graph, with the orientation dual to the positive
coordinate orientation of the free dual square. -/
def wiredBoxSrc {L : ℕ} : WiredEdge L → WiredVertex L
  | .inl e => horizontalPrimalSrc e
  | .inr e => verticalPrimalSrc e

/-- Target endpoint in the wired primal graph. -/
def wiredBoxTgt {L : ℕ} : WiredEdge L → WiredVertex L
  | .inl e => horizontalPrimalTgt e
  | .inr e => verticalPrimalTgt e

/-- KP's wired square, with one parallel boundary edge for each missing nearest-neighbour
incidence. The dual edge is the edge label, so multiplicity is retained exactly. -/
def wiredBoxGraph (L : ℕ) : Multigraph (WiredVertex L) (WiredEdge L) where
  src := wiredBoxSrc
  tgt := wiredBoxTgt
  src_ne_tgt := by
    intro e
    by_cases hL : L = 0
    · subst L
      cases e with
      | inl e => exact False.elim (by have h := e.1.2; omega)
      | inr e => exact False.elim (by have h := e.2.2; omega)
    · have hLpos : 0 < L := by omega
      cases e with
      | inl e =>
          by_cases hrow : e.2.val < L
          · by_cases hzero : e.2.val = 0
            · simp [wiredBoxSrc, wiredBoxTgt, horizontalPrimalSrc, horizontalPrimalTgt,
                hzero, hLpos]
            · simp [wiredBoxSrc, wiredBoxTgt, horizontalPrimalSrc, horizontalPrimalTgt,
                hrow, hzero]
              omega
          · have hlast : e.2.val = L := by have h := e.2.isLt; omega
            simp [wiredBoxSrc, wiredBoxTgt, horizontalPrimalSrc, horizontalPrimalTgt,
              hlast]
            omega
      | inr e =>
          by_cases hzero : e.1.val = 0
          · by_cases hlast : e.1.val < L
            · simp [wiredBoxSrc, wiredBoxTgt, verticalPrimalSrc, verticalPrimalTgt,
                hzero, hLpos]
            · simp [wiredBoxSrc, wiredBoxTgt, verticalPrimalSrc, verticalPrimalTgt,
                hzero, hLpos]
          · by_cases hlast : e.1.val < L
            · simp [wiredBoxSrc, wiredBoxTgt, verticalPrimalSrc, verticalPrimalTgt,
                hzero, hlast]
              omega
            · have hlast' : e.1.val = L := by have h := e.1.isLt; omega
              simp [wiredBoxSrc, wiredBoxTgt, verticalPrimalSrc, verticalPrimalTgt,
                hlast']
              omega

/-- The side-`L+1` dual square from KP §6.1, p. 32. Its vertices are the faces of the wired
primal graph, and its edges are in canonical bijection with wired primal edges. -/
def dualBoxGraph (L : ℕ) : Multigraph (SquareFreeVertex (L + 1)) (WiredEdge L) :=
  squareFreeGraph (L + 1)

end FroehlichSpencer.BKT.Duality

end
