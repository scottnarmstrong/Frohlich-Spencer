/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Periodic.TorusCohomology
public import FroehlichSpencer.BKT.Bridge.SquareCarriers

/-!
# The dual torus graph on KP's periodic square carrier

Quarter-turning the torus identifies its dual edges with the edges of the periodic square.

This module records that graph isomorphism and the signed transport of edge fields.

The signs are
retained explicitly because the carrier sorts endpoints lexicographically.
-/

@[expose] public section

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Lattice2D

namespace FroehlichSpencer.BKT.Rotator.Periodic

variable {L : ℕ}

/-- The quarter turn on the vertex torus. -/
def torusQuarterTurn (p : TorusVertex L) : TorusVertex L := (-p.2, p.1)

/-- The inverse quarter turn. -/
def torusQuarterTurnInv (p : TorusVertex L) : TorusVertex L := (p.2, -p.1)

/-- The quarter turn as a vertex equivalence. -/
def torusQuarterTurnEquiv : TorusVertex L ≃ TorusVertex L where
  toFun := torusQuarterTurn
  invFun := torusQuarterTurnInv
  left_inv := by
    intro p
    ext <;> simp [torusQuarterTurn, torusQuarterTurnInv]
  right_inv := by
    intro p
    ext <;> simp [torusQuarterTurn, torusQuarterTurnInv]

/-- The torus dual edge corresponding to a primal oriented edge after a quarter turn. -/
def torusDualEdgeTurn : TorusEdge L → TorusEdge L
  | (p, false) => (torusQuarterTurn p, false)
  | (p, true) => (torusQuarterTurn (p.1 - 1, p.2), true)

/-- The inverse edge relabeling for the quarter-turn duality. -/
def torusDualEdgeTurnInv : TorusEdge L → TorusEdge L
  | (p, false) => (torusQuarterTurnInv p, false)
  | (p, true) => (torusQuarterTurnInv (p.1, p.2 + 1), true)

/-- The quarter-turn dual edge relabeling is a bijection. -/
def torusDualEdgeTurnEquiv : TorusEdge L ≃ TorusEdge L where
  toFun := torusDualEdgeTurn
  invFun := torusDualEdgeTurnInv
  left_inv := by
    rintro ⟨p, d⟩
    cases d <;> ext <;> simp [torusDualEdgeTurn, torusDualEdgeTurnInv,
      torusQuarterTurn, torusQuarterTurnInv]
  right_inv := by
    rintro ⟨p, d⟩
    cases d <;> ext <;> simp [torusDualEdgeTurn, torusDualEdgeTurnInv,
      torusQuarterTurn, torusQuarterTurnInv]

/-- The dual torus graph whose oriented edge gradient is exactly `torusDualGradient`. -/
def torusDualGraph (hL : 2 < L) : Multigraph (TorusVertex L) (TorusEdge L) where
  src e := torusQuarterTurnEquiv.symm ((torusGraph L hL).src (torusDualEdgeTurn e))
  tgt e := torusQuarterTurnEquiv.symm ((torusGraph L hL).tgt (torusDualEdgeTurn e))
  src_ne_tgt e h := by
    apply (torusGraph L hL).src_ne_tgt (torusDualEdgeTurn e)
    exact torusQuarterTurnEquiv.symm.injective h

/-- The real-valued dual height gradient. -/
def torusDualGradientReal (h : TorusVertex L → ℝ) : TorusEdge L → ℝ
  | (p, false) => h p - h (p.1, p.2 - 1)
  | (p, true) => h (p.1 - 1, p.2) - h p

/-- The dual graph gradient in the edge orientation induced by `torusDualEdgeTurn`. -/
theorem torusDualGraph_grad_eq_torusDualGradientReal (hL : 2 < L)
    (h : TorusVertex L → ℝ) (e : TorusEdge L) :
    (torusDualGraph hL).grad h e = torusDualGradientReal h e := by
  cases e with
  | mk p d =>
    cases d
    · simp [Multigraph.grad, torusDualGraph, torusDualEdgeTurn,
        torusQuarterTurn, torusQuarterTurnInv, torusQuarterTurnEquiv,
        torusDualGradientReal, torusGraph, torusStep]
      congr 1
      abel_nf
    · simp [Multigraph.grad, torusDualGraph, torusDualEdgeTurn,
        torusQuarterTurn, torusQuarterTurnInv, torusQuarterTurnEquiv,
        torusDualGradientReal, torusGraph, torusStep]

/--
The dual graph isomorphism to the periodic square carrier.
-/
noncomputable def torusDualSquareIso [NeZero L] (hL : 2 < L) :
    Multigraph.Isomorphism (torusDualGraph hL) (squarePeriodic L) where
  vertices := torusQuarterTurnEquiv.trans (squareTorusVertexEquiv L).symm
  edges := torusDualEdgeTurnEquiv.trans (torusGraphToSquarePeriodicIso hL).edges
  endpoints e := by
    have ht := (torusGraphToSquarePeriodicIso hL).endpoints (torusDualEdgeTurn e)
    simpa [torusDualGraph, torusDualEdgeTurnEquiv, torusQuarterTurnEquiv,
      torusQuarterTurn, torusQuarterTurnInv, torusGraphToSquarePeriodicIso,
      Equiv.trans_apply] using ht

/--
Signed transport of a real dual-edge field to the sorted  carrier.
-/
noncomputable def torusDualFieldToSquare [NeZero L] (hL : 2 < L) (f : TorusEdge L → ℝ) :
    SquarePeriodicEdge L → ℝ := by
  classical
  let I := torusDualSquareIso hL
  exact fun e =>
    if currentSameOrientation I (I.edges.symm e) then
      f (I.edges.symm e) else -f (I.edges.symm e)

/--
Pulling a square-periodic gradient back through the dual carrier gives the corresponding
torus-dual gradient, with the orientation sign restored.
-/
theorem torusDualFieldToSquare_grad [NeZero L] (hL : 2 < L) (h : TorusVertex L → ℝ)
    (e : TorusEdge L) :
    torusDualFieldToSquare hL ((torusDualGraph hL).grad h) ((torusDualSquareIso hL).edges e) =
      (squarePeriodic L).grad ((torusDualSquareIso hL).pushField h) ((torusDualSquareIso hL).edges e) := by
  let I := torusDualSquareIso hL
  classical
  rcases I.endpoints e with he | he
  · have hsame : currentSameOrientation I e := by
      simp [currentSameOrientation, he]
    have hfield :
        torusDualFieldToSquare hL ((torusDualGraph hL).grad h) (I.edges e) =
          (torusDualGraph hL).grad h e := by
      simp [torusDualFieldToSquare, I, hsame]
    have hright :
        (squarePeriodic L).grad (I.pushField h) (I.edges e) =
          (torusDualGraph hL).grad h e := by
      simp [Multigraph.grad, Multigraph.Isomorphism.pushField, he]
    exact hfield.trans hright.symm
  · have hsame : ¬ currentSameOrientation I e := by
      intro hh
      have hv : (torusDualGraph hL).src e = (torusDualGraph hL).tgt e :=
        I.vertices.injective (hh.1.symm.trans he.1)
      exact (torusDualGraph hL).src_ne_tgt e hv
    have hfield :
        torusDualFieldToSquare hL ((torusDualGraph hL).grad h) (I.edges e) =
          -(torusDualGraph hL).grad h e := by
      simp [torusDualFieldToSquare, I, hsame]
    have hright :
        (squarePeriodic L).grad (I.pushField h) (I.edges e) =
          -(torusDualGraph hL).grad h e := by
      simp [Multigraph.grad, Multigraph.Isomorphism.pushField, he]
    exact hfield.trans hright.symm

end FroehlichSpencer.BKT.Rotator.Periodic

end
