/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Duality.WiredBox

/-!
# Free finite spin box and its dual-face carriers

The box has spin sites `{0,…,L}²` and all internal nearest-neighbour bonds. Its bounded dual faces
are `{0,…,L-1}²`; `none` denotes the single exterior face. The current convention below is the
source orientation in FS81 (A.3): the current on an oriented primal bond is the height on its
left face minus the height on its right face (J pp. 534, 595–596).
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Rotator

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Duality
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Villain

variable {L : ℕ}

/-- Spin sites in the free square box of side `L + 1`. -/
abbrev RotatorSpinSite (L : ℕ) := SquareFreeVertex (L + 1)

/-- Internal bonds in the free square box, each represented once and positively oriented. -/
abbrev RotatorInternalBond (L : ℕ) := SquareFreeEdge (L + 1)

/-- Bounded dual faces and the unique exterior face. -/
abbrev RotatorDualFace (L : ℕ) := WiredVertex L

/-- The free finite spin box with all internal nearest-neighbour bonds. -/
def rotatorFreeGraph (L : ℕ) : Multigraph (RotatorSpinSite L) (RotatorInternalBond L) :=
  squareFreeGraph (L + 1)

/-- The planar dual graph: each internal spin bond crosses exactly one dual edge, and the
exterior is represented by `none`. -/
def rotatorDualGraph (L : ℕ) : Multigraph (RotatorDualFace L) (RotatorInternalBond L) :=
  wiredBoxGraph L

/-- An integer height on dual faces, pinned to zero on the exterior face. -/
abbrev RotatorFaceHeight (L : ℕ) :=
  {h : RotatorDualFace L → ℤ // h none = 0}

/-- Divergence of an integer current on the free spin box, with outgoing bonds counted positively.
-/
def rotatorCurrentDivergence (q : RotatorInternalBond L → ℤ) (x : RotatorSpinSite L) : ℤ :=
  currentDivergence (rotatorFreeGraph L) q x

/-- The current induced by a zero-exterior dual-face height. The sign is `height(src) -
height(tgt)`, matching FS81 (A.3) in the positive-coordinate bond orientation. -/
def rotatorFaceHeightCurrent (h : RotatorFaceHeight L) (e : RotatorInternalBond L) : ℤ :=
  h.1 ((rotatorDualGraph L).src e) - h.1 ((rotatorDualGraph L).tgt e)

/-- The admissible currents in the free spin box. -/
def RotatorNeutralCurrent (L : ℕ) :=
  {q : RotatorInternalBond L → ℤ // ∀ x, rotatorCurrentDivergence q x = 0}

/-- The oriented edge-current formula from FS81 (A.3), stated using the dual graph endpoints. -/
theorem rotatorFaceHeightCurrent_sourceOrientation (h : RotatorFaceHeight L)
    (e : RotatorInternalBond L) :
    rotatorFaceHeightCurrent h e =
      h.1 ((rotatorDualGraph L).src e) - h.1 ((rotatorDualGraph L).tgt e) := rfl

end FroehlichSpencer.BKT.Rotator

end
