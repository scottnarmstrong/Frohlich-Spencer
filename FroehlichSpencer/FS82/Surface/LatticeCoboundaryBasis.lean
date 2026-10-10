/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.LatticeCoord
public import FroehlichSpencer.FS82.Surface.LatticeCell
public import FroehlichSpencer.FS82.Surface.LatticeChain
public import FroehlichSpencer.FS82.Surface.LatticeIsEdge
public import FroehlichSpencer.FS82.Surface.LatticeRankBefore
public import FroehlichSpencer.FS82.Surface.LatticeBasis
public import FroehlichSpencer.FS82.Surface.LatticeEdgeCell

/-! FS82 source definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

noncomputable def latticeCoboundaryBasis (c : LatticeCell) : LatticeChain :=
  ∑ i : Fin 4, match c i with
    | Sum.inr _ => 0
    | Sum.inl t =>
        ((-1 : ℤ) ^ latticeRankBefore c i) •
          (latticeBasis (latticeEdgeCell c i (t - 1)) - latticeBasis (latticeEdgeCell c i t))

end FroehlichSpencer.FS82.Surface

end
