/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.RectBox4
public import FroehlichSpencer.FS82.Surface.DualCoord
public import FroehlichSpencer.FS82.Surface.DualCell
public import FroehlichSpencer.FS82.Surface.DualCellAxes
public import FroehlichSpencer.FS82.Surface.DualCellDegree
public import FroehlichSpencer.FS82.Surface.DualPlaquettes
public import FroehlichSpencer.FS82.Surface.LatticeCoord
public import FroehlichSpencer.FS82.Surface.LatticeCell
public import FroehlichSpencer.FS82.Surface.LatticeChain
public import FroehlichSpencer.FS82.Surface.DualEmbedCoordC1
public import FroehlichSpencer.FS82.Surface.DualCellEmbeddingC1
public import FroehlichSpencer.FS82.Surface.LatticeIsEdge
public import FroehlichSpencer.FS82.Surface.LatticeRankBefore
public import FroehlichSpencer.FS82.Surface.LatticeBasis
public import FroehlichSpencer.FS82.Surface.LatticeEdgeCell
public import FroehlichSpencer.FS82.Surface.LatticeCoboundaryBasis
public import FroehlichSpencer.FS82.Surface.LatticeCoboundary

/-! FS82 source definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

abbrev SourceClosedIntegerCurrent (R : RectBox4) :=
  {q : LatticeChain // latticeCoboundary q = 0 ∧
    ∀ c : LatticeCell, c ∈ q.support →
      ∃ p : DualPlaquettes R, dualCellEmbeddingC1 R p.1 = c}

end FroehlichSpencer.FS82.Surface

end
