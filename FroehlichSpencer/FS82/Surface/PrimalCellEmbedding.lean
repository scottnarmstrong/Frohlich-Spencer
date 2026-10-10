/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.RectBox4
public import FroehlichSpencer.FS82.Surface.LatticeCoord
public import FroehlichSpencer.FS82.Surface.LatticeCell
public import FroehlichSpencer.FS82.Surface.PrimalCoord
public import FroehlichSpencer.FS82.Surface.PrimalCell

/-! FS82 perimeter surface definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

/-- The lattice cell of a cell of the box. -/
def primalCellEmbedding (R : RectBox4) (c : PrimalCell R) : LatticeCell :=
  fun i => match c i with
    | Sum.inl v => Sum.inl (R.origin i + v.val)
    | Sum.inr e => Sum.inr (R.origin i + e.val)

end FroehlichSpencer.FS82.Surface

end
