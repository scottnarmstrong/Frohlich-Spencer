/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.RectBox4
public import FroehlichSpencer.FS82.Surface.PrimalCoord
public import FroehlichSpencer.FS82.Surface.PrimalCell

/-! FS82 perimeter surface definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

/-- The dimension of a cell: the number of its interval coordinates. -/
def primalCellDegree (R : RectBox4) (c : PrimalCell R) : ℕ :=
  (Finset.univ.filter fun i : Fin 4 => (c i).isRight).card

end FroehlichSpencer.FS82.Surface

end
