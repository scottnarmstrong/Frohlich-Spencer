/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.RectBox4
public import FroehlichSpencer.FS82.Surface.PrimalCoord

/-! FS82 perimeter surface definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

/-- A cell of the box: a site coordinate or a unit interval on each of the four axes. -/
abbrev PrimalCell (R : RectBox4) := (i : Fin 4) → PrimalCoord R i

end FroehlichSpencer.FS82.Surface

end
