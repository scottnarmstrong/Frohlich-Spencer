/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.RectBox4

/-! FS82 perimeter surface definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

/-- One coordinate of a cell of the box `Λ` of `R`, the sites `x` with
`origin i ≤ x i ≤ origin i + side i` (FS82 (2.3): "a finite, rectangular array of sites"):
`Sum.inl v` is the site coordinate `origin i + v`, and `Sum.inr e` is the unit interval from
`origin i + e` to `origin i + e + 1`. -/
abbrev PrimalCoord (R : RectBox4) (i : Fin 4) :=
  Sum (Fin (R.side i + 1)) (Fin (R.side i))

end FroehlichSpencer.FS82.Surface

end
