/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.RectBox4
public import FroehlichSpencer.FS82.Surface.LatticeVertices4

/-! FS82 source definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

def isExteriorVertex (R : RectBox4) (x : LatticeVertices4) : Prop :=
  ∃ i : Fin 4, x i ≤ R.origin i ∨ R.origin i + R.side i < x i

end FroehlichSpencer.FS82.Surface

end
