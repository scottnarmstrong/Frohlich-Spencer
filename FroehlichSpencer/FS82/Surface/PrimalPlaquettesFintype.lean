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
public import FroehlichSpencer.FS82.Surface.PrimalCellDegree
public import FroehlichSpencer.FS82.Surface.PrimalPlaquettes

/-! FS82 perimeter surface definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

/-- Support instance: a box has finitely many plaquettes. -/
@[instance_reducible] noncomputable def primalPlaquettesFintype (R : RectBox4) : Fintype (PrimalPlaquettes R) := Fintype.ofFinite _
attribute [instance] primalPlaquettesFintype

end FroehlichSpencer.FS82.Surface

end
