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
public import FroehlichSpencer.FS82.Surface.DualCellDecidableEq
public import FroehlichSpencer.FS82.Surface.DualLinks

/-! FS82 source definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

@[instance_reducible] def dualLinksDecidableEq (R : RectBox4) : DecidableEq (DualLinks R) := inferInstance
attribute [instance] dualLinksDecidableEq

end FroehlichSpencer.FS82.Surface

end
