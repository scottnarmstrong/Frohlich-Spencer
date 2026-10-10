/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.SurfaceXY.XYBox
public import FroehlichSpencer.FS82.SurfaceXY.XYCoord

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceXY

noncomputable section
open Classical

abbrev xyCoordIsEdge {D : ℕ} {B : XYBox D} {i : Fin D} (x : XYCoord B i) : Prop := x.isRight

end
end FroehlichSpencer.FS82.SurfaceXY

end
