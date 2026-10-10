/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.SurfaceXY.XYBox
public import FroehlichSpencer.FS82.SurfaceXY.XYCoord
public import FroehlichSpencer.FS82.SurfaceXY.XYCell
public import FroehlichSpencer.FS82.SurfaceXY.xyCoordIsEdge
public import FroehlichSpencer.FS82.SurfaceXY.xyCellAxes
public import FroehlichSpencer.FS82.SurfaceXY.xyCellDegree
public import FroehlichSpencer.FS82.SurfaceXY.XYSite
public import FroehlichSpencer.FS82.SurfaceXY.XYAngleConfig

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceXY

noncomputable section
open Classical

def xySpinCharacter {D : ℕ} {B : XYBox D}
    (θ : XYAngleConfig B) (x y : XYSite B) : ℂ :=
  fourier (T := (1 : ℝ)) 1 (θ x - θ y)

end
end FroehlichSpencer.FS82.SurfaceXY

end
