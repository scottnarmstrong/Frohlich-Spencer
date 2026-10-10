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
public import FroehlichSpencer.FS82.SurfaceXY.XYChain
public import FroehlichSpencer.FS82.SurfaceXY.xyCoordIsEdge
public import FroehlichSpencer.FS82.SurfaceXY.xyCellRankBefore
public import FroehlichSpencer.FS82.SurfaceXY.xyCellAxes
public import FroehlichSpencer.FS82.SurfaceXY.xyCellDegree
public import FroehlichSpencer.FS82.SurfaceXY.XYSite
public import FroehlichSpencer.FS82.SurfaceXY.XYBond
public import FroehlichSpencer.FS82.SurfaceXY.XYAngleConfig
public import FroehlichSpencer.FS82.SurfaceXY.xyBasisChain
public import FroehlichSpencer.FS82.SurfaceXY.xyLowerFace
public import FroehlichSpencer.FS82.SurfaceXY.xyUpperFace
public import FroehlichSpencer.FS82.SurfaceXY.xyAxisBoundaryBasis
public import FroehlichSpencer.FS82.SurfaceXY.xyAxisBoundary
public import FroehlichSpencer.FS82.SurfaceXY.xyBoundary
public import FroehlichSpencer.FS82.SurfaceXY.xyCircleChainPairing
public import FroehlichSpencer.FS82.SurfaceXY.xyAngleCochain

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceXY

noncomputable section
open Classical

def xyBondDifference {D : ℕ} {B : XYBox D}
    (θ : XYAngleConfig B) (b : XYBond B) : UnitAddCircle :=
  xyCircleChainPairing (xyBoundary (Finsupp.single b.1 1)) (xyAngleCochain θ)

end
end FroehlichSpencer.FS82.SurfaceXY

end
