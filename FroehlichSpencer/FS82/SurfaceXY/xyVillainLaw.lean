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
public import FroehlichSpencer.FS82.SurfaceXY.xyBondDifference
public import FroehlichSpencer.FS82.SurfaceXY.xyCircleRepresentative
public import FroehlichSpencer.FS82.SurfaceXY.xyVillainWeight
public import FroehlichSpencer.FS82.SurfaceXY.xyAngleHaarMeasure
public import FroehlichSpencer.FS82.SurfaceXY.xyVillainDensity
public import FroehlichSpencer.FS82.SurfaceXY.xyVillainPartition

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceXY

noncomputable section
open Classical

def xyVillainLaw {D : ℕ} {B : XYBox D} (β : ℝ) (_hβ : 0 < β) : Measure (XYAngleConfig B) :=
  (xyAngleHaarMeasure B).withDensity (fun θ => ENNReal.ofReal
    (xyVillainDensity (B := B) β θ / xyVillainPartition (B := B) β))

end
end FroehlichSpencer.FS82.SurfaceXY

end
