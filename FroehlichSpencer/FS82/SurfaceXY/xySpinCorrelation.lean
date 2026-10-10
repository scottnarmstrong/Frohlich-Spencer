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
public import FroehlichSpencer.FS82.SurfaceXY.xySpinCharacter
public import FroehlichSpencer.FS82.SurfaceXY.xySpinDot

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceXY

noncomputable section
open Classical

def xySpinCorrelation {D : ℕ} {B : XYBox D} (β : ℝ) (x y : XYSite B) : ℝ :=
  (∫ θ : XYAngleConfig B,
      xyVillainDensity (B := B) β θ * xySpinDot θ x y ∂xyAngleHaarMeasure B) /
    xyVillainPartition (B := B) β

end
end FroehlichSpencer.FS82.SurfaceXY

end
