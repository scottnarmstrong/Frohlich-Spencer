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
public import FroehlichSpencer.FS82.SurfaceXY.xyBasisChain
public import FroehlichSpencer.FS82.SurfaceXY.xyLowerFace
public import FroehlichSpencer.FS82.SurfaceXY.xyUpperFace

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceXY

noncomputable section
open Classical

def xyAxisBoundaryBasis {D : ℕ} {B : XYBox D} (c : XYCell B) (i : Fin D) : XYChain B :=
  match c i with
    | Sum.inl _ => 0
    | Sum.inr e =>
        ((-1 : ℤ) ^ xyCellRankBefore c i) •
          (xyBasisChain (xyUpperFace c i e) - xyBasisChain (xyLowerFace c i e))

end
end FroehlichSpencer.FS82.SurfaceXY

end
