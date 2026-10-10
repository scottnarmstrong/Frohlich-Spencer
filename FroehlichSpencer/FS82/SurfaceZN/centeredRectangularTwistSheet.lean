/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.SurfaceZN.Box4
public import FroehlichSpencer.FS82.SurfaceZN.Cell4
public import FroehlichSpencer.FS82.SurfaceZN.Chain4
public import FroehlichSpencer.FS82.SurfaceZN.centeredCubeSide
public import FroehlichSpencer.FS82.SurfaceZN.vertexUpdate
public import FroehlichSpencer.FS82.SurfaceZN.edgeCell
public import FroehlichSpencer.FS82.SurfaceZN.rectangleBaseCell
public import FroehlichSpencer.FS82.SurfaceZN.rectangularTwistPlaquetteAt
public import FroehlichSpencer.FS82.SurfaceZN.centeredRectangularTwistPlaquette
public import FroehlichSpencer.FS82.SurfaceZN.rectangularTwistSheetSupport

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceZN

noncomputable section
open Classical

def centeredRectangularTwistSheet {L T M : ℕ}
    (hL : L ≤ M) (hT : T ≤ M) (hM : 0 < M) : Chain4 (centeredCubeSide M) :=
  Finsupp.equivFunOnFinite.symm (fun c =>
    if rectangularTwistSheetSupport (centeredRectangularTwistPlaquette hL hT hM) c
    then (1 : ℤ) else 0)

end
end FroehlichSpencer.FS82.SurfaceZN

end
