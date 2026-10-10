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
public import FroehlichSpencer.FS82.SurfaceZN.coordIsEdge
public import FroehlichSpencer.FS82.SurfaceZN.cellRankBefore
public import FroehlichSpencer.FS82.SurfaceZN.basisChain
public import FroehlichSpencer.FS82.SurfaceZN.vertexUpdate
public import FroehlichSpencer.FS82.SurfaceZN.lowerFace
public import FroehlichSpencer.FS82.SurfaceZN.upperFace
public import FroehlichSpencer.FS82.SurfaceZN.axisBoundaryBasis
public import FroehlichSpencer.FS82.SurfaceZN.axisBoundary

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceZN

noncomputable section
open Classical

def boundary {B : Box4} : Chain4 B →ₗ[ℤ] Chain4 B :=
  ∑ i : Fin 4, axisBoundary i

end
end FroehlichSpencer.FS82.SurfaceZN

end
