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
public import FroehlichSpencer.FS82.SurfaceZN.cellAxes
public import FroehlichSpencer.FS82.SurfaceZN.cellDegree
public import FroehlichSpencer.FS82.SurfaceZN.basisChain
public import FroehlichSpencer.FS82.SurfaceZN.vertexUpdate
public import FroehlichSpencer.FS82.SurfaceZN.lowerFace
public import FroehlichSpencer.FS82.SurfaceZN.upperFace
public import FroehlichSpencer.FS82.SurfaceZN.axisBoundaryBasis
public import FroehlichSpencer.FS82.SurfaceZN.axisBoundary
public import FroehlichSpencer.FS82.SurfaceZN.boundary
public import FroehlichSpencer.FS82.SurfaceZN.Links
public import FroehlichSpencer.FS82.SurfaceZN.Plaquettes
public import FroehlichSpencer.FS82.SurfaceZN.Config
public import FroehlichSpencer.FS82.SurfaceZN.circleChainPairing
public import FroehlichSpencer.FS82.SurfaceZN.primalCircleCochain
public import FroehlichSpencer.FS82.SurfaceZN.primalPlaquetteFlux

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceZN

noncomputable section
open Classical

def disorderTwistedFlux {B : Box4} (N ξ : ℕ) (S : Chain4 B)
    (θ : Config B) (p : Plaquettes B) : UnitAddCircle :=
  primalPlaquetteFlux θ p + ((((S p.1 : ℝ) * (ξ : ℝ) / (N : ℝ)) : ℝ) : UnitAddCircle)

end
end FroehlichSpencer.FS82.SurfaceZN

end
