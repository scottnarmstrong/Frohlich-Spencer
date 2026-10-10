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

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceZN

noncomputable section
open Classical

def axisBoundaryBasis {B : Box4} (c : Cell4 B) (i : Fin 4) : Chain4 B :=
  match c i with
  | Sum.inl _ => 0
  | Sum.inr e => ((-1 : ℤ) ^ cellRankBefore c i) •
      (basisChain (upperFace c i e) - basisChain (lowerFace c i e))

end
end FroehlichSpencer.FS82.SurfaceZN

end
