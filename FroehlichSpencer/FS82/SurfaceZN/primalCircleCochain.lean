/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.SurfaceZN.Box4
public import FroehlichSpencer.FS82.SurfaceZN.Cell4
public import FroehlichSpencer.FS82.SurfaceZN.coordIsEdge
public import FroehlichSpencer.FS82.SurfaceZN.cellAxes
public import FroehlichSpencer.FS82.SurfaceZN.cellDegree
public import FroehlichSpencer.FS82.SurfaceZN.Links
public import FroehlichSpencer.FS82.SurfaceZN.Config

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceZN

noncomputable section
open Classical

def primalCircleCochain {B : Box4} (θ : Config B) : Cell4 B → UnitAddCircle := fun c =>
  if h : cellDegree c = 1 then θ ⟨c, h⟩ else 0

end
end FroehlichSpencer.FS82.SurfaceZN

end
