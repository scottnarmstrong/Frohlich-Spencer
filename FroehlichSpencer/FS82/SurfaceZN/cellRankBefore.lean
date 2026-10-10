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

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceZN

noncomputable section
open Classical

def cellRankBefore {B : Box4} (c : Cell4 B) (i : Fin 4) : ℕ :=
  (Finset.univ.filter fun j : Fin 4 => j < i ∧ coordIsEdge (c j)).card

end
end FroehlichSpencer.FS82.SurfaceZN

end
