/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.SurfaceZN.Box4
public import FroehlichSpencer.FS82.SurfaceZN.Cell4
public import FroehlichSpencer.FS82.SurfaceZN.vertexUpdate
public import FroehlichSpencer.FS82.SurfaceZN.edgeCell
public import FroehlichSpencer.FS82.SurfaceZN.rectangleBaseCell

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceZN

noncomputable section
open Classical

def rectangularTwistPlaquetteAt {B : Box4} {L T : ℕ}
    (x₀ x₁ x₂ x₃ : ℕ)
    (hx₀ : x₀ + L ≤ B 0 + 1) (hx₁ : x₁ + T ≤ B 1 + 1)
    (hx₂ : x₂ < B 2) (hx₃ : x₃ < B 3)
    (i : Fin L) (j : Fin T) : Cell4 B :=
  edgeCell (edgeCell
    (vertexUpdate (vertexUpdate (rectangleBaseCell B) 0 ⟨x₀ + i.val, by omega⟩)
      1 ⟨x₁ + j.val, by omega⟩)
    2 ⟨x₂, hx₂⟩) 3 ⟨x₃, hx₃⟩

end
end FroehlichSpencer.FS82.SurfaceZN

end
