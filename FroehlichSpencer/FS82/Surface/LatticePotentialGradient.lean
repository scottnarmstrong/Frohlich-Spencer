/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.LatticeCoord
public import FroehlichSpencer.FS82.Surface.LatticeCell
public import FroehlichSpencer.FS82.Surface.LatticeVertices4

/-! FS82 source definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

noncomputable def latticePotentialGradient (γ : LatticeVertices4 → ℤ) (c : LatticeCell) : ℤ :=
  if _hdeg : (Finset.univ.filter fun i : Fin 4 => (c i).isRight).card = 1 then
    ∑ i : Fin 4, match c i with
      | Sum.inl _ => 0
      | Sum.inr t =>
        γ (fun j => if j = i then t + 1 else Sum.elim id id (c j)) -
          γ (fun j => if j = i then t else Sum.elim id id (c j))
  else 0

end FroehlichSpencer.FS82.Surface

end
