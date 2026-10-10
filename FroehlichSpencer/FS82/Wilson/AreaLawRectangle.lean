/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.DualityFinite

/-!
# Finite rectangular Wilson sheets

The rectangle is based at the origin in the `0–1` coordinate plane. Its loop
is the cubical boundary of the oriented sum of its `L × T` plaquettes.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

/-- The lower corner of the origin-based rectangle. -/
@[expose] def wilsonRectangleBaseCell (B : Box 4) : Cell 4 B := fun i =>
  Sum.inl ⟨0, Nat.zero_lt_succ (B i)⟩

/-- The positively oriented `0–1` plaquette based at `(i,j,0,0)`. -/
@[expose] def wilsonRectanglePlaquette {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (i : Fin L) (j : Fin T) : Cell 4 B :=
  edgeCell (edgeCell (wilsonRectangleBaseCell B) 0 (Fin.castLE hL i))
    1 (Fin.castLE hT j)

/-- The oriented rectangular plaquette sheet with `L*T` unit faces. -/
@[expose] noncomputable def wilsonRectangleSheet {B : Box 4} (L T : ℕ)
    (hL : L ≤ B 0) (hT : T ≤ B 1) : Chain 4 B :=
  ∑ x : Fin L × Fin T,
    basisChain (wilsonRectanglePlaquette hL hT x.1 x.2)

/-- The finite Wilson loop bounding the rectangular sheet. -/
@[expose] noncomputable def wilsonRectangleLoop {B : Box 4} (L T : ℕ)
    (hL : L ≤ B 0) (hT : T ≤ B 1) : Chain 4 B :=
  boundary (wilsonRectangleSheet L T hL hT)

/-- Distinct unit squares in the rectangle have distinct cubical carriers. -/
theorem wilsonRectanglePlaquette_injective {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) :
    Function.Injective (fun x : Fin L × Fin T =>
      wilsonRectanglePlaquette hL hT x.1 x.2) := by
  intro x y hxy
  apply Prod.ext
  · apply Fin.ext
    have h := congrFun hxy (0 : Fin 4)
    change Sum.inr (Fin.castLE hL x.1) = Sum.inr (Fin.castLE hL y.1) at h
    have hv := congrArg Fin.val (Sum.inr.inj h)
    simpa using hv
  · apply Fin.ext
    have h := congrFun hxy (1 : Fin 4)
    change Sum.inr (Fin.castLE hT x.2) = Sum.inr (Fin.castLE hT y.2) at h
    have hv := congrArg Fin.val (Sum.inr.inj h)
    simpa using hv

end FroehlichSpencer.FS82.Wilson

end
