/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.SurfaceZN.Box4
public import FroehlichSpencer.FS82.SurfaceZN.Cell4
public import FroehlichSpencer.FS82.SurfaceZN.centeredCubeSide
public import FroehlichSpencer.FS82.SurfaceZN.vertexUpdate
public import FroehlichSpencer.FS82.SurfaceZN.edgeCell
public import FroehlichSpencer.FS82.SurfaceZN.rectangleBaseCell
public import FroehlichSpencer.FS82.SurfaceZN.rectangularTwistPlaquetteAt

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceZN

noncomputable section
open Classical

def centeredRectangularTwistPlaquette {L T M : ℕ}
    (hL : L ≤ M) (hT : T ≤ M) (hM : 0 < M)
    (i : Fin L) (j : Fin T) : Cell4 (centeredCubeSide M) :=
  rectangularTwistPlaquetteAt (M + 1) (M + 1) M M
    (Nat.le_trans (Nat.add_le_add_left hL (M + 1))
      (Nat.le_of_eq ((Nat.add_right_comm M 1 M).trans (congrArg (· + 1) (Nat.two_mul M).symm))))
    (Nat.le_trans (Nat.add_le_add_left hT (M + 1))
      (Nat.le_of_eq ((Nat.add_right_comm M 1 M).trans (congrArg (· + 1) (Nat.two_mul M).symm))))
    (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hM) (Nat.le_of_eq (Nat.two_mul M).symm))
    (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hM) (Nat.le_of_eq (Nat.two_mul M).symm)) i j

end
end FroehlichSpencer.FS82.SurfaceZN

end
