/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.SurfaceXY.XYBox
public import FroehlichSpencer.FS82.SurfaceXY.XYCoord
public import FroehlichSpencer.FS82.SurfaceXY.XYCell

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceXY

noncomputable section
open Classical

def xyLowerFace {D : ℕ} {B : XYBox D} (c : XYCell B) (i : Fin D) (e : Fin (B i)) : XYCell B :=
  Function.update c i (Sum.inl ⟨e.val, Nat.lt_succ_of_le e.isLt.le⟩)

end
end FroehlichSpencer.FS82.SurfaceXY

end
