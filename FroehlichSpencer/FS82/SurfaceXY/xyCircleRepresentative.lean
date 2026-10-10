/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceXY

noncomputable section
open Classical

def xyCircleRepresentative (z : UnitAddCircle) : ℝ :=
  letI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  (AddCircle.equivIoc (1 : ℝ) (-1 / 2) z).1

end
end FroehlichSpencer.FS82.SurfaceXY

end
