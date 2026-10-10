/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.SurfaceXY.XYBox

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceXY

noncomputable section
open Classical

def xyCubeFamily (D : ℕ) : ℕ → XYBox D := fun N _ => 2 * N

end
end FroehlichSpencer.FS82.SurfaceXY

end
