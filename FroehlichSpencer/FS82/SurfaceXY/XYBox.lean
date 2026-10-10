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

abbrev XYBox (D : ℕ) := Fin D → ℕ

end
end FroehlichSpencer.FS82.SurfaceXY

end
