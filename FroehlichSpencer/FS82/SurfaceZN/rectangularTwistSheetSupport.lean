/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.SurfaceZN.Box4
public import FroehlichSpencer.FS82.SurfaceZN.Cell4

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceZN

noncomputable section
open Classical

def rectangularTwistSheetSupport {B : Box4} {L T : ℕ}
    (plaq : Fin L → Fin T → Cell4 B) (c : Cell4 B) : Prop := ∃ i j, plaq i j = c

end
end FroehlichSpencer.FS82.SurfaceZN

end
