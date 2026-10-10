/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.RectBox4
public import FroehlichSpencer.FS82.Surface.RectBox4ShortestSide
public import FroehlichSpencer.FS82.Surface.RectBox4LongestSide

/-! FS82 source definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

def IsLogThickRectBox4 (R : RectBox4) : Prop :=
  Real.log ((R.longestSide + 1 : ℕ) : ℝ) ≤ (R.shortestSide : ℝ)

end FroehlichSpencer.FS82.Surface

end
