/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.RectBox4

/-! FS82 perimeter surface definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

/-- The box of the cube of sites `[-N, N]⁴`, `N ≥ 1`. -/
def centredCube (N : ℕ) (hN : 0 < N) : RectBox4 where
  origin := fun _ => -(N : ℤ)
  side := fun _ => 2 * N
  side_pos := fun _ => Nat.mul_pos Nat.zero_lt_two hN

end FroehlichSpencer.FS82.Surface

end
