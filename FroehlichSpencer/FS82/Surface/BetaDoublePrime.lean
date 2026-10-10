/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib

/-! FS82 source definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

def betaDoublePrime (cPack : ℝ → ℝ) (β : ℝ) : ℝ :=
  β * (1 - 2 * β * cPack β)

end FroehlichSpencer.FS82.Surface

end
