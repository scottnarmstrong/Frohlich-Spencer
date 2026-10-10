/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Basic.Real.Basic
public import FroehlichSpencer.Surface.Site

/-! # Configuration space -/

public section

namespace FroehlichSpencer

/-- The space of real-valued potential configurations on `ℤ^ν`. -/
abbrev Configuration (ν : ℕ) := Site ν → ℝ

end FroehlichSpencer


end
