/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Data.Fin.Basic

/-! # Lattice sites -/

public section

namespace FroehlichSpencer

/-- The sites of the lattice ℤ^ν. -/
abbrev Site (ν : ℕ) := Fin ν → ℤ

end FroehlichSpencer


end
