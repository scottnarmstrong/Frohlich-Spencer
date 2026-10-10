/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Fintype.Prod

/-! # Edges of the free square domain -/

@[expose] public section

namespace FroehlichSpencer.BKT

/--
The edges of `Λ_L^free` (KP p. 2): the pairs `{(a, b), (c, d)}` of points of
`{0, …, L - 1}²` with `{|a - c|, |b - d|} = {0, 1}`.
-/
abbrev SquareFreeEdge (L : ℕ) : Type :=
  {p : (Fin L × Fin L) × (Fin L × Fin L) //
    toLex p.1 < toLex p.2 ∧
      ({|((p.1.1 : ℕ) : ℤ) - (p.2.1 : ℕ)|, |((p.1.2 : ℕ) : ℤ) - (p.2.2 : ℕ)|} : Finset ℤ) = {0, 1}}

end FroehlichSpencer.BKT

end
