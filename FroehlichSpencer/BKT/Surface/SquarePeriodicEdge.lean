/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Fintype.Prod

/-! # Edges of the periodic square domain -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The edges of `Λ_L^per` (KP p. 2): the pairs `{(a, b), (c, d)}` of points of
`{0, …, L - 1}²` that are equal in one coordinate and differ by exactly one modulo `L` in the
other. Each unordered pair is listed once, as the ordered pair whose first point is
lexicographically smaller (so `Λ_2^per` is the 4-cycle, as in KP's definition by pairs). -/
abbrev SquarePeriodicEdge (L : ℕ) : Type :=
  {p : (Fin L × Fin L) × (Fin L × Fin L) //
    toLex p.1 < toLex p.2 ∧
      ((p.1.1 = p.2.1 ∧ (((p.1.2 : ℕ) : ℤ) ≡ (p.2.2 : ℕ) + 1 [ZMOD L] ∨
          ((p.2.2 : ℕ) : ℤ) ≡ (p.1.2 : ℕ) + 1 [ZMOD L])) ∨
        (p.1.2 = p.2.2 ∧ (((p.1.1 : ℕ) : ℤ) ≡ (p.2.1 : ℕ) + 1 [ZMOD L] ∨
          ((p.2.1 : ℕ) : ℤ) ≡ (p.1.1 : ℕ) + 1 [ZMOD L])))}

end FroehlichSpencer.BKT

end
