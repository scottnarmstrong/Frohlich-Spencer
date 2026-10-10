/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Condition λ on the a priori weights of a lattice Coulomb gas -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- FS81's Condition λ (J p. 530) on the a priori weights `λ(q)`, `q ∈ ℤ`, of a lattice Coulomb
gas at inverse temperature `β`, with its constant `C` and its parameters `α` and `ε` explicit:
`ε < 1/16`, and for all `q ∈ ℤ`, a) `λ(q) = λ(-q)` (charge conjugation invariance) and
b) `|λ(q)| ≤ C exp[(α + εβ) q²]` (low density condition). -/
def IsConditionLambda (C α ε β : ℝ) (lam : ℤ → ℝ) : Prop :=
  ε < 1 / 16 ∧ ∀ q : ℤ, lam q = lam (-q) ∧ |lam q| ≤ C * Real.exp ((α + ε * β) * (q : ℝ) ^ 2)

end FroehlichSpencer.BKT

end
