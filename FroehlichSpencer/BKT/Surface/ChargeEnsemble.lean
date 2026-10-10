/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.Group.Support
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Basic

/-! # Ensembles of charge densities (KP §1.7.1) -/

@[expose] public section

namespace FroehlichSpencer.BKT

universe u

/-- An ensemble (KP p. 5): a finite (possibly empty) collection of charge densities
`ϱ : V → ℤ` (functions that are not identically zero) whose supports are mutually disjoint. -/
def IsChargeEnsemble {V : Type u} (N : Finset (V → ℤ)) : Prop :=
  (∀ ϱ ∈ N, ϱ ≠ 0) ∧
    ∀ ϱ₁ ∈ N, ∀ ϱ₂ ∈ N, ϱ₁ ≠ ϱ₂ → Disjoint (Function.support ϱ₁) (Function.support ϱ₂)

end FroehlichSpencer.BKT

end
