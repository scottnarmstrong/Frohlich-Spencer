/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.LatticeCoord
public import FroehlichSpencer.FS82.Surface.LatticeCell
public import FroehlichSpencer.FS82.Surface.LatticeChain

/-! FS82 perimeter surface definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

/-- The rectangular loop `ℒ_{L×T}` (FS82 §1 and (2.5)) in the 0–1 lattice plane, with corners
`(0,0)`, `(L,0)`, `(L,T)`, `(0,T)` at `x₂ = x₃ = 0`, as an integer chain of links: `+1` on the links
from `(0,0)` to `(L,0)` and from `(L,0)` to `(L,T)`, and `-1` on the links of the sides from `(0,T)`
to `(L,T)` and from `(0,0)` to `(0,T)`. -/
noncomputable def rectangularLoop (L T : ℕ) : LatticeChain :=
  (∑ k ∈ Finset.range L,
      (Finsupp.single (![Sum.inr (k : ℤ), Sum.inl 0, Sum.inl 0, Sum.inl 0] : LatticeCell) (1 : ℤ) -
        Finsupp.single (![Sum.inr (k : ℤ), Sum.inl (T : ℤ), Sum.inl 0, Sum.inl 0] : LatticeCell)
          (1 : ℤ))) +
  ∑ k ∈ Finset.range T,
      (Finsupp.single (![Sum.inl (L : ℤ), Sum.inr (k : ℤ), Sum.inl 0, Sum.inl 0] : LatticeCell) (1 : ℤ) -
        Finsupp.single (![Sum.inl 0, Sum.inr (k : ℤ), Sum.inl 0, Sum.inl 0] : LatticeCell) (1 : ℤ))

end FroehlichSpencer.FS82.Surface

end
