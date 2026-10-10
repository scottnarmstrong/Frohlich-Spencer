/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.FreeBox

/-!
# Positive nearest-neighbour steps in `ℤ²`

A bond of a finite domain `Λ ⊆ ℤ²` with free boundary conditions is an ordered pair of sites of `Λ`
whose second entry is the first plus a positive coordinate unit vector; each nearest-neighbour pair
`(ij) ⊂ Λ` of FS81 (1.26), J p. 533, is listed exactly once. The square `{0, …, L}²` is the
`ℤ²` copy of the free spin box `RotatorSpinSite L`.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Rotator.Ginibre

/-- `y` is the right or upper nearest neighbour of `x` in `ℤ²`. -/
def LatticeStep (x y : ℤ × ℤ) : Prop :=
  y = x + (1, 0) ∨ y = x + (0, 1)

instance : DecidableRel LatticeStep := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The square `{0, …, L}²` in `ℤ²`. -/
def squareBoxZ (L : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (0 : ℤ) L ×ˢ Finset.Icc (0 : ℤ) L

/-- The `ℤ²` position of a site of the free spin box. -/
def siteToZ {L : ℕ} (p : RotatorSpinSite L) : ℤ × ℤ :=
  ((p.1 : ℕ), (p.2 : ℕ))

end FroehlichSpencer.BKT.Rotator.Ginibre

end
