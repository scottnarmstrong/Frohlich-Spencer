/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Ginibre.SquareBox

/-!
# The `ℓ¹` distance on `ℤ²` and on the free spin box
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Rotator.Transition

open FroehlichSpencer.BKT.Rotator.Ginibre

/-- The `ℓ¹` norm `|z₁| + |z₂|` of a point of `ℤ²`. -/
def l1Norm (z : ℤ × ℤ) : ℕ :=
  z.1.natAbs + z.2.natAbs

/-- The `ℓ¹` (graph) distance between two sites of the free spin box. -/
def boxDist {L : ℕ} (p q : RotatorSpinSite L) : ℕ :=
  l1Norm (siteToZ p - siteToZ q)

end FroehlichSpencer.BKT.Rotator.Transition

end
