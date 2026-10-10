module
public import Mathlib

@[expose] public section

namespace FroehlichSpencer.BKT.Surface.VillainClock

/-- The lattice `ℓ¹` distance. -/
def l1Dist (u v : ℤ × ℤ) : ℕ := (u.1 - v.1).natAbs + (u.2 - v.2).natAbs

end FroehlichSpencer.BKT.Surface.VillainClock
