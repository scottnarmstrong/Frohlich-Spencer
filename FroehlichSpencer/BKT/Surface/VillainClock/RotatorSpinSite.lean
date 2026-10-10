module
public import Mathlib

@[expose] public section

namespace FroehlichSpencer.BKT.Surface.VillainClock

/-- Sites of the free square `[0,L]²`, with coordinates represented by `Fin (L+1)`. -/
abbrev rotatorSpinSite (L : ℕ) := Fin (L + 1) × Fin (L + 1)

end FroehlichSpencer.BKT.Surface.VillainClock
