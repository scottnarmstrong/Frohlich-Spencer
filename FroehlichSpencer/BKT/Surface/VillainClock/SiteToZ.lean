module
public import Mathlib
public import FroehlichSpencer.BKT.Surface.VillainClock.RotatorSpinSite

@[expose] public section

namespace FroehlichSpencer.BKT.Surface.VillainClock

/-- The lattice coordinates of a site in the finite free square. -/
def siteToZ {L : ℕ} (p : rotatorSpinSite L) : ℤ × ℤ :=
  ((p.1.val : ℤ), (p.2.val : ℤ))

end FroehlichSpencer.BKT.Surface.VillainClock
