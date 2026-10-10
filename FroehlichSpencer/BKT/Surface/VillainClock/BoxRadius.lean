module
public import Mathlib

@[expose] public section

namespace FroehlichSpencer.BKT.Surface.VillainClock

/-- Sup-norm radius of a lattice site. -/
def boxRadius (z : ℤ × ℤ) : ℕ := max z.1.natAbs z.2.natAbs

end FroehlichSpencer.BKT.Surface.VillainClock
