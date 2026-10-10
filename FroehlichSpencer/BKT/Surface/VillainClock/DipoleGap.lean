module
public import Mathlib

@[expose] public section

namespace FroehlichSpencer.BKT.Surface.VillainClock

/-- The gap `min(ξ,1−ξ)` for the marked dipole. -/
def dipoleGap (ξ : ℝ) : ℝ := min ξ (1 - ξ)

end FroehlichSpencer.BKT.Surface.VillainClock
