module
public import Mathlib

@[expose] public section

namespace FroehlichSpencer.BKT.Surface.VillainClock

/-- Centered free square `[-L,L]²`. -/
def freeBox (L : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(L : ℤ)) L ×ˢ Finset.Icc (-(L : ℤ)) L

end FroehlichSpencer.BKT.Surface.VillainClock
