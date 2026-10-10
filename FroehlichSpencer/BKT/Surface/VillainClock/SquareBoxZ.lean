module
public import Mathlib

@[expose] public section

namespace FroehlichSpencer.BKT.Surface.VillainClock

/-- The lattice square `{0,…,L}²`. -/
def squareBoxZ (L : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (0 : ℤ) L ×ˢ Finset.Icc (0 : ℤ) L

end FroehlichSpencer.BKT.Surface.VillainClock
