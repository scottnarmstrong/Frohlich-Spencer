module
public import Mathlib

@[expose] public section

namespace FroehlichSpencer.BKT.Surface.VillainClock

/-- Graph distance in the free square, written in the coordinates of its vertices. -/
def freeRadius {L : ℕ} (p x : Fin L × Fin L) : ℕ :=
  Nat.dist p.1.val x.1.val + Nat.dist p.2.val x.2.val

end FroehlichSpencer.BKT.Surface.VillainClock
