module
public import Mathlib

@[expose] public section

namespace FroehlichSpencer.BKT.Surface.VillainClock

/-- Angle at a lattice site, extended by zero off the finite region. -/
def latticeAngleLiteral {Λ : Finset (ℤ × ℤ)} (θ : Λ → ℝ) (z : ℤ × ℤ) : ℝ :=
  if h : z ∈ Λ then θ ⟨z, h⟩ else 0

end FroehlichSpencer.BKT.Surface.VillainClock
