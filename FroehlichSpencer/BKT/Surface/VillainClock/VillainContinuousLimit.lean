module
public import Mathlib.Topology.Order.LiminfLimsup
public import FroehlichSpencer.BKT.Surface.VillainClock.FreeBox
public import FroehlichSpencer.BKT.Surface.VillainClock.VillainContinuousCorrelation

@[expose] public section

open Filter

namespace FroehlichSpencer.BKT.Surface.VillainClock

/-- Thermodynamic limit value, encoded as the limsup of the free centered-square correlations. -/
noncomputable def villainContinuousLimit (β : ℝ) (hβ : 0 < β) (ξ : ℤ)
    (u v : ℤ × ℤ) : ℝ :=
  Filter.limsup (fun L : ℕ =>
    villainContinuousCorrelation β hβ ξ (freeBox L) u v) atTop

end FroehlichSpencer.BKT.Surface.VillainClock
