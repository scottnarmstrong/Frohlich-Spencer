module
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import FroehlichSpencer.BKT.Surface.VillainClockDisorderExpectation

@[expose] public section

open Filter Topology

namespace FroehlichSpencer.BKT

/-- A Villain-clock disorder limit point along a strictly increasing exhaustion of centered boxes. -/
def IsVillainClockDisorderExhaustingLimitPoint (N r : ℕ) (β ξ c : ℝ)
    (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r) : Prop :=
  ∃ s : ℕ → ℕ, StrictMono s ∧ Tendsto s atTop atTop ∧
    Tendsto (fun t => villainClockDisorderExpectation N hN β hβ ξ (r + s t) r
      (Nat.lt_of_lt_of_le hr (Nat.le_add_right r (s t))) (Nat.le_add_right r (s t))) atTop (𝓝 c)

end FroehlichSpencer.BKT

end
