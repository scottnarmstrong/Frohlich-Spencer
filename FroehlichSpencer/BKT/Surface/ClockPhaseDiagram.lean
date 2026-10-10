/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import FroehlichSpencer.BKT.Surface.ClockExpDecay
public import FroehlichSpencer.BKT.Surface.ClockLongRangeOrder
public import FroehlichSpencer.BKT.Surface.ClockIntermediatePhase
import FroehlichSpencer.BKT.Provider.ClockPhaseDiagram

/-! # The three phases of the `ℤ_n` clock model -/

open Filter

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
the phase diagram of the `ℤ_n` clock models (FS81 result 4, J p. 528; §7.1,
Remark 2, J p. 585, and J p. 589).

There are thresholds `0 < β_h ≤ β₀`, a lower scale
`β' = β'(β) → ∞` of (7.3), and Peierls thresholds `β̄(n)` such that:
* (high temperature) for `n ≥ 2` and `0 ≤ β < β_h` the fundamental harmonic decays exponentially;
* (low temperature) for `n ≥ 2` and `β > β̄(n)` every harmonic has long-range order;
* (the massless intermediate phase) for every harmonic margin `q ∈ (0, 1)` there are upper ends
  `β₁(n) → ∞` and `n₁` such that for `n ≥ n₁`: `β₀ < β₁(n) ≤ β̄(n)`, and the model is in the
  massless intermediate phase (`IsClockIntermediatePhase`, lower scale `β'(β)`) at every
  `β ∈ [β₀, β₁(n)]`.

The orderings `β_h ≤ β₀` and `β₁(n) ≤ β̄(n)` make the three temperature ranges disjoint.
-/
theorem clock_phase_diagram :
    ∃ βh β₀ : ℝ, 0 < βh ∧ βh ≤ β₀ ∧ ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧ ∃ βbar : ℕ → ℝ,
      (∀ (n : ℕ) (hn : 0 < n), 2 ≤ n → ∀ (β : ℝ) (hβ : 0 ≤ β), β < βh →
        IsClockExpDecay n hn β hβ 1) ∧
      (∀ (n : ℕ) (hn : 0 < n), 2 ≤ n → ∀ (β : ℝ) (hβ : 0 ≤ β), βbar n < β →
        ∀ ξ : ℤ, IsClockLongRangeOrder n hn β hβ ξ) ∧
      ∀ q : ℝ, 0 < q → q < 1 → ∃ β₁ : ℕ → ℝ, Tendsto β₁ atTop atTop ∧ ∃ n₁ : ℕ,
        ∀ (n : ℕ) (hn : 0 < n), n₁ ≤ n → β₀ < β₁ n ∧ β₁ n ≤ βbar n ∧
          ∀ (β : ℝ) (hβ : 0 ≤ β), β₀ ≤ β → β ≤ β₁ n →
            IsClockIntermediatePhase n hn β hβ q (β' β) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.clock_phase_diagram
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
