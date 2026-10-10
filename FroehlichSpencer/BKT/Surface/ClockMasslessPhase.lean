/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import FroehlichSpencer.BKT.Surface.ClockIntermediatePhase
import FroehlichSpencer.BKT.Provider.ClockMasslessPhase

/-! # FS81 result 4: the massless intermediate phase of the `ℤ_n` clock model -/

open Filter

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
FS81 result 4 (J p. 528): "for `n` large enough, there exist temperatures
`T̲_c > 0` and `T̃_c > T̲_c` such that, for `T̲_c < T < T̃_c`, the `ℤ_n`-model has a massless,
intermediate phase", in the form of §7.1, Remark 2 (J p. 585).

There is a lower end `β₀ > 0`,
independent of `n` (FS81's `β̲_c`), and a lower scale `β' = β'(β)` of (7.3), independent of `n`,
with `β'(β) → ∞` as `β → ∞`, such that for every harmonic margin `q ∈ (0, 1)` there are upper ends
`β₁(n) → ∞` (FS81's `β̄_c(n)`) and `n₁` with: for every `n ≥ n₁`, `β₀ < β₁(n)` and the model is in
the massless intermediate phase (`IsClockIntermediatePhase`, with lower scale `β'(β)`) at every
`β ∈ [β₀, β₁(n)]`, i.e. at every temperature `1/β₁(n) ≤ T ≤ 1/β₀`.
-/
theorem clock_massless_intermediatePhase :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧
      ∀ q : ℝ, 0 < q → q < 1 → ∃ β₁ : ℕ → ℝ, Tendsto β₁ atTop atTop ∧
        ∃ n₁ : ℕ, ∀ (n : ℕ) (hn : 0 < n), n₁ ≤ n → β₀ < β₁ n ∧
          ∀ (β : ℝ) (hβ : 0 ≤ β), β₀ ≤ β → β ≤ β₁ n →
            IsClockIntermediatePhase n hn β hβ q (β' β) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.clock_massless_intermediatePhase
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
