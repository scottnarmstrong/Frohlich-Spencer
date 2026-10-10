/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.ClockIntermediatePhase
public import FroehlichSpencer.BKT.Bridge.ClockIntermediatePhase
public import FroehlichSpencer.BKT.Clock.Source.Result4
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.clock_massless_intermediatePhase`

This module contains `FroehlichSpencer.BKT.Provider.clock_massless_intermediatePhase`, the proof of
the statement `FroehlichSpencer.BKT.clock_massless_intermediatePhase` (file
`FroehlichSpencer/BKT/Surface/ClockMasslessPhase.lean`, FS81 result 4).

-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open Filter Topology
open FroehlichSpencer.BKT.Ginibre FroehlichSpencer.BKT.Clock
open FroehlichSpencer.BKT.Bridge.ClockIntermediatePhase (isClockIntermediatePhase_of_exact)


theorem clock_massless_intermediatePhase :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧
      ∀ q : ℝ, 0 < q → q < 1 → ∃ β₁ : ℕ → ℝ, Tendsto β₁ atTop atTop ∧
        ∃ n₁ : ℕ, ∀ (n : ℕ) (hn : 0 < n), n₁ ≤ n → β₀ < β₁ n ∧
          ∀ (β : ℝ) (hβ : 0 ≤ β), β₀ ≤ β → β ≤ β₁ n →
            IsClockIntermediatePhase n hn β hβ q (β' β) := by
  obtain ⟨β₀, hβ₀, β', hβ'T, h⟩ := Source.clock_massless_window_exact
  refine ⟨β₀, hβ₀, β', hβ'T, fun q hq _ => ?_⟩
  obtain ⟨β₁, hβ₁, n₁, hwin⟩ := h q hq
  exact ⟨β₁, hβ₁, n₁, fun n hn0 hn1 => ⟨(hwin n hn1 hn0).1, fun β hβ hlo hhi =>
    isClockIntermediatePhase_of_exact hn0 hβ ((hwin n hn1 hn0).2 β hβ hlo hhi)⟩⟩

end FroehlichSpencer.BKT.Provider

end
