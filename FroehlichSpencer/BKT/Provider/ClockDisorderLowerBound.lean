/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.ClockDisorder
import Mathlib.Tactic

/-!
# Provider: FS81 (7.5) on the `ℤ_n` grid
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open Filter Topology
open FroehlichSpencer.BKT FroehlichSpencer.BKT.Clock.Disorder
open FroehlichSpencer.BKT.Bridge.ClockDisorder


theorem clock_disorder_lowerBound :
    ∃ n₁ : ℝ → ℕ, Tendsto n₁ atTop atTop ∧
      ∀ β : ℝ, 0 ≤ β → ∀ (n : ℕ) (hn : 0 < n), n₁ β ≤ n →
        (∀ k : ℕ, 1 ≤ k → k < n → ∃ D : ℕ → ℝ, IsClockDisorderLimit n hn β ((k : ℝ) / n) D) ∧
        ∃ β''' : ℝ, 0 ≤ β''' ∧ ∃ C : ℝ, 0 < C ∧
          ∀ k : ℕ, 1 ≤ k → k < n → ∀ D : ℕ → ℝ, IsClockDisorderLimit n hn β ((k : ℝ) / n) D →
            ∀ r : ℕ, 0 < r →
              C * (1 + (r : ℝ)) ^ (-(((k : ℝ) / n) ^ 2 * β''' / (2 * Real.pi))) ≤ D r := by
  obtain ⟨n₁, hn₁, h⟩ := clock_disorder_lowerBound_grid
  refine ⟨n₁, hn₁, fun β hβ n hn hnn => ⟨fun k _ _ => exists_clockDisorderLimit n hn β _, ?_⟩⟩
  obtain ⟨β''', hβ''', C, hC, hb⟩ := h β hβ n hn hnn
  exact ⟨β''', hβ''', C, hC, fun k hk1 hkn D hD r hr =>
    hb k hk1 hkn r hr (D r) (isClockDisorderLimitPoint_of_limit hD r hr)⟩
end FroehlichSpencer.BKT.Provider

end
