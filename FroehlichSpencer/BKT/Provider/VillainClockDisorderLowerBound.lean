/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import FroehlichSpencer.BKT.Surface.VillainClockDisorderLimit
public import FroehlichSpencer.BKT.Clock.VillainClock.DisorderExhaustion
public import FroehlichSpencer.BKT.Bridge.VillainClockDisorder


@[expose] public section

open MeasureTheory Filter
open FroehlichSpencer.BKT.Clock.VillainClock
open FroehlichSpencer.BKT.Bridge.VillainClockDisorder

namespace FroehlichSpencer.BKT.Provider

theorem villainClock_disorder_lowerBound_grid_exhausting :
    ∃ n₁ : ℝ → ℕ, Tendsto n₁ atTop atTop ∧
      ∀ (β : ℝ) (hβ : 0 < β) (N : ℕ) (hN : 0 < N),
        n₁ β ≤ N →
          ∃ (β''' : ℝ), 0 ≤ β''' ∧
            ∃ C : ℝ, 0 < C ∧
              ∀ k : ℕ, 1 ≤ k → k < N →
                ∀ (r : ℕ) (hr : 0 < r) (c : ℝ),
                  IsVillainClockDisorderExhaustingLimitPoint
                    N r β ((k : ℝ) / N) c hβ hN hr →
                  C * (1 + (r : ℝ)) ^
                    (-(((k : ℝ) / N) ^ 2 * β''' / (2 * Real.pi))) ≤ c := by
  obtain ⟨n₁, hn₁, hroot⟩ :=
    Clock.VillainClock.villainClock_disorder_lowerBound_grid_exhausting
  refine ⟨n₁, hn₁, ?_⟩
  intro β hβ N hN hn₁N
  obtain ⟨β''', hβ''', C, hC, hrest⟩ := hroot β hβ N hN hn₁N
  refine ⟨β''', hβ''', C, hC, ?_⟩
  intro k hk1 hkN r hr c hc
  apply hrest k hk1 hkN r hr c
  exact (isVillainClockDisorderExhaustingLimitPoint_iff N r β ((k : ℝ) / N) c
    hβ hN hr).mp hc

end FroehlichSpencer.BKT.Provider

end
