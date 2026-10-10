module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import FroehlichSpencer.BKT.Surface.VillainClockDisorderLimit
import FroehlichSpencer.BKT.Provider.VillainClockDisorderLowerBound

-- FROZEN_ANCHOR_PREFIX_BEGIN
@[expose] public section

open Filter

namespace FroehlichSpencer.BKT

/-- FS81 (7.5), for ξ=k/N and every exhausting Villain-clock disorder limit point. -/
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
                    (-(((k : ℝ) / N) ^ 2 * β''' / (2 * Real.pi))) ≤ c :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.villainClock_disorder_lowerBound_grid_exhausting
  -- FROZEN_ANCHOR_PROOF_END

-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
