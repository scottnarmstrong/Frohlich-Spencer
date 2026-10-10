/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Probability.Notation
public import FroehlichSpencer.BKT.Surface.ClockLaw
import FroehlichSpencer.BKT.Provider.ClockWellDefined

/-! # Normalization of the `ℤ_n` clock model in a finite region -/

open MeasureTheory

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
the total mass of the `ℤ_n` clock state (`n ≥ 1`) is in `(0, ∞)`, so the clock
state in a finite region `Λ ⊂ ℤ²` is a probability measure, for every real `β`.
-/
theorem isProbabilityMeasure_clockLaw (n : ℕ) (hn : 0 < n) (β : ℝ) (Λ : Finset (ℤ × ℤ)) :
    IsProbabilityMeasure (clockLaw n hn β Λ) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.isProbabilityMeasure_clockLaw n hn β Λ
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
