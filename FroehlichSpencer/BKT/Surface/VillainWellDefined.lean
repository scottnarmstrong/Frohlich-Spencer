/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Probability.Notation
public import FroehlichSpencer.BKT.Surface.VillainLaw
import FroehlichSpencer.BKT.Provider.VillainWellDefined

/-! # Normalization of the Villain model -/

open MeasureTheory

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
`Z^Vil ∈ (0, ∞)`, so `μ^Vil_{β,Λ_L^zero}` is a probability measure (KP p. 4).
-/
theorem isProbabilityMeasure_villainLaw (L : ℕ) (β : ℝ) (hβ : 0 < β) :
    IsProbabilityMeasure (villainLaw L β hβ) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.isProbabilityMeasure_villainLaw L β hβ
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
