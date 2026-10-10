/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Probability.Notation
public import FroehlichSpencer.BKT.Surface.FreeVillainLaw
import FroehlichSpencer.BKT.Provider.FreeVillainWellDefined

/-! # Normalization of the free-boundary Villain model in a finite region -/

open MeasureTheory

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
the total mass `Z_Λ` of the free-boundary Villain state is in `(0, ∞)`, so the
Villain state in a finite region `Λ ⊂ ℤ²` is a probability measure (FS81 (1.26), `Z_Λ⁻¹`).
-/
theorem isProbabilityMeasure_freeVillainLaw (β : ℝ) (hβ : 0 < β) (Λ : Finset (ℤ × ℤ)) :
    IsProbabilityMeasure (freeVillainLaw β hβ Λ) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.isProbabilityMeasure_freeVillainLaw β hβ Λ
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
