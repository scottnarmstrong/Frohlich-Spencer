/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Probability.Notation
public import FroehlichSpencer.BKT.Surface.PlaneRotatorLaw
import FroehlichSpencer.BKT.Provider.PlaneRotatorWellDefined

/-! # Normalization of the plane rotator in a finite region -/

open MeasureTheory

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
`Z_Λ ∈ (0, ∞)`, so the plane rotator state of FS81 (1.26) in a finite region
`Λ ⊂ ℤ²` is a probability measure, for every real `β`.
-/
theorem isProbabilityMeasure_planeRotatorLaw (β : ℝ) (Λ : Finset (ℤ × ℤ)) :
    IsProbabilityMeasure (planeRotatorLaw β Λ) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.isProbabilityMeasure_planeRotatorLaw β Λ
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
