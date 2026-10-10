/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Probability.Notation
public import FroehlichSpencer.BKT.Surface.SOSLiteralDiffLaw
import FroehlichSpencer.BKT.Provider.SOSLiteralWellDefined

/-! # Normalization of FS81's solid-on-solid state (7.16) in a box -/

open MeasureTheory

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
for `0 < β ≤ 1`, every finite region `A ⊂ ℤ²` with a base point `w ∈ A` and every
box `[-R, R]² ⊇ A`, the total mass of FS81's state (7.16) is in `(0, ∞)` (the normalization
`Z_A⁻¹`), so the law of the height differences `sosLiteralDiffLaw` is a probability measure.
-/
theorem isProbabilityMeasure_sosLiteralDiffLaw (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (A : Finset (ℤ × ℤ)) (w : ℤ × ℤ) (hw : w ∈ A) (R : ℕ)
    (hA : A ⊆ Finset.Icc (-(R : ℤ)) R ×ˢ Finset.Icc (-(R : ℤ)) R) :
    IsProbabilityMeasure (sosLiteralDiffLaw β hβ hβ1 A w hw R hA) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.isProbabilityMeasure_sosLiteralDiffLaw β hβ hβ1 A w hw R hA
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
