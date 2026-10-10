/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Probability.Notation
public import FroehlichSpencer.BKT.Surface.SOSDirichletLaw
import FroehlichSpencer.BKT.Provider.SOSDirichletWellDefined

/-! # Normalization of the solid-on-solid model in a box -/

open MeasureTheory

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
the total mass of the solid-on-solid model in the box `{0, …, L - 1}²` with
Dirichlet boundary conditions is in `(0, ∞)` for every `β > 0`, so `sosDirichletLaw L β hβ` is a
probability measure (the normalization `Z⁻¹` of FS81's (7.16)).
-/
theorem isProbabilityMeasure_sosDirichletLaw (L : ℕ) (β : ℝ) (hβ : 0 < β) :
    IsProbabilityMeasure (sosDirichletLaw L β hβ) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.isProbabilityMeasure_sosDirichletLaw L β hβ
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
