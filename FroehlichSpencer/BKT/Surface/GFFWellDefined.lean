/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Probability.Notation
public import FroehlichSpencer.BKT.Surface.GFFLaw
import FroehlichSpencer.BKT.Provider.GFFWellDefined

/-! # Normalization of the discrete Gaussian free field -/

open MeasureTheory

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

universe u v

/--
`Z^GFF_{β,Λ,v} ∈ (0, ∞)`, so `μ^GFF_{β,Λ,v}` is a probability measure (KP (1.3),
p. 2).
-/
theorem isProbabilityMeasure_gffLaw {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V) :
    IsProbabilityMeasure (gffLaw G hG β hβ v) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.isProbabilityMeasure_gffLaw G hG β hβ v
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
