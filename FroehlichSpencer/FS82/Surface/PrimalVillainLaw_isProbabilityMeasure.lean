/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.RectBox4
public import FroehlichSpencer.FS82.Surface.LatticeCoord
public import FroehlichSpencer.FS82.Surface.LatticeCell
public import FroehlichSpencer.FS82.Surface.LatticeChain
public import FroehlichSpencer.FS82.Surface.LatticeIsEdge
public import FroehlichSpencer.FS82.Surface.LatticeRankBefore
public import FroehlichSpencer.FS82.Surface.LatticeBasis
public import FroehlichSpencer.FS82.Surface.LatticeUpperFace
public import FroehlichSpencer.FS82.Surface.LatticeLowerFace
public import FroehlichSpencer.FS82.Surface.LatticeBoundaryBasis
public import FroehlichSpencer.FS82.Surface.PrimalCoord
public import FroehlichSpencer.FS82.Surface.PrimalCell
public import FroehlichSpencer.FS82.Surface.PrimalCellDegree
public import FroehlichSpencer.FS82.Surface.PrimalLinks
public import FroehlichSpencer.FS82.Surface.PrimalLinksFintype
public import FroehlichSpencer.FS82.Surface.PrimalPlaquettes
public import FroehlichSpencer.FS82.Surface.PrimalPlaquettesFintype
public import FroehlichSpencer.FS82.Surface.PrimalCellEmbedding
public import FroehlichSpencer.FS82.Surface.PrimalPlaquetteCurl
public import FroehlichSpencer.FS82.Surface.PrimalVillainLaw
public import FroehlichSpencer.FS82.Provider.PrimalVillainLawProbability

/-! FS82 perimeter surface theorem statement -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

/-- The total mass `Ẑ_Λ` of FS82 (2.4) is in `(0, ∞)`: the Villain measure (2.3) of every box is a
probability measure. -/
theorem primalVillainLaw_isProbabilityMeasure (R : RectBox4) (β : ℝ) (hβ : 0 < β) :
    MeasureTheory.IsProbabilityMeasure (primalVillainLaw R β hβ) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN

  by exact FroehlichSpencer.FS82.Provider.primalVillainLaw_isProbabilityMeasure R β hβ
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.FS82.Surface

end
-- FROZEN_ANCHOR_SUFFIX_END
