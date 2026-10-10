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
public import FroehlichSpencer.FS82.Surface.WilsonLoopObservable
public import FroehlichSpencer.FS82.Surface.WilsonLoopExpectation
public import FroehlichSpencer.FS82.Surface.RectangularLoop
public import FroehlichSpencer.FS82.Surface.CentredCube
public import FroehlichSpencer.FS82.Surface.WilsonCubeSequence
public import FroehlichSpencer.FS82.Provider.WilsonLoopPerimeterLawCubeLimit

/-! FS82 perimeter surface theorem statement -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

/-- FS82 (2.8) along the centred cubes, for the Villain action and `m = 1`: for `β` large enough
there is `d = d(β)` such that, for all `L, T ≥ 1`, the real parts of the expectations of
`W(ℒ_{L×T})` in the cubes have a limit point, every limit point and the lower limit are at least
`exp[-d (L + T)]`, and so is their limit (2.6) along the cubes if it exists. -/
theorem fs82WilsonLoopPerimeterLawCubeLimit :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ (β : ℝ) (hβ : 0 < β), β₀ ≤ β → ∃ d : ℝ, 0 ≤ d ∧
      ∀ L T : ℕ, 1 ≤ L → 1 ≤ T →
        (∃ x : ℝ, MapClusterPt x atTop (wilsonCubeSequence β hβ L T)) ∧
        (∀ x : ℝ, MapClusterPt x atTop (wilsonCubeSequence β hβ L T) →
          Real.exp (-(d * ((L : ℝ) + T))) ≤ x) ∧
        Real.exp (-(d * ((L : ℝ) + T))) ≤ Filter.liminf (wilsonCubeSequence β hβ L T) atTop ∧
        ∀ w : ℝ, Tendsto (wilsonCubeSequence β hβ L T) atTop (nhds w) →
          Real.exp (-(d * ((L : ℝ) + T))) ≤ w :=
  -- FROZEN_ANCHOR_PROOF_BEGIN

  by exact FroehlichSpencer.FS82.Provider.fs82WilsonLoopPerimeterLawCubeLimit
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.FS82.Surface

end
-- FROZEN_ANCHOR_SUFFIX_END
