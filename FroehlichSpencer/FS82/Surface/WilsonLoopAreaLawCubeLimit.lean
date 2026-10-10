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
public import FroehlichSpencer.FS82.Provider.WilsonLoopAreaLawCubeLimit

/-! FS82 perimeter surface theorem statement -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

/-- FS82 (2.7) along the centred cubes, for the Villain action and `m = 1`: for `β` small enough
there is `c > 0`, independent of `β`, `L` and `T`, such that, for all `L, T ≥ 1`, the real parts of
the expectations of `W(ℒ_{L×T})` in the cubes have a limit point, every limit point lies in
`[0, exp[-c L T]]`, the upper limit is at most `exp[-c L T]`, and their limit (2.6) along the cubes
lies in `[0, exp[-c L T]]` if it exists. -/
theorem fs82WilsonLoopAreaLawCubeLimit :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ →
      ∀ L T : ℕ, 1 ≤ L → 1 ≤ T →
        (∃ x : ℝ, MapClusterPt x atTop (wilsonCubeSequence β hβ L T)) ∧
        (∀ x : ℝ, MapClusterPt x atTop (wilsonCubeSequence β hβ L T) →
          0 ≤ x ∧ x ≤ Real.exp (-(c * ((L : ℝ) * T)))) ∧
        Filter.limsup (wilsonCubeSequence β hβ L T) atTop ≤ Real.exp (-(c * ((L : ℝ) * T))) ∧
        ∀ w : ℝ, Tendsto (wilsonCubeSequence β hβ L T) atTop (nhds w) →
          0 ≤ w ∧ w ≤ Real.exp (-(c * ((L : ℝ) * T))) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN

  by exact FroehlichSpencer.FS82.Provider.fs82WilsonLoopAreaLawCubeLimit
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.FS82.Surface

end
-- FROZEN_ANCHOR_SUFFIX_END
