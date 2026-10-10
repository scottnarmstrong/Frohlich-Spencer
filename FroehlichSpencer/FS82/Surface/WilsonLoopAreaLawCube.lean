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
public import FroehlichSpencer.FS82.Provider.WilsonLoopAreaLawCube

/-! FS82 perimeter surface theorem statement -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

/-- FS82 (2.7) in finite volume, for the Villain action and `m = 1`, on centred cubes: for `β`
small enough, `⟨W(ℒ_{L×T})⟩_Λ(β)` is real and `0 ≤ ⟨W(ℒ_{L×T})⟩_Λ(β) ≤ exp[-c L T]`, with `c > 0`
independent of `β`, `L`, `T` and `Λ`, for all `L, T ≥ 1` and every cube `Λ = [-N, N]⁴` with
`N ≥ max(L, T) + 1`. These are the cubes of the perimeter law. -/
theorem fs82WilsonLoopAreaLawCube :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ →
      ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ (N : ℕ) (hN : 0 < N), max L T + 1 ≤ N →
        (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).im = 0 ∧
        0 ≤ (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).re ∧
        (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).re ≤
          Real.exp (-(c * ((L : ℝ) * T))) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN

  by exact FroehlichSpencer.FS82.Provider.fs82WilsonLoopAreaLawCube
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.FS82.Surface

end
-- FROZEN_ANCHOR_SUFFIX_END
