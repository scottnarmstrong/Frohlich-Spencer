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
public import FroehlichSpencer.FS82.Provider.WilsonLoopTransitionCube

/-! FS82 perimeter surface theorem statement -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

/-- The transition of the Wilson loop in finite volume, FS82 (2.7) and (2.8), for the Villain
action and `m = 1`: there are `0 < β₀ < β₁` and `c > 0` such that, in every centred cube
`Λ = [-N, N]⁴` with `N ≥ max(L, T) + 1` and for all `L, T ≥ 1`, the expectation
`⟨W(ℒ_{L×T})⟩_Λ(β)` is real, satisfies the area law `0 ≤ ⟨W⟩ ≤ exp[-c L T]` for `0 < β ≤ β₀`, and
satisfies the perimeter law `⟨W⟩ ≥ exp[-d (L + T)]` with `d = d(β)` for `β ≥ β₁`. One family of
finite volumes carries both laws. -/
theorem fs82WilsonLoopTransitionCube :
    ∃ β₀ β₁ c : ℝ, 0 < β₀ ∧ β₀ < β₁ ∧ 0 < c ∧
      (∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ →
        ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ (N : ℕ) (hN : 0 < N), max L T + 1 ≤ N →
          (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).im = 0 ∧
          0 ≤ (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).re ∧
          (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).re ≤
            Real.exp (-(c * ((L : ℝ) * T)))) ∧
      (∀ (β : ℝ) (hβ : 0 < β), β₁ ≤ β → ∃ d : ℝ, 0 ≤ d ∧
        ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ (N : ℕ) (hN : 0 < N), max L T + 1 ≤ N →
          (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).im = 0 ∧
          Real.exp (-(d * ((L : ℝ) + T))) ≤
            (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).re) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN

  by exact FroehlichSpencer.FS82.Provider.fs82WilsonLoopTransitionCube
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.FS82.Surface

end
-- FROZEN_ANCHOR_SUFFIX_END
