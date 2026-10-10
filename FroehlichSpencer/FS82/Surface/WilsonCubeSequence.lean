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

/-! FS82 perimeter surface definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

/-- The expectations of `W(ℒ_{L×T})` along the centred cubes, FS82 (2.6):
`n ↦ Re ⟨W(ℒ_{L×T})⟩_Λ(β)` for `Λ = [-(n+1), n+1]⁴`. -/
noncomputable def wilsonCubeSequence (β : ℝ) (hβ : 0 < β) (L T : ℕ) : ℕ → ℝ :=
  fun n => (wilsonLoopExpectation (centredCube (n + 1) (Nat.succ_pos n)) β hβ
    (rectangularLoop L T)).re

end FroehlichSpencer.FS82.Surface

end
