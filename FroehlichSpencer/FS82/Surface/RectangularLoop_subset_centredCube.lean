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
public import FroehlichSpencer.FS82.Surface.PrimalCoord
public import FroehlichSpencer.FS82.Surface.PrimalCell
public import FroehlichSpencer.FS82.Surface.PrimalCellDegree
public import FroehlichSpencer.FS82.Surface.PrimalLinks
public import FroehlichSpencer.FS82.Surface.PrimalCellEmbedding
public import FroehlichSpencer.FS82.Surface.RectangularLoop
public import FroehlichSpencer.FS82.Surface.CentredCube
public import FroehlichSpencer.FS82.Provider.RectangularLoopInCube

/-! FS82 perimeter surface theorem statement -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

/-- For `L, T ≤ N` the loop `ℒ_{L×T}` lies in the cube `[-N, N]⁴` (FS82 (1.8): `ℒ ⊂ Λ`): every
cell of the chain is a link of the cube. -/
theorem rectangularLoop_subset_centredCube (L T N : ℕ) (hN : 0 < N) (hL : L ≤ N) (hT : T ≤ N)
    (c : LatticeCell) (hc : c ∈ (rectangularLoop L T).support) :
    ∃ ℓ : PrimalLinks (centredCube N hN), primalCellEmbedding (centredCube N hN) ℓ.1 = c :=
  -- FROZEN_ANCHOR_PROOF_BEGIN

  by exact FroehlichSpencer.FS82.Provider.rectangularLoop_subset_centredCube L T N hN hL hT c hc
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.FS82.Surface

end
-- FROZEN_ANCHOR_SUFFIX_END
