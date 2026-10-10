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
public import FroehlichSpencer.FS82.Surface.PrimalCellEmbedding

/-! FS82 perimeter surface definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

/-- FS82 (2.3): `dθ_p = ∑_{xy ⊂ ∂p} θ_xy`, the oriented sum of the link angles around the
plaquette `p`, with (2.1), `θ_yx = -θ_xy`. The coefficient of a link is its coefficient in the
lattice boundary of `p`. -/
noncomputable def primalPlaquetteCurl (R : RectBox4) (θ : PrimalLinks R → ℝ)
    (p : PrimalPlaquettes R) : ℝ :=
  ∑ ℓ : PrimalLinks R,
    ((latticeBoundaryBasis (primalCellEmbedding R p.1) (primalCellEmbedding R ℓ.1) : ℤ) : ℝ) * θ ℓ

end FroehlichSpencer.FS82.Surface

end
