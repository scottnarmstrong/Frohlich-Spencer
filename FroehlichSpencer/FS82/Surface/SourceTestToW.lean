/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.RectBox4
public import FroehlichSpencer.FS82.Surface.DualCoord
public import FroehlichSpencer.FS82.Surface.DualCell
public import FroehlichSpencer.FS82.Surface.DualCellAxes
public import FroehlichSpencer.FS82.Surface.DualCellDegree
public import FroehlichSpencer.FS82.Surface.DualVertices
public import FroehlichSpencer.FS82.Surface.DualLinks
public import FroehlichSpencer.FS82.Surface.LatticeCoord
public import FroehlichSpencer.FS82.Surface.LatticeCell
public import FroehlichSpencer.FS82.Surface.LatticeChain
public import FroehlichSpencer.FS82.Surface.RealLatticeChain
public import FroehlichSpencer.FS82.Surface.DualEmbedCoordC1
public import FroehlichSpencer.FS82.Surface.DualCellEmbeddingC1
public import FroehlichSpencer.FS82.Surface.LambdaStarEmbeddingC1
public import FroehlichSpencer.FS82.Surface.LatticeIsEdge
public import FroehlichSpencer.FS82.Surface.LatticeRankBefore
public import FroehlichSpencer.FS82.Surface.LatticeBasis
public import FroehlichSpencer.FS82.Surface.LatticeUpperFace
public import FroehlichSpencer.FS82.Surface.LatticeLowerFace
public import FroehlichSpencer.FS82.Surface.LatticeBoundaryBasis
public import FroehlichSpencer.FS82.Surface.LatticeBoundary
public import FroehlichSpencer.FS82.Surface.CastLatticeChain
public import FroehlichSpencer.FS82.Surface.RealifyLatticeLinearMap
public import FroehlichSpencer.FS82.Surface.RealLatticeBoundary
public import FroehlichSpencer.FS82.Surface.LambdaStarRealChain
public import FroehlichSpencer.FS82.Surface.RealDualField
public import FroehlichSpencer.FS82.Surface.IsInteriorDualLink
public import FroehlichSpencer.FS82.Surface.IsInteriorSupported
public import FroehlichSpencer.FS82.Surface.EuclideanToFinsupp
public import FroehlichSpencer.FS82.Surface.LambdaStarRealZeroExtension
public import FroehlichSpencer.FS82.Surface.FullLatticeDivergence
public import FroehlichSpencer.FS82.Surface.LambdaStarVertexRestriction
public import FroehlichSpencer.FS82.Surface.LambdaStarVertexDivergence
public import FroehlichSpencer.FS82.Surface.GlobalCoClosed
public import FroehlichSpencer.FS82.Surface.W
public import FroehlichSpencer.FS82.Surface.InteriorSupported_coClosed_iff
public import FroehlichSpencer.FS82.Surface.InteriorSupported_coClosed_iff
public import FroehlichSpencer.FS82.Surface.ExistsUnique_finiteLatticeHodgeInverse

/-! FS82 source definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

noncomputable def sourceTestToW (R : RectBox4) (μ : RealDualField R)
    (hμ : IsInteriorSupported R μ) (hglobal : μ ∈ GlobalCoClosed R) : W R :=
  ⟨μ, (interiorSupported_coClosed_iff R μ hμ).mp hglobal⟩

-- Define only after `existsUnique_finiteLatticeHodgeInverse` is proved and .

end FroehlichSpencer.FS82.Surface

end
