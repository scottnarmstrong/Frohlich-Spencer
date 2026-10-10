/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.ExistsUnique_finiteLatticeHodgeInverse
public import FroehlichSpencer.FS82.Surface.FiniteLatticeHodgeInverse
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
public import FroehlichSpencer.FS82.Surface.LatticeEdgeCell
public import FroehlichSpencer.FS82.Surface.LatticeUpperFace
public import FroehlichSpencer.FS82.Surface.LatticeLowerFace
public import FroehlichSpencer.FS82.Surface.LatticeBoundaryBasis
public import FroehlichSpencer.FS82.Surface.LatticeCoboundaryBasis
public import FroehlichSpencer.FS82.Surface.LatticeBoundary
public import FroehlichSpencer.FS82.Surface.LatticeCoboundary
public import FroehlichSpencer.FS82.Surface.LatticeDeltaD
public import FroehlichSpencer.FS82.Surface.CastLatticeChain
public import FroehlichSpencer.FS82.Surface.RealifyLatticeLinearMap
public import FroehlichSpencer.FS82.Surface.RealLatticeBoundary
public import FroehlichSpencer.FS82.Surface.RealLatticeDeltaD
public import FroehlichSpencer.FS82.Surface.LambdaStarRealChain
public import FroehlichSpencer.FS82.Surface.RealDualField
public import FroehlichSpencer.FS82.Surface.EuclideanToFinsupp
public import FroehlichSpencer.FS82.Surface.FinsuppToEuclidean
public import FroehlichSpencer.FS82.Surface.LambdaStarRealZeroExtension
public import FroehlichSpencer.FS82.Surface.LambdaStarRealCompression
public import FroehlichSpencer.FS82.Surface.PiLambdaStarDeltaDReal
public import FroehlichSpencer.FS82.Surface.FiniteLatticeHodgeOperator
public import FroehlichSpencer.FS82.Surface.FullLatticeDivergence
public import FroehlichSpencer.FS82.Surface.LambdaStarVertexRestriction
public import FroehlichSpencer.FS82.Surface.LambdaStarVertexDivergence
public import FroehlichSpencer.FS82.Surface.W
public import FroehlichSpencer.FS82.Surface.FiniteLatticeHodgeOperatorOnCoClosed

@[expose] public section

open scoped BigOperators
open FroehlichSpencer.FS82.Surface
namespace FroehlichSpencer.FS82.Provider

theorem finiteLatticeHodgeInverse_spec (R : RectBox4) :
    (∀ μ : W R, finiteLatticeHodgeOperatorOnCoClosed R (finiteLatticeHodgeInverse R μ) = μ) ∧
      ∀ V', (∀ μ : W R, finiteLatticeHodgeOperatorOnCoClosed R (V' μ) = μ) →
        V' = finiteLatticeHodgeInverse R := by
  have hchosen := Classical.choose_spec (existsUnique_finiteLatticeHodgeInverse R).exists
  constructor
  · simpa only [finiteLatticeHodgeInverse] using hchosen
  · intro V' hV'
    obtain ⟨V, hV, huniq⟩ := existsUnique_finiteLatticeHodgeInverse R
    have hchoose : Classical.choose (existsUnique_finiteLatticeHodgeInverse R).exists = V :=
      huniq _ hchosen
    calc
      V' = V := huniq V' hV'
      _ = finiteLatticeHodgeInverse R := by
        simpa only [finiteLatticeHodgeInverse] using hchoose.symm

end FroehlichSpencer.FS82.Provider

end
