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
public import FroehlichSpencer.FS82.Surface.DualLinksFintype
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
public import FroehlichSpencer.FS82.Surface.RealLatticeCoboundary
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
public import FroehlichSpencer.FS82.Surface.LatticeCurl
public import FroehlichSpencer.FS82.Surface.LatticeGaugeQuotient
public import FroehlichSpencer.FS82.Surface.FiniteLatticeHodgeOperatorOnCoClosed
public import FroehlichSpencer.FS82.Surface.FiniteLatticeHodgeInverse
public import FroehlichSpencer.FS82.Surface.LatticeQuotientTestFunctional

/-! FS82 source definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

def SourceQuotientGaussianSpec (R : RectBox4) (β : ℝ) (_hβ : 0 < β)
    (P : MeasureTheory.Measure (LatticeGaugeQuotient R)) : Prop :=
  MeasureTheory.IsProbabilityMeasure P ∧
  ∀ μ : W R,
    MeasureTheory.charFun
        (MeasureTheory.Measure.map (latticeQuotientTestFunctional R μ) P) 1 =
      Complex.exp (-↑((β / 2) * inner ℝ (μ : RealDualField R)
        (finiteLatticeHodgeInverse R μ : RealDualField R)))

end FroehlichSpencer.FS82.Surface

end
