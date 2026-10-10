/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.RectBox4
public import FroehlichSpencer.FS82.Surface.RectBox4ShortestSide
public import FroehlichSpencer.FS82.Surface.RectBox4LongestSide
public import FroehlichSpencer.FS82.Surface.IsLogThickRectBox4
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
public import FroehlichSpencer.FS82.Surface.RealLatticeDeltaD
public import FroehlichSpencer.FS82.Surface.LambdaStarRealChain
public import FroehlichSpencer.FS82.Surface.RealDualField
public import FroehlichSpencer.FS82.Surface.IsInteriorDualLink
public import FroehlichSpencer.FS82.Surface.IsInteriorSupported
public import FroehlichSpencer.FS82.Surface.EuclideanToFinsupp
public import FroehlichSpencer.FS82.Surface.FinsuppToEuclidean
public import FroehlichSpencer.FS82.Surface.LambdaStarRealZeroExtension
public import FroehlichSpencer.FS82.Surface.LambdaStarRealCompression
public import FroehlichSpencer.FS82.Surface.PiLambdaStarDeltaDReal
public import FroehlichSpencer.FS82.Surface.FiniteLatticeHodgeOperator
public import FroehlichSpencer.FS82.Surface.FullLatticeDivergence
public import FroehlichSpencer.FS82.Surface.LambdaStarVertexRestriction
public import FroehlichSpencer.FS82.Surface.LambdaStarVertexDivergence
public import FroehlichSpencer.FS82.Surface.GlobalCoClosed
public import FroehlichSpencer.FS82.Surface.W
public import FroehlichSpencer.FS82.Surface.IntegerDualField
public import FroehlichSpencer.FS82.Surface.LatticeVertices4
public import FroehlichSpencer.FS82.Surface.LatticePotentialGradient
public import FroehlichSpencer.FS82.Surface.SourceIntegerGaugeRelation
public import FroehlichSpencer.FS82.Surface.LambdaStarIntegerZeroExtension
public import FroehlichSpencer.FS82.Surface.IntegerLatticeCurl
public import FroehlichSpencer.FS82.Surface.IntegerDualFieldWeight
public import FroehlichSpencer.FS82.Surface.BetaDoublePrime
public import FroehlichSpencer.FS82.Surface.FiniteLatticeHodgeOperatorOnCoClosed
public import FroehlichSpencer.FS82.Surface.FiniteLatticeHodgeInverse
public import FroehlichSpencer.FS82.Surface.SourceIntegerGaugeRelationSetoid
public import FroehlichSpencer.FS82.Surface.IntegerDualGaugeQuotient
public import FroehlichSpencer.FS82.Surface.IntegerDualGaugeQuotientMeasurableSpace
public import FroehlichSpencer.FS82.Surface.IntegerDualGaugeWeight
public import FroehlichSpencer.FS82.Surface.IntegerDualPairing
public import FroehlichSpencer.FS82.Surface.IntegerDualPartitionFunction
public import FroehlichSpencer.FS82.Surface.DiscreteDualMeasure
public import FroehlichSpencer.FS82.Surface.DiscreteDualMoment
public import FroehlichSpencer.FS82.Surface.SourceTestToW
public import FroehlichSpencer.FS82.Surface.FiniteLatticeCovarianceQuadratic
public import FroehlichSpencer.FS82.Provider.FiniteVillainDualMomentComparisonLogThick

/-! FS82 source root, option (B): log-thick rectangles. -/

open Filter

-- FROZEN_ANCHOR_PREFIX_BEGIN
@[expose] public section

namespace FroehlichSpencer.FS82.Surface

theorem fs82FiniteVillainDualMomentComparisonLogThick :
∃ β₀ : {b : ℝ // 0 < b}, ∃ cPack : ℝ → ℝ,
      (∀ β : ℝ, β₀.val ≤ β → 0 < cPack β) ∧
      Tendsto (fun β : ℝ => 2 * β * cPack β) atTop (nhds 0) ∧
      (∀ β : ℝ, β₀.val ≤ β →
        0 < betaDoublePrime cPack β ∧ betaDoublePrime cPack β < β) ∧
      Tendsto (betaDoublePrime cPack) atTop atTop ∧
      ∀ β : ℝ, (hβRange : β₀.val ≤ β) →
        ∀ R : RectBox4,
          IsLogThickRectBox4 R →
        ∀ μ : RealDualField R,
          ∀ hglobal : μ ∈ GlobalCoClosed R,
            ∀ hinterior : IsInteriorSupported R μ,
          ∀ ε : ℝ,
            ENNReal.ofReal
                (Real.exp (ε ^ 2 * betaDoublePrime cPack β / 2 *
                  finiteLatticeCovarianceQuadratic R
                    (sourceTestToW R μ hinterior hglobal))) ≤
              discreteDualMoment R β
                (by have := β₀.property; linarith [hβRange]) ε
                (sourceTestToW R μ hinterior hglobal) ∧
            discreteDualMoment R β
                (by have := β₀.property; linarith [hβRange]) ε
                (sourceTestToW R μ hinterior hglobal) ≤
              ENNReal.ofReal
                (Real.exp (ε ^ 2 * β / 2 *
                  finiteLatticeCovarianceQuadratic R
                    (sourceTestToW R μ hinterior hglobal))) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.FS82.Provider.fs82FiniteVillainDualMomentComparisonLogThick
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.FS82.Surface

end
-- FROZEN_ANCHOR_SUFFIX_END
