/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import FroehlichSpencer.FS82.Surface.RectBox4
public import FroehlichSpencer.FS82.Surface.DualCoord
public import FroehlichSpencer.FS82.Surface.DualCell
public import FroehlichSpencer.FS82.Surface.DualCellAxes
public import FroehlichSpencer.FS82.Surface.DualCellDegree
public import FroehlichSpencer.FS82.Surface.DualLinks
public import FroehlichSpencer.FS82.Surface.DualPlaquettes
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
public import FroehlichSpencer.FS82.Surface.SourceClosedIntegerCurrent
public import FroehlichSpencer.FS82.Surface.CastLatticeChain
public import FroehlichSpencer.FS82.Surface.RealifyLatticeLinearMap
public import FroehlichSpencer.FS82.Surface.RealLatticeBoundary
public import FroehlichSpencer.FS82.Surface.IntegerDualField
public import FroehlichSpencer.FS82.Surface.LatticeVertices4
public import FroehlichSpencer.FS82.Surface.LatticePotentialGradient
public import FroehlichSpencer.FS82.Surface.SourceIntegerGaugeRelation
public import FroehlichSpencer.FS82.Surface.LambdaStarIntegerZeroExtension
public import FroehlichSpencer.FS82.Surface.IntegerLatticeCurl
public import FroehlichSpencer.FS82.Surface.IntegerDualFieldWeight
public import FroehlichSpencer.FS82.Surface.BetaDoublePrime
public import FroehlichSpencer.FS82.Surface.SourceIntegerGaugeRelationSetoid
public import FroehlichSpencer.FS82.Surface.IntegerDualGaugeQuotient
public import FroehlichSpencer.FS82.Surface.IntegerDualGaugeQuotientMeasurableSpace
public import FroehlichSpencer.FS82.Surface.IntegerDualGaugeWeight
public import FroehlichSpencer.FS82.Surface.IntegerDualPartitionFunction
public import FroehlichSpencer.FS82.Surface.DiscreteDualMeasure
public import FroehlichSpencer.FS82.SurfaceInfinite.CubeRegion
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalPlaquetteAxes
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalPlaquette
public import FroehlichSpencer.FS82.SurfaceInfinite.InCube
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceCurrentEquiv
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceIntegerCellSign
public import FroehlichSpencer.FS82.SurfaceInfinite.CubeCurvatureMap
public import FroehlichSpencer.FS82.SurfaceInfinite.CubeCurvatureLaw
public import FroehlichSpencer.FS82.SurfaceInfinite.CubeCurvatureLimitState
public import FroehlichSpencer.FS82.SurfaceInfinite.LatticePoint
public import FroehlichSpencer.FS82.SurfaceInfinite.Torus4
public import FroehlichSpencer.FS82.SurfaceInfinite.CellDegree
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalLinkField
public import FroehlichSpencer.FS82.SurfaceInfinite.CellBaseCoordinate
public import FroehlichSpencer.FS82.SurfaceInfinite.CellPoint
public import FroehlichSpencer.FS82.SurfaceInfinite.LinkAxisCell
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalLinkAxisSupport
public import FroehlichSpencer.FS82.SurfaceInfinite.LatticeCharacter
public import FroehlichSpencer.FS82.SurfaceInfinite.Torus4Haar
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalLinkFourierComponent
public import FroehlichSpencer.FS82.SurfaceInfinite.FourierLaplacianSymbol
public import FroehlichSpencer.FS82.SurfaceInfinite.FourierGreenDensity
public import FroehlichSpencer.FS82.SurfaceInfinite.FourierGreenQuadratic
public import FroehlichSpencer.FS82.SurfaceInfinite.CellOrientationSign
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalPlaquetteField
public import FroehlichSpencer.FS82.SurfaceInfinite.FillingPlaquetteEmbedding
public import FroehlichSpencer.FS82.SurfaceInfinite.FillingCurvatureIndexSet
public import FroehlichSpencer.FS82.SurfaceInfinite.FillingCurvaturePairing
public import FroehlichSpencer.FS82.Provider.InfiniteRoot293

-- FROZEN_ANCHOR_PREFIX_BEGIN
@[expose] public section

open MeasureTheory
open Filter Topology
open scoped ComplexConjugate

open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.SurfaceInfinite

noncomputable section

theorem source_infiniteVolume_momentComparison :
  ∃ β₀ : {b : ℝ // 0 < b}, ∃ cPack : ℝ → ℝ,
    (∀ β, β₀.val ≤ β → 0 < cPack β) ∧
    Tendsto (fun β : ℝ => 2 * β * cPack β) atTop (𝓝 0) ∧
    (∀ β, β₀.val ≤ β →
      0 < Surface.betaDoublePrime cPack β ∧
      Surface.betaDoublePrime cPack β < β) ∧
    Tendsto (Surface.betaDoublePrime cPack) atTop atTop ∧
    ∀ β (hβ : β₀.val ≤ β),
      ∀ L : SurfaceInfinite.CubeCurvatureLimitState β (lt_of_lt_of_le β₀.property hβ),
        ∀ μ : SurfaceInfinite.GlobalLinkField,
          Surface.realLatticeBoundary (μ : Surface.RealLatticeChain) = 0 →
          ∀ σ : SurfaceInfinite.GlobalPlaquetteField,
            Surface.realLatticeBoundary (σ : Surface.RealLatticeChain) =
              (μ : Surface.RealLatticeChain) →
            ∀ t : ℝ,
              Real.exp ((t ^ 2 * Surface.betaDoublePrime cPack β / 2) *
                  SurfaceInfinite.fourierGreenQuadratic μ) ≤
                ∫ x, Real.exp (t * SurfaceInfinite.fillingCurvaturePairing σ x) ∂
                  (L.law (SurfaceInfinite.fillingCurvatureIndexSet σ)).toMeasure ∧
              (∫ x, Real.exp (t * SurfaceInfinite.fillingCurvaturePairing σ x) ∂
                  (L.law (SurfaceInfinite.fillingCurvatureIndexSet σ)).toMeasure) ≤
                Real.exp ((t ^ 2 * β / 2) * SurfaceInfinite.fourierGreenQuadratic μ) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.FS82.Provider.InfiniteRoot293.source_infiniteVolume_momentComparison
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end
end FroehlichSpencer.FS82.SurfaceInfinite

end
-- FROZEN_ANCHOR_SUFFIX_END
