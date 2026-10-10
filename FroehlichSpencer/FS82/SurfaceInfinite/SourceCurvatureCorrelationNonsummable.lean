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
public import FroehlichSpencer.FS82.Surface.DualEmbedCoordC1
public import FroehlichSpencer.FS82.Surface.DualCellEmbeddingC1
public import FroehlichSpencer.FS82.Surface.LambdaStarEmbeddingC1
public import FroehlichSpencer.FS82.Surface.LatticeIsEdge
public import FroehlichSpencer.FS82.Surface.LatticeRankBefore
public import FroehlichSpencer.FS82.Surface.LatticeBasis
public import FroehlichSpencer.FS82.Surface.LatticeEdgeCell
public import FroehlichSpencer.FS82.Surface.LatticeCoboundaryBasis
public import FroehlichSpencer.FS82.Surface.LatticeCoboundary
public import FroehlichSpencer.FS82.Surface.SourceClosedIntegerCurrent
public import FroehlichSpencer.FS82.Surface.IntegerDualField
public import FroehlichSpencer.FS82.Surface.LatticeVertices4
public import FroehlichSpencer.FS82.Surface.LatticePotentialGradient
public import FroehlichSpencer.FS82.Surface.SourceIntegerGaugeRelation
public import FroehlichSpencer.FS82.Surface.LambdaStarIntegerZeroExtension
public import FroehlichSpencer.FS82.Surface.IntegerLatticeCurl
public import FroehlichSpencer.FS82.Surface.IntegerDualFieldWeight
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
public import FroehlichSpencer.FS82.SurfaceInfinite.SourcePointCoordinate
public import FroehlichSpencer.FS82.SurfaceInfinite.DualCurvatureCell
public import FroehlichSpencer.FS82.SurfaceInfinite.DualCurvatureAt
public import FroehlichSpencer.FS82.SurfaceInfinite.PairPlaquettes
public import FroehlichSpencer.FS82.SurfaceInfinite.PairProduct
public import FroehlichSpencer.FS82.SurfaceInfinite.CurvatureCylinderState
public import FroehlichSpencer.FS82.SurfaceInfinite.DualCurvatureCorrelation
public import FroehlichSpencer.FS82.SurfaceInfinite.AbsolutelySummableCorrelation
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceLatticeShift
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslateCoordinate
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslateCell
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslateCellAdd
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslateCellZero
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceGlobalPlaquetteAxesTranslate
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslatePlaquetteEquiv
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslatePlaquettes
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslatePlaquetteIndex
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceUntranslateCurvatureAssignment
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslateCylinderLaw
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceCubeStateToCylinderState
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceShiftBoxSet
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceShiftBoxSetFinite
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceShiftBox
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceShiftUniform
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceFiniteShiftAverage
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceAveragedCylinderLaw
public import FroehlichSpencer.FS82.Provider.InfiniteRoot211

-- FROZEN_ANCHOR_PREFIX_BEGIN
@[expose] public section

open MeasureTheory
open Filter Topology
open scoped ComplexConjugate

open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.SurfaceInfinite

noncomputable section

theorem source_curvatureCorrelation_nonsummable :
    ∃ β₁ : {b : ℝ // 0 < b},
      ∀ β (hβ : β₁.val ≤ β),
        ∃ L : SurfaceInfinite.CubeCurvatureLimitState β
            (lt_of_lt_of_le β₁.property hβ),
          ∃ s : ℕ → ℕ, StrictMono s ∧
            ∃ S : SurfaceInfinite.CurvatureCylinderState,
              (∀ P x, Tendsto
                (fun k => (SurfaceInfinite.sourceAveragedCylinderLaw
                  (SurfaceInfinite.sourceCubeStateToCylinderState L) (s k) P x).toReal)
                atTop (𝓝 ((S.law P x).toReal))) ∧
              (∀ a P, SurfaceInfinite.sourceTranslateCylinderLaw S a P = S.law P) ∧
              ¬ SurfaceInfinite.AbsolutelySummableCorrelation
                (SurfaceInfinite.dualCurvatureCorrelation S) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.FS82.Provider.InfiniteRoot211.source_curvatureCorrelation_nonsummable
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end
end FroehlichSpencer.FS82.SurfaceInfinite

end
-- FROZEN_ANCHOR_SUFFIX_END
