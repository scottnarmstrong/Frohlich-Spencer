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
public import FroehlichSpencer.FS82.Surface.SourceIntegerGaugeRelationSetoid
public import FroehlichSpencer.FS82.Surface.IntegerDualGaugeQuotient
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalPlaquetteAxes
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalPlaquette
public import FroehlichSpencer.FS82.SurfaceInfinite.InCube
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceCurrentEquiv
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceIntegerCellSign
public import FroehlichSpencer.FS82.Surface.ExistsUnique_sourceGaugeClass_closedCurrentEquiv
public import FroehlichSpencer.FS82.Surface.SourceIntegerGaugeRelation_isEquivalence

@[expose] public section

open MeasureTheory
open Filter Topology
open scoped ComplexConjugate

open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.SurfaceInfinite

noncomputable section

noncomputable def cubeCurvatureMap (R : RectBox4) (P : Finset GlobalPlaquette)
    (hP : ∀ p ∈ P, inCube R p) : IntegerDualGaugeQuotient R → P → ℤ :=
  fun c p =>
    sourceIntegerCellSign p.1 *
      (sourceCurrentEquiv R c).1
        (dualCellEmbeddingC1 R (Classical.choose (hP p.1 p.2)).1)

end
end FroehlichSpencer.FS82.SurfaceInfinite

end
