/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Surface.RectBox4
public import FroehlichSpencer.FS82.Surface.RectBox4ShortestSide
public import FroehlichSpencer.FS82.Surface.RectBox4LongestSide
public import FroehlichSpencer.FS82.Surface.IsLogThickRectBox4
public import FroehlichSpencer.FS82.Surface.DualCoord
public import FroehlichSpencer.FS82.Surface.DualCell
public import FroehlichSpencer.FS82.Surface.DualCellAxes
public import FroehlichSpencer.FS82.Surface.DualCellDegree
public import FroehlichSpencer.FS82.Surface.DualCellFintype
public import FroehlichSpencer.FS82.Surface.DualCellDecidableEq
public import FroehlichSpencer.FS82.Surface.DualVertices
public import FroehlichSpencer.FS82.Surface.DualVerticesFintype
public import FroehlichSpencer.FS82.Surface.DualVerticesDecidableEq
public import FroehlichSpencer.FS82.Surface.DualLinks
public import FroehlichSpencer.FS82.Surface.DualLinksFintype
public import FroehlichSpencer.FS82.Surface.DualLinksDecidableEq
public import FroehlichSpencer.FS82.Surface.DualPlaquettes
public import FroehlichSpencer.FS82.Surface.DualPlaquettesFintype
public import FroehlichSpencer.FS82.Surface.DualPlaquettesDecidableEq
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
public import FroehlichSpencer.FS82.Surface.LatticeDeltaD
public import FroehlichSpencer.FS82.Surface.CastLatticeChain
public import FroehlichSpencer.FS82.Surface.RealifyLatticeLinearMap
public import FroehlichSpencer.FS82.Surface.RealLatticeBoundary
public import FroehlichSpencer.FS82.Surface.RealLatticeCoboundary
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
public import FroehlichSpencer.FS82.Surface.LambdaStarVertexHaloFinset
public import FroehlichSpencer.FS82.Surface.DualVertexHalo
public import FroehlichSpencer.FS82.Surface.LambdaStarVertexHaloRestriction
public import FroehlichSpencer.FS82.Surface.LambdaStarVertexDivergence
public import FroehlichSpencer.FS82.Surface.GlobalCoClosed
public import FroehlichSpencer.FS82.Surface.W
public import FroehlichSpencer.FS82.Surface.LatticeCurl
public import FroehlichSpencer.FS82.Surface.LatticeGaugeQuotient
public import FroehlichSpencer.FS82.Surface.IntegerDualField
public import FroehlichSpencer.FS82.Surface.LatticeVertices4
public import FroehlichSpencer.FS82.Surface.LatticePotentialGradient
public import FroehlichSpencer.FS82.Surface.LatticePotentialVertexCell
public import FroehlichSpencer.FS82.Surface.IsExteriorVertex
public import FroehlichSpencer.FS82.Surface.SourceIntegerGaugeRelation
public import FroehlichSpencer.FS82.Surface.LambdaStarIntegerZeroExtension
public import FroehlichSpencer.FS82.Surface.IntegerLatticeCurl
public import FroehlichSpencer.FS82.Surface.IntegerDualFieldWeight
public import FroehlichSpencer.FS82.Surface.BetaDoublePrime
public import FroehlichSpencer.FS82.Bridge.GaugeRelation
public import FroehlichSpencer.FS82.SourceInterface.SourceTheorems

/-! FS82 characterization proof. -/

@[expose] public section

open scoped BigOperators
open Filter
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.Gaussian
namespace FroehlichSpencer.FS82.Provider


theorem normalizeIntegerGaugePotential_connectedExterior
    (R : RectBox4) (γ : Surface.LatticeVertices4 → ℤ)
    (hsupp : ∀ c : Surface.LatticeCell,
      Surface.latticePotentialGradient γ c ≠ 0 →
        c ∈ Set.range (Surface.lambdaStarEmbeddingC1 R)) :
    ∃ γ₀ : Surface.LatticeVertices4 → ℤ,
      (∀ c : Surface.LatticeCell,
        Surface.latticePotentialGradient γ₀ c =
          Surface.latticePotentialGradient γ c) ∧
      Set.Finite {x : Surface.LatticeVertices4 | γ₀ x ≠ 0} ∧
      (∀ x, γ₀ x ≠ 0 →
        ∃ v : DualVertices R,
          Surface.dualCellEmbeddingC1 R v.1 =
            Surface.latticePotentialVertexCell x) ∧
      (∀ x, Surface.isExteriorVertex R x → γ₀ x = 0) ∧
      ∀ η : Surface.LatticeVertices4 → ℤ,
        (∀ c : Surface.LatticeCell,
          Surface.latticePotentialGradient η c =
            Surface.latticePotentialGradient γ c) →
        (∀ x, Surface.isExteriorVertex R x → η x = 0) → η = γ₀ := by
  exact FroehlichSpencer.FS82.SourceInterfaceTheorems.normalizeIntegerGaugePotential_connectedExterior_gate R γ hsupp

end FroehlichSpencer.FS82.Provider

end
