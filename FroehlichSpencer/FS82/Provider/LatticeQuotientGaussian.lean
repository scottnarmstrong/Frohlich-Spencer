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
public import FroehlichSpencer.FS82.Surface.SourceQuotientGaussianSpec
public import FroehlichSpencer.FS82.Bridge.QuotientGaussian
public import FroehlichSpencer.FS82.SourceInterface.SourceTheorems

/-! FS82 characterization proof. -/

@[expose] public section

open scoped BigOperators
open Filter
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.Gaussian
namespace FroehlichSpencer.FS82.Provider


private theorem transportedInverseSolves (R : RectBox4) (μ : W R) :
    finiteLatticeHodgeOperatorOnCoClosed R
      (FroehlichSpencer.FS82.QuotientGaussianBridge.transportedFiniteLatticeHodgeInverse R μ) = μ := by
  let C := latticeExactOneComplex (B := R.side) R.origin
  let e : W R ≃ₗ[ℝ] coClosed C := literalWEquivCoClosed R
  apply Subtype.ext
  change finiteLatticeHodgeOperator R
      ((FroehlichSpencer.FS82.QuotientGaussianBridge.transportedFiniteLatticeHodgeInverse R μ : W R) : RealDualField R) =
    (μ : RealDualField R)
  rw [finiteLatticeHodgeOperator_bridge R]
  have htransport : e (FroehlichSpencer.FS82.QuotientGaussianBridge.transportedFiniteLatticeHodgeInverse R μ) =
      hodgeInverseOnCoClosed C (e μ) := by
    rfl
  have htransport_val := congrArg Subtype.val htransport
  have htransport_val' :
      ((e (FroehlichSpencer.FS82.QuotientGaussianBridge.transportedFiniteLatticeHodgeInverse R μ) : coClosed C) :
          EuclideanSpace ℝ (SourceDualOneCells R.side)) =
        (((FroehlichSpencer.FS82.QuotientGaussianBridge.transportedFiniteLatticeHodgeInverse R μ : W R) : RealDualField R) :
          EuclideanSpace ℝ (SourceDualOneCells R.side)) := by
    simpa [e] using literalWEquivCoClosed_apply_val R
      (FroehlichSpencer.FS82.QuotientGaussianBridge.transportedFiniteLatticeHodgeInverse R μ)
  have hvector :
      (((FroehlichSpencer.FS82.QuotientGaussianBridge.transportedFiniteLatticeHodgeInverse R μ : W R) : RealDualField R) :
          EuclideanSpace ℝ (SourceDualOneCells R.side)) =
        ((hodgeInverseOnCoClosed C (e μ) : coClosed C) :
          EuclideanSpace ℝ (SourceDualOneCells R.side)) := by
    calc
      _ = ((e (FroehlichSpencer.FS82.QuotientGaussianBridge.transportedFiniteLatticeHodgeInverse R μ) : coClosed C) :
          EuclideanSpace ℝ (SourceDualOneCells R.side)) := htransport_val'.symm
      _ = _ := htransport_val
  have hμval :
      ((e μ : coClosed C) : EuclideanSpace ℝ (SourceDualOneCells R.side)) =
        (((μ : W R) : RealDualField R) : EuclideanSpace ℝ (SourceDualOneCells R.side)) := by
    simpa [e] using literalWEquivCoClosed_apply_val R μ
  have hh := congrArg Subtype.val (hodgeOnCoClosed_hodgeInverse C (e μ))
  change formLaplacian C (hodgeInverseOnCoClosed C (e μ) : EuclideanSpace ℝ (SourceDualOneCells R.side)) =
      (e μ : EuclideanSpace ℝ (SourceDualOneCells R.side)) at hh
  rw [latticeFormLaplacian_eq_stencil] at hh
  have hop := congrArg (latticeStencilOperator (B := R.side) R.origin) hvector
  exact hop.trans (hh.trans hμval)

private theorem transportedInverse_eq_source (R : RectBox4) :
    FroehlichSpencer.FS82.QuotientGaussianBridge.transportedFiniteLatticeHodgeInverse R =
      finiteLatticeHodgeInverse R := by
  obtain ⟨V, hV, huniq⟩ :=
    FroehlichSpencer.FS82.SourceInterfaceTheorems.existsUnique_finiteLatticeHodgeInverse_gate R
  have hselected := Classical.choose_spec
    (FroehlichSpencer.FS82.SourceInterfaceTheorems.existsUnique_finiteLatticeHodgeInverse_gate R).exists
  calc
    FroehlichSpencer.FS82.QuotientGaussianBridge.transportedFiniteLatticeHodgeInverse R = V :=
      huniq _ (transportedInverseSolves R)
    _ = finiteLatticeHodgeInverse R := (huniq _ hselected).symm

private theorem sourceTest_eq_internal (R : RectBox4) (μ : W R) :
    latticeQuotientTestFunctional R μ =
      FroehlichSpencer.FS82.QuotientGaussianBridge.gateQuotientTestFunctional R μ := by
  rfl

private theorem quotientGaussianSpec_iff (R : RectBox4) (β : ℝ) (hβ : 0 < β)
    (P : MeasureTheory.Measure (LatticeGaugeQuotient R)) :
    SourceQuotientGaussianSpec R β hβ P ↔
      @FroehlichSpencer.FS82.SourceModels.HodgeGaussian.SourceQuotientGaussianSpec
        FroehlichSpencer.FS82.QuotientGaussianBridge.quotientGaussianModelInputs R β hβ P := by
  constructor
  · rintro ⟨hp, hchar⟩
    constructor
    · exact hp
    · intro μ
      change MeasureTheory.charFun
        (MeasureTheory.Measure.map
          (FroehlichSpencer.FS82.QuotientGaussianBridge.gateQuotientTestFunctional R μ) P) 1 =
          Complex.exp (-↑((β / 2) * inner ℝ (μ : RealDualField R)
            (FroehlichSpencer.FS82.QuotientGaussianBridge.transportedFiniteLatticeHodgeInverse R μ : RealDualField R)))
      rw [← sourceTest_eq_internal R μ, transportedInverse_eq_source R]
      exact hchar μ
  · rintro ⟨hp, hchar⟩
    constructor
    · exact hp
    · change ∀ μ : W R,
        MeasureTheory.charFun
          (MeasureTheory.Measure.map
            (FroehlichSpencer.FS82.QuotientGaussianBridge.gateQuotientTestFunctional R μ) P) 1 =
            Complex.exp (-↑((β / 2) * inner ℝ (μ : RealDualField R)
              (FroehlichSpencer.FS82.QuotientGaussianBridge.transportedFiniteLatticeHodgeInverse R μ : RealDualField R))) at hchar
      intro μ
      have h := hchar μ
      rw [← sourceTest_eq_internal R μ, transportedInverse_eq_source R] at h
      exact h

theorem existsUnique_latticeQuotientGaussian
    (R : RectBox4) (β : ℝ) (hβ : 0 < β) :
    ∃! P : MeasureTheory.Measure (Surface.LatticeGaugeQuotient R),
      SourceQuotientGaussianSpec
        R β hβ P := by
  exact (existsUnique_congr (fun P =>
    quotientGaussianSpec_iff R β hβ P)).mpr (FroehlichSpencer.FS82.SourceInterfaceTheorems.existsUnique_latticeQuotientGaussian_gate R β hβ)

end FroehlichSpencer.FS82.Provider

end
