module
public import FroehlichSpencer.FS82.Cubical.DualStencil
public import Mathlib.Tactic

public import FroehlichSpencer.FS82.SourceInterface.LiteralSurface
public import FroehlichSpencer.FS82.SourceInterface.OperatorInvariance
public import FroehlichSpencer.FS82.SourceInterface.ProbabilityHelper
public import FroehlichSpencer.FS82.SourceInterface.PartitionHelpers
public import FroehlichSpencer.FS82.SourceInterface.SourceModels
public import FroehlichSpencer.FS82.SourceInterface.CarrierTransport
public import FroehlichSpencer.FS82.SourceInterface.CurlExactness
public import FroehlichSpencer.FS82.Gaussian.LatticeComplex
public import FroehlichSpencer.FS82.Gaussian.IntegerExactness
public import FroehlichSpencer.FS82.Gaussian.IntegerGauge

@[expose] public section

namespace FroehlichSpencer.FS82.Surface

/-- The literal operator restricted to the literal co-closed carrier, using
the proved preservation gate. -/
noncomputable def finiteLatticeHodgeOperatorOnCoClosed_internal (R : RectBox4) :
    W R →ₗ[ℝ] W R where
  toFun μ := ⟨finiteLatticeHodgeOperator R (μ : RealDualField R),
    finiteLatticeHodgeOperator_preservesCoClosed_internal R μ⟩
  map_add' μ ν := by
    apply Subtype.ext
    exact map_add (finiteLatticeHodgeOperator R)
      (μ : RealDualField R) (ν : RealDualField R)
  map_smul' a μ := by
    apply Subtype.ext
    exact map_smul (finiteLatticeHodgeOperator R) a (μ : RealDualField R)

end FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.SourceInterfaceResults

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian


theorem latticeDivergence_eq_zero_iff_full_gate
    (R : FroehlichSpencer.FS82.Surface.RectBox4)
    (μ : FroehlichSpencer.FS82.Surface.RealDualField R) :
    FroehlichSpencer.FS82.Surface.lambdaStarVertexHaloRestriction R
        (FroehlichSpencer.FS82.Surface.fullLatticeDivergence R μ) = 0 ↔
      FroehlichSpencer.FS82.Surface.fullLatticeDivergence R μ = 0 := by
  exact FroehlichSpencer.FS82.Surface.latticeDivergence_eq_zero_iff_full_internal R μ


theorem interiorSupported_coClosed_iff_gate
    (R : FroehlichSpencer.FS82.Surface.RectBox4)
    (μ : FroehlichSpencer.FS82.Surface.RealDualField R)
    (hμ : FroehlichSpencer.FS82.Surface.IsInteriorSupported R μ) :
    μ ∈ FroehlichSpencer.FS82.Surface.GlobalCoClosed R ↔
      μ ∈ FroehlichSpencer.FS82.Surface.W R := by
  exact FroehlichSpencer.FS82.Surface.interiorSupported_coClosed_iff_internal R μ hμ


theorem normalizeIntegerGaugePotential_connectedExterior_gate
    (R : FroehlichSpencer.FS82.Surface.RectBox4)
    (γ : FroehlichSpencer.FS82.Surface.LatticeVertices4 → ℤ)
    (hsupp : ∀ c : FroehlichSpencer.FS82.Surface.LatticeCell,
      FroehlichSpencer.FS82.Surface.latticePotentialGradient γ c ≠ 0 →
        c ∈ Set.range (FroehlichSpencer.FS82.Surface.lambdaStarEmbeddingC1 R)) :
    ∃ γ₀ : FroehlichSpencer.FS82.Surface.LatticeVertices4 → ℤ,
      (∀ c : FroehlichSpencer.FS82.Surface.LatticeCell,
        FroehlichSpencer.FS82.Surface.latticePotentialGradient γ₀ c =
          FroehlichSpencer.FS82.Surface.latticePotentialGradient γ c) ∧
      Set.Finite {x : FroehlichSpencer.FS82.Surface.LatticeVertices4 |
        γ₀ x ≠ 0} ∧
      (∀ x, γ₀ x ≠ 0 →
        ∃ v : FroehlichSpencer.FS82.Surface.DualVertices R,
          FroehlichSpencer.FS82.Surface.dualCellEmbeddingC1 R v.1 =
            FroehlichSpencer.FS82.Surface.latticePotentialVertexCell x) ∧
      (∀ x, FroehlichSpencer.FS82.Surface.isExteriorVertex R x → γ₀ x = 0) ∧
      ∀ η : FroehlichSpencer.FS82.Surface.LatticeVertices4 → ℤ,
        (∀ c : FroehlichSpencer.FS82.Surface.LatticeCell,
          FroehlichSpencer.FS82.Surface.latticePotentialGradient η c =
            FroehlichSpencer.FS82.Surface.latticePotentialGradient γ c) →
        (∀ x, FroehlichSpencer.FS82.Surface.isExteriorVertex R x → η x = 0) →
        η = γ₀ := by
  exact FroehlichSpencer.FS82.Surface.normalizeIntegerGaugePotential_connectedExterior_internal
    R γ hsupp


theorem sourceIntegerGaugeRelation_isEquivalence_gate
    (R : FroehlichSpencer.FS82.Surface.RectBox4) :
    Equivalence
      (FroehlichSpencer.FS82.Surface.sourceIntegerGaugeRelation R) := by
  exact FroehlichSpencer.FS82.Surface.sourceIntegerGaugeRelation_isEquivalence_internal R


/-- Generic uniqueness helper for the quotient-Gaussian gate after the tests
are shown to exhaust the quotient continuous dual. -/
theorem finite_measure_characteristic_uniqueness_helper
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    {μ ν : MeasureTheory.Measure E}
    [MeasureTheory.IsFiniteMeasure μ] [MeasureTheory.IsFiniteMeasure ν]
    (h : MeasureTheory.charFunDual μ = MeasureTheory.charFunDual ν) : μ = ν :=
  finiteMeasures_eq_of_charFunDual_eq h


theorem finiteLatticeHodgeOperator_preservesCoClosed_gate
    (R : FroehlichSpencer.FS82.Surface.RectBox4)
    (μ : FroehlichSpencer.FS82.Surface.W R) :
    FroehlichSpencer.FS82.Surface.finiteLatticeHodgeOperator R
      (μ : FroehlichSpencer.FS82.Surface.RealDualField R) ∈
        FroehlichSpencer.FS82.Surface.W R :=
  FroehlichSpencer.FS82.Surface.finiteLatticeHodgeOperator_preservesCoClosed_internal R μ


theorem existsUnique_finiteLatticeHodgeInverse_gate
    (R : FroehlichSpencer.FS82.Surface.RectBox4) :
    ∃! V : FroehlichSpencer.FS82.Surface.W R →ₗ[ℝ]
        FroehlichSpencer.FS82.Surface.W R,
      ∀ μ : FroehlichSpencer.FS82.Surface.W R,
        FroehlichSpencer.FS82.Surface.finiteLatticeHodgeOperatorOnCoClosed_internal
          R (V μ) = μ := by
  let C := latticeExactOneComplex (B := R.side) R.origin
  let e : FroehlichSpencer.FS82.Surface.W R ≃ₗ[ℝ] coClosed C :=
    FroehlichSpencer.FS82.Surface.literalWEquivCoClosed R
  let E := LinearEquiv.ofInjectiveEndo (hodgeOnCoClosed C)
    (hodgeOnCoClosed_injective C)
  let V : coClosed C →ₗ[ℝ] coClosed C := E.symm.toLinearMap
  have hV (μ : coClosed C) : hodgeOnCoClosed C (V μ) = μ := by
    change E (E.symm μ) = μ
    exact E.apply_symm_apply μ
  let Vsrc : FroehlichSpencer.FS82.Surface.W R →ₗ[ℝ]
      FroehlichSpencer.FS82.Surface.W R :=
    e.symm.toLinearMap.comp (V.comp e.toLinearMap)
  refine ⟨Vsrc, ?_, ?_⟩
  · intro μ
    apply Subtype.ext
    change FroehlichSpencer.FS82.Surface.finiteLatticeHodgeOperator R
        (Vsrc μ : FroehlichSpencer.FS82.Surface.RealDualField R) =
      (μ : FroehlichSpencer.FS82.Surface.RealDualField R)
    rw [FroehlichSpencer.FS82.Surface.finiteLatticeHodgeOperator_bridge R]
    have htransport : e (Vsrc μ) = V (e μ) := by
      change e (e.symm (V (e μ))) = V (e μ)
      exact e.apply_symm_apply _
    have htransport_val := congrArg Subtype.val htransport
    have htransport_val' :
        ((e (Vsrc μ) : coClosed C) : EuclideanSpace ℝ (SourceDualOneCells R.side)) =
          ((((Vsrc μ : FroehlichSpencer.FS82.Surface.W R) :
            FroehlichSpencer.FS82.Surface.RealDualField R) :
              EuclideanSpace ℝ (SourceDualOneCells R.side))) := by
      simpa [e] using
        FroehlichSpencer.FS82.Surface.literalWEquivCoClosed_apply_val R (Vsrc μ)
    have hvector :
        ((((Vsrc μ : FroehlichSpencer.FS82.Surface.W R) :
          FroehlichSpencer.FS82.Surface.RealDualField R) :
            EuclideanSpace ℝ (SourceDualOneCells R.side))) =
          ((V (e μ) : coClosed C) : EuclideanSpace ℝ (SourceDualOneCells R.side)) := by
      calc
        _ = ((e (Vsrc μ) : coClosed C) : EuclideanSpace ℝ (SourceDualOneCells R.side)) :=
          htransport_val'.symm
        _ = ((V (e μ) : coClosed C) : EuclideanSpace ℝ (SourceDualOneCells R.side)) :=
          htransport_val
    have hμval :
        ((e μ : coClosed C) : EuclideanSpace ℝ (SourceDualOneCells R.side)) =
          (((μ : FroehlichSpencer.FS82.Surface.W R) :
            FroehlichSpencer.FS82.Surface.RealDualField R) :
              EuclideanSpace ℝ (SourceDualOneCells R.side)) := by
      simpa [e] using
        FroehlichSpencer.FS82.Surface.literalWEquivCoClosed_apply_val R μ
    have hh := congrArg Subtype.val (hV (e μ))
    change formLaplacian C (V (e μ) : EuclideanSpace ℝ (SourceDualOneCells R.side)) =
      (e μ : EuclideanSpace ℝ (SourceDualOneCells R.side)) at hh
    rw [latticeFormLaplacian_eq_stencil] at hh
    change latticeStencilOperator (B := R.side) R.origin
        ((((Vsrc μ : FroehlichSpencer.FS82.Surface.W R) :
          FroehlichSpencer.FS82.Surface.RealDualField R) :
            EuclideanSpace ℝ (SourceDualOneCells R.side))) =
      (((μ : FroehlichSpencer.FS82.Surface.W R) :
        FroehlichSpencer.FS82.Surface.RealDualField R) :
          EuclideanSpace ℝ (SourceDualOneCells R.side))
    have hop := congrArg (latticeStencilOperator (B := R.side) R.origin) hvector
    exact hop.trans (hh.trans hμval)
  · intro V' hV'
    let Vint : coClosed C →ₗ[ℝ] coClosed C :=
      e.toLinearMap.comp (V'.comp e.symm.toLinearMap)
    have hVint (μ : coClosed C) :
        latticeStencilOperator (B := R.side) R.origin (Vint μ) = μ := by
      have hsrc := congrArg Subtype.val (hV' (e.symm μ))
      change FroehlichSpencer.FS82.Surface.finiteLatticeHodgeOperator R
          (V' (e.symm μ) : FroehlichSpencer.FS82.Surface.RealDualField R) =
        (e.symm μ : FroehlichSpencer.FS82.Surface.RealDualField R) at hsrc
      rw [FroehlichSpencer.FS82.Surface.finiteLatticeHodgeOperator_bridge R] at hsrc
      change latticeStencilOperator (B := R.side) R.origin
          ((((V' (e.symm μ) : FroehlichSpencer.FS82.Surface.W R) :
            FroehlichSpencer.FS82.Surface.RealDualField R) :
              EuclideanSpace ℝ (SourceDualOneCells R.side))) =
        (((e.symm μ : FroehlichSpencer.FS82.Surface.W R) :
          FroehlichSpencer.FS82.Surface.RealDualField R) :
            EuclideanSpace ℝ (SourceDualOneCells R.side)) at hsrc
      have hinter : Vint μ = e (V' (e.symm μ)) := by rfl
      have hinter_val := congrArg Subtype.val hinter
      have hsourceval :
          ((e (V' (e.symm μ)) : coClosed C) :
            EuclideanSpace ℝ (SourceDualOneCells R.side)) =
            ((((V' (e.symm μ) : FroehlichSpencer.FS82.Surface.W R) :
              FroehlichSpencer.FS82.Surface.RealDualField R) :
                EuclideanSpace ℝ (SourceDualOneCells R.side))) := by
        change ((FroehlichSpencer.FS82.Surface.literalWEquivCoClosed R
            (V' (e.symm μ)) : coClosed C) :
              EuclideanSpace ℝ (SourceDualOneCells R.side)) = _
        exact FroehlichSpencer.FS82.Surface.literalWEquivCoClosed_apply_val R
          (V' (e.symm μ))
      have hμval :
          (((e.symm μ : FroehlichSpencer.FS82.Surface.W R) :
            FroehlichSpencer.FS82.Surface.RealDualField R) :
              EuclideanSpace ℝ (SourceDualOneCells R.side)) =
            (μ : EuclideanSpace ℝ (SourceDualOneCells R.side)) := by
        change (((FroehlichSpencer.FS82.Surface.literalWEquivCoClosed R).symm μ :
            FroehlichSpencer.FS82.Surface.W R) :
              FroehlichSpencer.FS82.Surface.RealDualField R) = _
        exact FroehlichSpencer.FS82.Surface.literalWEquivCoClosed_symm_apply_val R μ
      have hvector :
          (Vint μ : EuclideanSpace ℝ (SourceDualOneCells R.side)) =
            ((((V' (e.symm μ) : FroehlichSpencer.FS82.Surface.W R) :
              FroehlichSpencer.FS82.Surface.RealDualField R) :
                EuclideanSpace ℝ (SourceDualOneCells R.side))) := by
        rw [hinter_val, hsourceval]
      have hop := congrArg (latticeStencilOperator (B := R.side) R.origin) hvector
      change latticeStencilOperator (B := R.side) R.origin
          (Vint μ : EuclideanSpace ℝ (SourceDualOneCells R.side)) =
        (μ : EuclideanSpace ℝ (SourceDualOneCells R.side))
      exact hop.trans (hsrc.trans hμval)
    have hH' (μ : coClosed C) : hodgeOnCoClosed C (Vint μ) = μ := by
      apply Subtype.ext
      have hh := hVint μ
      change formLaplacian C (Vint μ : EuclideanSpace ℝ (SourceDualOneCells R.side)) =
        (μ : EuclideanSpace ℝ (SourceDualOneCells R.side))
      rw [latticeFormLaplacian_eq_stencil]
      exact hh
    apply LinearMap.ext
    intro μ
    apply Subtype.ext
    have hpoint : Vint (e μ) = V (e μ) :=
      (hodgeOnCoClosed_injective C) ((hH' (e μ)).trans (hV (e μ)).symm)
    have htransport : e (Vsrc μ) = V (e μ) := by
      change e (e.symm (V (e μ))) = V (e μ)
      exact e.apply_symm_apply _
    have hinter : Vint (e μ) = e (V' μ) := by rfl
    have hsub : V' μ = Vsrc μ := e.injective (hinter.symm.trans (hpoint.trans htransport.symm))
    exact congrArg Subtype.val hsub


theorem latticeCurlKernel_annihilatesCoClosed_gate
    (R : FroehlichSpencer.FS82.Surface.RectBox4)
    (μ : FroehlichSpencer.FS82.Surface.W R) :
    (FroehlichSpencer.FS82.Surface.latticeCurl R).ker ≤
      (InnerProductSpace.toDualMap ℝ
        (FroehlichSpencer.FS82.Surface.RealDualField R)
        (μ : FroehlichSpencer.FS82.Surface.RealDualField R)).ker :=
  FroehlichSpencer.FS82.Surface.latticeCurlKernel_annihilatesCoClosed_gate R μ


end SourceInterfaceResults
end FS82
end FroehlichSpencer
