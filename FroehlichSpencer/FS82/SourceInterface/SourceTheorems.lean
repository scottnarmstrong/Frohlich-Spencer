module

public import FroehlichSpencer.FS82.SourceInterface.SourceTheoremsBasic
public import FroehlichSpencer.FS82.SourceInterface.PartitionExistence
public import FroehlichSpencer.FS82.SourceInterface.GaussianExistence
public import FroehlichSpencer.FS82.SourceInterface.GaugeCurrentEquivalence
public import FroehlichSpencer.FS82.SourceInterface.SourceModels
public import FroehlichSpencer.FS82.SourceInterface.GaugeWeightGate
public import FroehlichSpencer.FS82.SourceInterface.PairingInvariant

@[expose] public section

open scoped BigOperators
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.SourceModels.IntegerDualModel

namespace FroehlichSpencer.FS82.SourceInterfaceTheorems

local instance sourceRelationEquivalenceGate : SourceRelationEquivalenceGate :=
  ⟨Surface.sourceIntegerGaugeRelation_isEquivalence_internal⟩

local instance integerWeightInvariantGate : IntegerWeightInvariantGate :=
  ⟨Surface.integerDualFieldWeight_respectsGauge_internal⟩

/-- the literal arbitrary-potential relation is equivalent to the
finite supported exact-shift condition used by the integer cubical complex. -/
theorem sourceIntegerGaugeRelation_iff_sourceExactShiftSupportCondition226_gate
    (R : RectBox4) (α α' : IntegerDualField R) :
    sourceIntegerGaugeRelation R α α' ↔
      FroehlichSpencer.FS82.Gaussian.sourceExactShiftSupportCondition226
        R.origin
        (FroehlichSpencer.FS82.Gaussian.sourceIntegerSignTwist α')
        (FroehlichSpencer.FS82.Gaussian.sourceIntegerSignTwist α) := by
  exact Surface.sourceIntegerGaugeRelation_iff_sourceExactShiftSupportCondition226_internal
    R α α'

/-- the source curl weight descends to gauge classes. -/
theorem integerDualFieldWeight_respectsGauge_gate
    (R : RectBox4) (β : ℝ) (hβ : 0 < β) (α α' : IntegerDualField R)
    (hα : sourceIntegerGaugeRelation R α α') :
    integerDualFieldWeight R β hβ α = integerDualFieldWeight R β hβ α' := by
  exact Surface.integerDualFieldWeight_respectsGauge_internal R β hβ α α' hα

/-- the integer pairing is invariant under source gauge changes on
the co-closed test carrier. -/
theorem integerDualPairing_respectsGauge_gate
    (R : RectBox4) (μ : W R) (α α' : IntegerDualField R)
    (h : sourceIntegerGaugeRelation R α α') :
    (∑ e : DualLinks R, (α e : ℝ) * (μ : RealDualField R) e) =
      ∑ e : DualLinks R, (α' e : ℝ) * (μ : RealDualField R) e := by
  exact FroehlichSpencer.FS82.SourcePairingInvariant.integerDualPairing_respectsGauge
    R μ α α' h

/-- Exact source halo/divergence identity. -/
theorem latticeDivergence_eq_zero_iff_full_gate
    (R : RectBox4) (μ : RealDualField R) :
    Surface.lambdaStarVertexHaloRestriction R
        (Surface.fullLatticeDivergence R μ) = 0 ↔
      Surface.fullLatticeDivergence R μ = 0 := by
  exact SourceInterfaceResults.latticeDivergence_eq_zero_iff_full_gate R μ

/-- Exact interior-supported co-closed-carrier identity. -/
theorem interiorSupported_coClosed_iff_gate
    (R : RectBox4) (μ : RealDualField R)
    (hμ : Surface.IsInteriorSupported R μ) :
    μ ∈ Surface.GlobalCoClosed R ↔ μ ∈ Surface.W R := by
  exact SourceInterfaceResults.interiorSupported_coClosed_iff_gate R μ hμ

/-- Exact arbitrary-potential exterior normalization gate. -/
theorem normalizeIntegerGaugePotential_connectedExterior_gate
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
  exact SourceInterfaceResults.normalizeIntegerGaugePotential_connectedExterior_gate R γ hsupp

/-- Exact source relation equivalence gate. -/
theorem sourceIntegerGaugeRelation_isEquivalence_gate (R : RectBox4) :
    Equivalence (sourceIntegerGaugeRelation R) := by
  exact SourceInterfaceResults.sourceIntegerGaugeRelation_isEquivalence_gate R

/-- the literal gauge quotient is equivalent to the finite carrier of
closed integer currents supported on the source C1 plaquettes. -/
noncomputable def sourceGaugeClass_closedCurrentEquiv_gate (R : RectBox4) :
    IntegerDualGaugeQuotient R ≃ Surface.SourceClosedIntegerCurrent R := by
  letI : SourceRelationEquivalenceGate :=
    ⟨sourceIntegerGaugeRelation_isEquivalence_gate⟩
  exact Surface.GaugeCurrentEquivalence.sourceGaugeClass_closedCurrentEquiv R

/-- Exact finite Hodge-operator preservation gate. -/
theorem finiteLatticeHodgeOperator_preservesCoClosed_gate
    (R : RectBox4) (μ : W R) :
    Surface.finiteLatticeHodgeOperator R (μ : RealDualField R) ∈ W R := by
  exact SourceInterfaceResults.finiteLatticeHodgeOperator_preservesCoClosed_gate R μ

/-- Exact finite Hodge inverse existence-and-uniqueness gate. -/
theorem existsUnique_finiteLatticeHodgeInverse_gate (R : RectBox4) :
    ∃! V : W R →ₗ[ℝ] W R,
      ∀ μ : W R,
        Surface.finiteLatticeHodgeOperatorOnCoClosed_internal R (V μ) = μ := by
  exact SourceInterfaceResults.existsUnique_finiteLatticeHodgeInverse_gate R

/-- Exact annihilation of the co-closed tests by the literal curl kernel. -/
theorem latticeCurlKernel_annihilatesCoClosed_gate
    (R : RectBox4) (μ : W R) :
    (Surface.latticeCurl R).ker ≤
      (InnerProductSpace.toDualMap ℝ (RealDualField R)
        (μ : RealDualField R)).ker := by
  exact SourceInterfaceResults.latticeCurlKernel_annihilatesCoClosed_gate R μ


theorem existsUnique_latticeQuotientGaussian_gate
    (R : RectBox4) (β : ℝ) (hβ : 0 < β) :
    ∃! P : MeasureTheory.Measure (Surface.LatticeGaugeQuotient R),
      FroehlichSpencer.FS82.SourceModels.HodgeGaussian.SourceQuotientGaussianSpec
        R β hβ P := by
  exact FroehlichSpencer.FS82.QuotientGaussianBridge.existsUnique_sourceQuotientGaussian R β hβ


/-- the literal source partition function exists uniquely and is
strictly positive. -/
theorem existsUnique_integerDualPartitionFunction_gate (R : RectBox4)
    (β : ℝ) (hβ : 0 < β) :
    ∃! Z : ℝ, HasSum (integerDualGaugeWeight R β hβ) Z ∧ 0 < Z := by
  exact FroehlichSpencer.FS82.SourceInterface.existsUnique_integerDualPartitionFunction R β hβ


end FroehlichSpencer.FS82.SourceInterfaceTheorems
end
