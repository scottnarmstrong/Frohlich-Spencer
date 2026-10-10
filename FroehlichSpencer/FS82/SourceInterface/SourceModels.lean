module

public import FroehlichSpencer.FS82.SourceInterface.LiteralSurface
public import FroehlichSpencer.FS82.SourceInterface.ProbabilityHelper
public import FroehlichSpencer.FS82.SourceInterface.PartitionHelpers

@[expose] public section

open scoped BigOperators
open Filter
open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.SourceModels

namespace HodgeGaussian
class QuotientGaussianModelInputs where
  inverse : ∀ R : RectBox4, W R →ₗ[ℝ] W R
  test : ∀ R : RectBox4, W R → StrongDual ℝ (LatticeGaugeQuotient R)
variable [QuotientGaussianModelInputs]
noncomputable def finiteLatticeHodgeInverse (R : RectBox4) : W R →ₗ[ℝ] W R :=
  QuotientGaussianModelInputs.inverse R
noncomputable def latticeQuotientTestFunctional (R : RectBox4) (μ : W R) :
    StrongDual ℝ (LatticeGaugeQuotient R) :=
  QuotientGaussianModelInputs.test R μ
def SourceQuotientGaussianSpec (R : RectBox4) (β : ℝ) (_hβ : 0 < β)
    (P : MeasureTheory.Measure (LatticeGaugeQuotient R)) : Prop :=
  MeasureTheory.IsProbabilityMeasure P ∧
  ∀ μ : W R,
    MeasureTheory.charFun
        (MeasureTheory.Measure.map (latticeQuotientTestFunctional R μ) P) 1 =
      Complex.exp (-↑((β / 2) * inner ℝ (μ : RealDualField R)
        (finiteLatticeHodgeInverse R μ : RealDualField R)))
variable (R : RectBox4) (β : ℝ) (hβ : 0 < β)
end HodgeGaussian

namespace IntegerDualModel
class SourceRelationEquivalenceGate : Prop where
  proof : ∀ R : RectBox4, Equivalence (sourceIntegerGaugeRelation R)
variable [SourceRelationEquivalenceGate]
theorem sourceIntegerGaugeRelation_isEquivalence_internal (R : RectBox4) :
    Equivalence (sourceIntegerGaugeRelation R) :=
  SourceRelationEquivalenceGate.proof R
noncomputable def sourceIntegerGaugeRelationSetoid (R : RectBox4) :
    Setoid (IntegerDualField R) :=
  ⟨sourceIntegerGaugeRelation R, sourceIntegerGaugeRelation_isEquivalence_internal R⟩

abbrev IntegerDualGaugeQuotient (R : RectBox4) :=
  Quotient (sourceIntegerGaugeRelationSetoid R)


instance integerDualGaugeQuotientMeasurableSpace (R : RectBox4) :
    MeasurableSpace (IntegerDualGaugeQuotient R) := ⊤
class IntegerWeightInvariantGate : Prop where
  invariant : ∀ (R : RectBox4) (β : ℝ) (hβ : 0 < β)
      (α α' : IntegerDualField R), sourceIntegerGaugeRelation R α α' →
      integerDualFieldWeight R β hβ α = integerDualFieldWeight R β hβ α'
variable [IntegerWeightInvariantGate]
omit [SourceRelationEquivalenceGate] in
theorem integerDualFieldWeight_respectsGauge_internal (R : RectBox4) (β : ℝ) (hβ : 0 < β)
    (α α' : IntegerDualField R) (hα : sourceIntegerGaugeRelation R α α') :
    integerDualFieldWeight R β hβ α = integerDualFieldWeight R β hβ α' :=
  IntegerWeightInvariantGate.invariant R β hβ α α' hα
noncomputable def integerDualGaugeWeight (R : RectBox4) (β : ℝ) (hβ : 0 < β) :
    IntegerDualGaugeQuotient R → ℝ :=
  Quotient.lift (integerDualFieldWeight R β hβ)
    (fun α α' hα => integerDualFieldWeight_respectsGauge_internal R β hβ α α' hα)
class PairingInvariantGate : Prop where
  invariant : ∀ (R : RectBox4) (μ : W R) (α α' : IntegerDualField R),
    sourceIntegerGaugeRelation R α α' →
      (∑ e : DualLinks R, (α e : ℝ) * (μ : RealDualField R) e) =
        ∑ e : DualLinks R, (α' e : ℝ) * (μ : RealDualField R) e
variable [PairingInvariantGate]
omit [SourceRelationEquivalenceGate] [IntegerWeightInvariantGate] in
theorem integerDualPairing_respectsGauge (R : RectBox4) (μ : W R)
    (α α' : IntegerDualField R) (h : sourceIntegerGaugeRelation R α α') :
    (∑ e : DualLinks R, (α e : ℝ) * (μ : RealDualField R) e) =
      ∑ e : DualLinks R, (α' e : ℝ) * (μ : RealDualField R) e :=
  PairingInvariantGate.invariant R μ α α' h

noncomputable def integerDualPairing (R : RectBox4) (μ : W R) :
    IntegerDualGaugeQuotient R → ℝ :=
  Quotient.lift
    (fun α => ∑ e : DualLinks R, (α e : ℝ) * (μ : RealDualField R) e)
    (integerDualPairing_respectsGauge R μ)
/-- Existence and uniqueness of the positive integer-dual partition sum. -/
class IntegerPartitionUniqueGate : Prop where
  unique : ∀ (R : RectBox4) (β : ℝ) (hβ : 0 < β),
    ∃! Z : ℝ, HasSum (integerDualGaugeWeight R β hβ) Z ∧ 0 < Z
variable [IntegerPartitionUniqueGate]
omit [PairingInvariantGate] in
theorem existsUnique_integerDualPartitionFunction (R : RectBox4) (β : ℝ)
    (hβ : 0 < β) :
    ∃! Z : ℝ, HasSum (integerDualGaugeWeight R β hβ) Z ∧ 0 < Z :=
  IntegerPartitionUniqueGate.unique R β hβ
variable (R : RectBox4) (β : ℝ) (hβ : 0 < β)
variable (Z_R : ℝ)
noncomputable def integerDualPartitionFunction (R : RectBox4) (β : ℝ)
    (hβ : 0 < β) : ℝ :=
  Classical.choose (existsUnique_integerDualPartitionFunction R β hβ).exists
noncomputable def discreteDualMeasure (R : RectBox4) (β : ℝ) (hβ : 0 < β) :
    MeasureTheory.Measure (IntegerDualGaugeQuotient R) :=
  MeasureTheory.Measure.sum fun c =>
    ENNReal.ofReal
      (integerDualGaugeWeight R β hβ c / integerDualPartitionFunction R β hβ) •
      MeasureTheory.Measure.dirac c

omit [PairingInvariantGate] [IntegerPartitionUniqueGate] in
theorem integerDualGaugeWeight_pos (R : RectBox4) (β : ℝ) (hβ : 0 < β)
    (c : IntegerDualGaugeQuotient R) :
    0 < integerDualGaugeWeight R β hβ c := by
  refine Quotient.inductionOn c ?_
  intro α
  change 0 < integerDualFieldWeight R β hβ α
  unfold integerDualFieldWeight
  exact Real.exp_pos _

class IntegerDualGaugeWeightSummabilityGate : Prop where
  summable : ∀ (R : RectBox4) (β : ℝ) (hβ : 0 < β),
    Summable (integerDualGaugeWeight R β hβ)

omit [PairingInvariantGate] [IntegerPartitionUniqueGate] in
theorem exists_positive_integerDualGaugeWeight (R : RectBox4) (β : ℝ)
    (hβ : 0 < β) :
    ∃ c : IntegerDualGaugeQuotient R,
      0 < integerDualGaugeWeight R β hβ c := by
  let α₀ : IntegerDualField R := fun _ => 0
  let c₀ : IntegerDualGaugeQuotient R :=
    Quotient.mk (sourceIntegerGaugeRelationSetoid R) α₀
  exact ⟨c₀, integerDualGaugeWeight_pos R β hβ c₀⟩

omit [PairingInvariantGate] [IntegerPartitionUniqueGate] in
theorem existsUnique_integerDualPartitionFunction_of_summable
    [IntegerDualGaugeWeightSummabilityGate]
    (R : RectBox4) (β : ℝ) (hβ : 0 < β) :
    ∃! Z : ℝ, HasSum (integerDualGaugeWeight R β hβ) Z ∧ 0 < Z := by
  exact existsUnique_positive_hasSum_of_summable
    (integerDualGaugeWeight R β hβ)
    (fun c => (integerDualGaugeWeight_pos R β hβ c).le)
    (IntegerDualGaugeWeightSummabilityGate.summable R β hβ)
    (exists_positive_integerDualGaugeWeight R β hβ)


noncomputable def discreteDualMoment (R : RectBox4) (β : ℝ) (hβ : 0 < β)
    (ε : ℝ) (μ : W R) : ENNReal :=
  ∫⁻ c, ENNReal.ofReal
    (Real.exp (ε * integerDualPairing R μ c)) ∂discreteDualMeasure R β hβ
end IntegerDualModel

end FroehlichSpencer.FS82.SourceModels
end
