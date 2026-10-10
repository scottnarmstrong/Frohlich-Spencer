module

public import FroehlichSpencer.FS82.SourceInterface.SourceTheoremsBasic
public import FroehlichSpencer.FS82.SourceInterface.PartitionExistence
public import FroehlichSpencer.FS82.SourceInterface.GaugeCurrentEquivalence
public import FroehlichSpencer.FS82.SourceInterface.SourceModels

@[expose] public section

open scoped BigOperators
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.SourceModels.IntegerDualModel

namespace FroehlichSpencer.FS82.SourceInterface

local instance sourceRelationEquivalenceGate : SourceRelationEquivalenceGate :=
  ⟨FroehlichSpencer.FS82.SourceInterfaceResults.sourceIntegerGaugeRelation_isEquivalence_gate⟩

local instance integerWeightInvariantGate : IntegerWeightInvariantGate :=
  ⟨FroehlichSpencer.FS82.Surface.integerDualFieldWeight_respectsGauge_internal⟩

noncomputable def dualPlaquetteLatticeEmbedding (R : RectBox4) :
    DualPlaquettes R ↪ LatticeCell where
  toFun p := dualCellEmbeddingC1 R p.1
  inj' := by
    intro p q hpq
    apply Subtype.ext
    exact (dualCellEmbeddingC1 R).injective hpq

noncomputable def closedCurrentCoordinatesFinsupp (R : RectBox4)
    (J : FroehlichSpencer.FS82.Surface.SourceClosedIntegerCurrent R) :
    DualPlaquettes R →₀ ℤ :=
  Finsupp.comapDomain (dualPlaquetteLatticeEmbedding R) J.1
    (dualPlaquetteLatticeEmbedding R).injective.injOn

theorem closedCurrentCoordinatesFinsupp_emb (R : RectBox4)
    (J : FroehlichSpencer.FS82.Surface.SourceClosedIntegerCurrent R) :
    Finsupp.embDomain (dualPlaquetteLatticeEmbedding R)
      (closedCurrentCoordinatesFinsupp R J) = J.1 := by
  dsimp [closedCurrentCoordinatesFinsupp]
  apply Finsupp.embDomain_comapDomain
  intro c hc
  obtain ⟨p, hp⟩ := J.2.2 c hc
  exact ⟨p, hp⟩

noncomputable def closedCurrentCoordinates (R : RectBox4)
    (J : FroehlichSpencer.FS82.Surface.SourceClosedIntegerCurrent R) :
    DualPlaquettes R → ℤ :=
  closedCurrentCoordinatesFinsupp R J

theorem closedCurrentCoordinates_injective (R : RectBox4) :
    Function.Injective (closedCurrentCoordinates R) := by
  intro J K h
  apply Subtype.ext
  have hcoords : closedCurrentCoordinatesFinsupp R J =
      closedCurrentCoordinatesFinsupp R K := by
    ext p
    exact congrFun h p
  have hJ := closedCurrentCoordinatesFinsupp_emb R J
  have hK := closedCurrentCoordinatesFinsupp_emb R K
  calc
    J.1 = Finsupp.embDomain (dualPlaquetteLatticeEmbedding R)
        (closedCurrentCoordinatesFinsupp R J) := hJ.symm
    _ = Finsupp.embDomain (dualPlaquetteLatticeEmbedding R)
        (closedCurrentCoordinatesFinsupp R K) := by rw [hcoords]
    _ = K.1 := hK

theorem closedCurrent_sqnorm_eq_coordinates (R : RectBox4)
    (J : FroehlichSpencer.FS82.Surface.SourceClosedIntegerCurrent R) :
    (∑ c ∈ J.1.support, ((J.1 c : ℝ) ^ 2)) =
      ∑ p : DualPlaquettes R, ((closedCurrentCoordinates R J p : ℝ) ^ 2) := by
  classical
  let q := closedCurrentCoordinatesFinsupp R J
  have hEmbed := closedCurrentCoordinatesFinsupp_emb R J
  calc
    (∑ c ∈ J.1.support, ((J.1 c : ℝ) ^ 2)) =
        (Finsupp.embDomain (dualPlaquetteLatticeEmbedding R) q).sum
          (fun _ z => ((z : ℝ) ^ 2)) := by
            rw [← hEmbed]
            rfl
    _ = q.sum (fun _ z => ((z : ℝ) ^ 2)) := by
          rw [Finsupp.sum_embDomain]
    _ = ∑ p : DualPlaquettes R, ((q p : ℝ) ^ 2) := by
          exact Finsupp.sum_fintype q (fun _ z => ((z : ℝ) ^ 2))
            (by intro p; simp)
    _ = ∑ p : DualPlaquettes R,
        ((closedCurrentCoordinates R J p : ℝ) ^ 2) := by
          rfl

noncomputable def gaugeClassCurrentCoordinates (R : RectBox4)
    (c : IntegerDualGaugeQuotient R) : DualPlaquettes R → ℤ :=
  closedCurrentCoordinates R
    (FroehlichSpencer.FS82.Surface.GaugeCurrentEquivalence.sourceGaugeClass_closedCurrentEquiv R c)

theorem gaugeClassCurrentCoordinates_injective (R : RectBox4) :
    Function.Injective (gaugeClassCurrentCoordinates R) := by
  intro c d h
  apply (FroehlichSpencer.FS82.Surface.GaugeCurrentEquivalence.sourceGaugeClass_closedCurrentEquiv R).injective
  exact closedCurrentCoordinates_injective R h

private theorem gaugeClassCurl_eq (R : RectBox4) (α : IntegerDualField R) :
    (FroehlichSpencer.FS82.Surface.GaugeCurrentEquivalence.sourceGaugeClass_closedCurrentEquiv
      R (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α)).1 =
        integerLatticeCurl R α := by
  change (FroehlichSpencer.FS82.Surface.IntegerGaugeTransport.integerGaugeQuotient_toSourceClosedCurrent
    R (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α)).1 = _
  rfl

theorem integerDualGaugeWeight_eq_gaussianCoordinates (R : RectBox4)
    (β : ℝ) (hβ : 0 < β) (c : IntegerDualGaugeQuotient R) :
    integerDualGaugeWeight R β hβ c =
      Real.exp (-(1 / (2 * β)) *
        ∑ p : DualPlaquettes R, ((gaugeClassCurrentCoordinates R c p : ℝ) ^ 2)) := by
  classical
  refine Quotient.inductionOn c ?_
  intro α
  rw [integerDualGaugeWeight]
  change integerDualFieldWeight R β hβ α = _
  rw [integerDualFieldWeight]
  rw [← gaugeClassCurl_eq R α]
  rw [closedCurrent_sqnorm_eq_coordinates R _]
  rfl

theorem integerDualGaugeWeight_summable (R : RectBox4)
    (β : ℝ) (hβ : 0 < β) : Summable (integerDualGaugeWeight R β hβ) := by
  let a : ℝ := 1 / (2 * β)
  have ha : 0 < a := by dsimp [a]; positivity
  have hmajor :=
    FroehlichSpencer.FS82.QuotientGaussianBridge.summable_integerQuadraticExp_pullback_of_injective
      (gaugeClassCurrentCoordinates R) (gaugeClassCurrentCoordinates_injective R)
      a ha
  refine hmajor.congr ?_
  intro c
  rw [integerDualGaugeWeight_eq_gaussianCoordinates]

noncomputable instance integerDualGaugeWeightSummabilityGate :
    IntegerDualGaugeWeightSummabilityGate where
  summable := integerDualGaugeWeight_summable

theorem existsUnique_integerDualPartitionFunction (R : RectBox4) (β : ℝ)
    (hβ : 0 < β) :
    ∃! Z : ℝ, HasSum (integerDualGaugeWeight R β hβ) Z ∧ 0 < Z := by
  exact FroehlichSpencer.FS82.SourceModels.IntegerDualModel.existsUnique_integerDualPartitionFunction_of_summable
    R β hβ


end FroehlichSpencer.FS82.SourceInterface
end
