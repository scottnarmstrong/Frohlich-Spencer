module
public import FroehlichSpencer.FS82.CovarianceTransport.ChordEnergy
public import FroehlichSpencer.FS82.CovarianceTransport.CovarianceBridge

/-!
# Transport of the literal discrete dual moment to source chord coordinates

The quotient law is
reindexed by its rooted-tree chord equivalence, including its normalizer.
-/

@[expose] public section

open scoped BigOperators
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.SourceModels.IntegerDualModel
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.SourceCovarianceBridge

namespace FroehlichSpencer.FS82.SourceCovarianceBridge

local instance sourceRelationEquivalenceGateMoment : SourceRelationEquivalenceGate :=
  ⟨FroehlichSpencer.FS82.SourceInterfaceResults.sourceIntegerGaugeRelation_isEquivalence_gate⟩
local instance integerWeightInvariantGateMoment : IntegerWeightInvariantGate :=
  ⟨FroehlichSpencer.FS82.SourceInterfaceTheorems.integerDualFieldWeight_respectsGauge_gate⟩
local instance pairingInvariantGateMoment : PairingInvariantGate :=
  ⟨FroehlichSpencer.FS82.SourceInterfaceTheorems.integerDualPairing_respectsGauge_gate⟩
local instance partitionUniqueGateMoment : IntegerPartitionUniqueGate :=
  ⟨FroehlichSpencer.FS82.SourceInterface.existsUnique_integerDualPartitionFunction⟩

variable (R : RectBox4)

noncomputable def literalSourceCoClosed (μ : W R) : SourceW R.side := by
  refine ⟨(μ : RealDualField R), ?_⟩
  have h := (literalWEquivCoClosed R μ).property
  change (latticeExactOneComplex (B := R.side) Cubical.originZero).d₀.adjoint
    (μ : RealDualField R) = 0
  change (latticeExactOneComplex (B := R.side) R.origin).d₀.adjoint
    (μ : RealDualField R) = 0 at h
  exact h

private theorem literalSourceCoClosed_eq (μ : W R) :
    literalSourceCoClosed R μ = literalWEquivCoClosed R μ := by
  apply Subtype.ext
  rfl

private theorem integerDualGaugeWeight_eq_reducedChord
    (β : ℝ) (hβ : 0 < β) (c : IntegerDualGaugeQuotient R) :
    integerDualGaugeWeight R β hβ c =
      Real.exp (-(1 / (2 * β)) *
        dotProduct
          (fun q => ((quotientClassToChord R c q : ℤ) : ℝ))
          ((reducedChordMatrix (sourceRootedTree R.side)
            (sourceFinitePoissonModel (B := R.side) R.origin)).mulVec
            (fun q => ((quotientClassToChord R c q : ℤ) : ℝ)))) := by
  classical
  refine Quotient.inductionOn c ?_
  intro α
  change integerDualFieldWeight R β hβ α = _
  rw [integerDualFieldWeight]
  change Real.exp (-(1 / (2 * β)) * literalCurlEnergy R α) = _
  rw [literalCurlEnergy_eq_reducedChord_quadratic R α]

private theorem sourcePrimalWeight_summable
    (β : ℝ) (hβ : 0 < β) (μ : W R) (t : ℝ) :
    Summable (fun n : (sourceRootedTree R.side).Chord → ℤ =>
      dualPrimalWeight (sourceChordMatrix (B := R.side) β)
        (sourceChordTest (literalSourceCoClosed R μ)) t n) := by
  let A := sourceChordMatrix (B := R.side) β
  let τ := sourceChordTest (literalSourceCoClosed R μ)
  have hA : A.PosDef := by
    dsimp [A, sourceChordMatrix]
    exact scaledChordMatrix_posDef _ _ hβ
  have hcomplex := summable_primal_quadratic_exp A hA
    (realTiltParameter τ t)
  have hterm (n : (sourceRootedTree R.side).Chord → ℤ) :
      primalQuadraticExp A (realTiltParameter τ t) n =
        (dualPrimalWeight A τ t n : ℂ) := by
    unfold primalQuadraticExp realTiltParameter dualPrimalWeight
    rw [Complex.ofReal_exp]
    apply congrArg Complex.exp
    push_cast
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have htilt :
        (2 * (Real.pi : ℂ)) *
            ∑ i, (t : ℂ) * (τ i : ℂ) / (2 * (Real.pi : ℂ)) * (n i : ℂ) =
          (t : ℂ) * ∑ i, (τ i : ℂ) * (n i : ℂ) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      field_simp [hpi]
    rw [htilt]
  have hcomplexReal : Summable (fun n : (sourceRootedTree R.side).Chord → ℤ =>
      (dualPrimalWeight A τ t n : ℂ)) := by
    exact hcomplex.congr fun n => hterm n
  have habs : Summable (fun n : (sourceRootedTree R.side).Chord → ℤ =>
      |dualPrimalWeight A τ t n|) := by
    have hnorm := hcomplexReal.norm
    refine hnorm.congr ?_
    intro n
    simp [Complex.norm_real, Real.norm_eq_abs]
  simpa [A, τ] using (Summable.of_abs habs)

private theorem sourcePrimalWeight_eq_literal
    (β : ℝ) (hβ : 0 < β) (μ : W R) (t : ℝ)
    (n : (sourceRootedTree R.side).Chord → ℤ) :
    dualPrimalWeight (sourceChordMatrix (B := R.side) β)
      (sourceChordTest (literalSourceCoClosed R μ)) t n =
      integerDualGaugeWeight R β hβ (rootChordToQuotient R n) *
        Real.exp (t * integerDualPairing R μ (rootChordToQuotient R n)) := by
  classical
  let T := sourceRootedTree R.side
  let τ := sourceChordTest (literalSourceCoClosed R μ)
  let α : IntegerDualField R := fun e =>
    T.extendChord n (IntegerGaugeTransport.linksEquivSource R e)
  have hchord : quotientClassToChord R
      (rootChordToQuotient R n) = n := quotientChord_right_inverse R n
  have hweight : integerDualGaugeWeight R β hβ (rootChordToQuotient R n) =
      Real.exp (-(1 / (2 * β)) *
        dotProduct (fun q => (n q : ℝ))
          ((reducedChordMatrix T
            (sourceFinitePoissonModel (B := R.side) R.origin)).mulVec
            (fun q => (n q : ℝ)))) := by
    rw [integerDualGaugeWeight_eq_reducedChord R β hβ, hchord]
  have hpair := integerDualPairing_eq_chord_pairing R μ
    (rootChordToQuotient R n)
  rw [hchord] at hpair
  rw [← literalSourceCoClosed_eq R μ] at hpair
  have hPoisson : sourcePoissonMatrix (B := R.side) R.origin =
      sourcePoissonMatrix (B := R.side) Cubical.originZero := by
    rfl
  have hquad :
      (∑ i : T.Chord, ∑ j : T.Chord,
          (n i : ℝ) * sourceChordMatrix (B := R.side) β i j * (n j : ℝ)) =
        (1 / (2 * Real.pi * β)) *
          dotProduct (fun q => (n q : ℝ))
            ((reducedChordMatrix T
              (sourceFinitePoissonModel (B := R.side) R.origin)).mulVec
              (fun q => (n q : ℝ))) := by
    have hK :
        reducedChordMatrix T
          (sourceFinitePoissonModel (B := R.side) R.origin) =
        reducedChordMatrix T
          (sourceFinitePoissonModel (B := R.side) Cubical.originZero) := by
      ext i j
      simp [reducedChordMatrix, sourceFinitePoissonModel, hPoisson]
    rw [show sourceChordMatrix (B := R.side) β =
        ((2 * Real.pi * β)⁻¹) • reducedChordMatrix T
          (sourceFinitePoissonModel (B := R.side) Cubical.originZero) by
          rfl]
    simp [dotProduct, Matrix.mulVec, hK, Finset.mul_sum]
    field_simp [ne_of_gt hβ, Real.pi_ne_zero]
    ring
  have hcoef :
      -Real.pi * ((1 / (2 * Real.pi * β)) *
          dotProduct (fun q => (n q : ℝ))
            ((reducedChordMatrix T
              (sourceFinitePoissonModel (B := R.side) R.origin)).mulVec
              (fun q => (n q : ℝ)))) =
        -(1 / (2 * β)) * dotProduct (fun q => (n q : ℝ))
          ((reducedChordMatrix T
            (sourceFinitePoissonModel (B := R.side) R.origin)).mulVec
            (fun q => (n q : ℝ))) := by
    calc
      _ = (-Real.pi * (1 / (2 * Real.pi * β))) *
          dotProduct (fun q => (n q : ℝ))
            ((reducedChordMatrix T
              (sourceFinitePoissonModel (B := R.side) R.origin)).mulVec
              (fun q => (n q : ℝ))) := by ring
      _ = _ := by
        have hscalar : -Real.pi * (1 / (2 * Real.pi * β)) =
            -(1 / (2 * β)) := by
          field_simp [ne_of_gt hβ, Real.pi_ne_zero]
        rw [hscalar]
  unfold dualPrimalWeight
  rw [hquad, hcoef, Real.exp_add, ← hweight, ← hpair]

private theorem sourceMoment_numerator_summable
    (β : ℝ) (hβ : 0 < β) (μ : W R) (t : ℝ) :
    Summable (fun c : IntegerDualGaugeQuotient R =>
      integerDualGaugeWeight R β hβ c *
        Real.exp (t * integerDualPairing R μ c)) := by
  let E := literalIntegerDualGaugeQuotientEquivChord R
  have hs := sourcePrimalWeight_summable R β hβ μ t
  have hcomp : Summable (fun c : IntegerDualGaugeQuotient R =>
      dualPrimalWeight (sourceChordMatrix (B := R.side) β)
        (sourceChordTest (literalSourceCoClosed R μ)) t (E c)) :=
    (Equiv.summable_iff (f := fun n =>
      dualPrimalWeight (sourceChordMatrix (B := R.side) β)
        (sourceChordTest (literalSourceCoClosed R μ)) t n) E).mpr hs
  refine hcomp.congr ?_
  intro c
  let n := quotientClassToChord R c
  have hE : E c = n := rfl
  have hc : rootChordToQuotient R n = c :=
    (E.left_inv c)
  rw [hE, ← hc]
  exact sourcePrimalWeight_eq_literal R β hβ μ t n

/-- The literal ENNReal expectation is the source real dual moment. -/
theorem literal_discreteDualMoment_eq_sourceDualMoment
    (β : ℝ) (hβ : 0 < β) (t : ℝ) (μ : W R) :
    discreteDualMoment R β hβ t μ =
      ENNReal.ofReal (sourceDualMoment β (literalSourceCoClosed R μ) t) := by
  classical
  let Z := integerDualPartitionFunction R β hβ
  let f (c : IntegerDualGaugeQuotient R) : ℝ :=
    integerDualGaugeWeight R β hβ c / Z *
      Real.exp (t * integerDualPairing R μ c)
  have hZpos : 0 < Z := by
    have h := Classical.choose_spec
      (FroehlichSpencer.FS82.SourceModels.IntegerDualModel.existsUnique_integerDualPartitionFunction R β hβ).exists
    simpa [Z, integerDualPartitionFunction] using h.2
  have hZhas : HasSum (integerDualGaugeWeight R β hβ) Z := by
    exact (Classical.choose_spec
      (FroehlichSpencer.FS82.SourceModels.IntegerDualModel.existsUnique_integerDualPartitionFunction R β hβ).exists).1
  have hfs : Summable f := by
    have hs := sourceMoment_numerator_summable R β hβ μ t
    have hs' := hs.mul_left Z⁻¹
    refine hs'.congr ?_
    intro c
    dsimp [f]
    ring
  have hfnn : ∀ c, 0 ≤ f c := by
    intro c
    dsimp [f]
    exact mul_nonneg
      (div_nonneg (integerDualGaugeWeight_pos R β hβ c).le hZpos.le)
      (Real.exp_nonneg _)
  have hIntegral : discreteDualMoment R β hβ t μ =
      ∑' c : IntegerDualGaugeQuotient R,
        ENNReal.ofReal (f c) := by
    rw [discreteDualMoment, discreteDualMeasure,
      MeasureTheory.lintegral_sum_measure]
    simp_rw [MeasureTheory.lintegral_smul_measure,
      MeasureTheory.lintegral_dirac]
    apply tsum_congr
    intro c
    dsimp [f]
    rw [← ENNReal.ofReal_mul
      (div_nonneg (integerDualGaugeWeight_pos R β hβ c).le hZpos.le)]
  rw [hIntegral, ← ENNReal.ofReal_tsum_of_nonneg hfnn hfs]
  have hsourceDenom :
      (∑' n : (sourceRootedTree R.side).Chord → ℤ,
        dualPrimalWeight (sourceChordMatrix (B := R.side) β)
          (sourceChordTest (literalSourceCoClosed R μ)) 0 n) = Z := by
    let E := literalIntegerDualGaugeQuotientEquivChord R
    calc
      _ = ∑' c : IntegerDualGaugeQuotient R,
          dualPrimalWeight (sourceChordMatrix (B := R.side) β)
            (sourceChordTest (literalSourceCoClosed R μ)) 0 (E c) :=
        (E.tsum_eq _).symm
      _ = ∑' c : IntegerDualGaugeQuotient R,
          integerDualGaugeWeight R β hβ c := by
        apply tsum_congr
        intro c
        let n := quotientClassToChord R c
        have hE : E c = n := rfl
        have hc : rootChordToQuotient R n = c := E.left_inv c
        rw [hE, ← hc, sourcePrimalWeight_eq_literal R β hβ μ 0 n]
        simp [Real.exp_zero]
      _ = Z := hZhas.tsum_eq
  have hsourceNum :
      (∑' n : (sourceRootedTree R.side).Chord → ℤ,
        dualPrimalWeight (sourceChordMatrix (B := R.side) β)
          (sourceChordTest (literalSourceCoClosed R μ)) t n) =
        ∑' c : IntegerDualGaugeQuotient R,
          integerDualGaugeWeight R β hβ c *
            Real.exp (t * integerDualPairing R μ c) := by
    let E := literalIntegerDualGaugeQuotientEquivChord R
    calc
      _ = ∑' c : IntegerDualGaugeQuotient R,
          dualPrimalWeight (sourceChordMatrix (B := R.side) β)
            (sourceChordTest (literalSourceCoClosed R μ)) t (E c) :=
        (E.tsum_eq _).symm
      _ = _ := by
        apply tsum_congr
        intro c
        let n := quotientClassToChord R c
        have hE : E c = n := rfl
        have hc : rootChordToQuotient R n = c := E.left_inv c
        rw [hE, ← hc, sourcePrimalWeight_eq_literal R β hβ μ t n]
  have hratio :
      (∑' c : IntegerDualGaugeQuotient R, f c) =
        sourceDualMoment β (literalSourceCoClosed R μ) t := by
    rw [sourceDualMoment, dualMoment, hsourceNum, hsourceDenom]
    have htsum :
        (∑' c : IntegerDualGaugeQuotient R, f c) =
          (∑' c : IntegerDualGaugeQuotient R,
            integerDualGaugeWeight R β hβ c *
              Real.exp (t * integerDualPairing R μ c)) / Z := by
      calc
        _ = ∑' c : IntegerDualGaugeQuotient R,
            Z⁻¹ * (integerDualGaugeWeight R β hβ c *
              Real.exp (t * integerDualPairing R μ c)) := by
          apply tsum_congr
          intro c
          dsimp [f]
          ring
        _ = Z⁻¹ * ∑' c : IntegerDualGaugeQuotient R,
            integerDualGaugeWeight R β hβ c *
              Real.exp (t * integerDualPairing R μ c) := tsum_mul_left
        _ = _ := by simp [div_eq_mul_inv, mul_comm]
    rw [htsum]
  change ENNReal.ofReal (∑' c : IntegerDualGaugeQuotient R, f c) = _
  rw [hratio]


end FroehlichSpencer.FS82.SourceCovarianceBridge
end
