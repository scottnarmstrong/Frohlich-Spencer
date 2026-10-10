module

public import FroehlichSpencer.FS82.SurfaceInfinite.All
public import FroehlichSpencer.FS82.CovarianceTransport.MomentBridge
public import FroehlichSpencer.FS82.Surface.IntegerDualPartitionFunction_spec
public import FroehlichSpencer.FS82.Infinite.LimitStateRoot
public import Mathlib.Tactic
@[expose] public section

open MeasureTheory
open scoped BigOperators
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.SourceCovarianceBridge
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Moment.SourceConstructor

namespace FroehlichSpencer.FS82.SurfaceInfinite

local instance sourceRelationEquivalenceGateCurvature :
    FroehlichSpencer.FS82.SourceModels.IntegerDualModel.SourceRelationEquivalenceGate :=
  ⟨FroehlichSpencer.FS82.SourceInterfaceResults.sourceIntegerGaugeRelation_isEquivalence_gate⟩

noncomputable def sourceQuotientPMF (R : RectBox4) (β : ℝ) (hβ : 0 < β) :
    PMF (IntegerDualGaugeQuotient R) := by
  letI : IsProbabilityMeasure (discreteDualMeasure R β hβ) :=
    discreteDualMeasure_isProbabilityMeasure R β hβ
  exact (discreteDualMeasure R β hβ).toPMF

theorem sourceQuotientPMF_apply (R : RectBox4) (β : ℝ) (hβ : 0 < β)
    (c : IntegerDualGaugeQuotient R) :
    sourceQuotientPMF R β hβ c =
      ENNReal.ofReal (integerDualGaugeWeight R β hβ c /
        integerDualPartitionFunction R β hβ) := by
  classical
  unfold sourceQuotientPMF
  rw [Measure.toPMF_apply]
  rw [discreteDualMeasure, Measure.sum_apply _ (MeasurableSet.singleton c)]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply]
  rw [tsum_eq_single c]
  · simp
  · intro i hi
    simp [hi]


theorem sourceWeight_eq_chord (R : RectBox4) (β : ℝ) (hβ : 0 < β)
    (c : IntegerDualGaugeQuotient R) :
    integerDualGaugeWeight R β hβ c =
      dualBaseWeight (sourceChordMatrix (B := R.side) β)
        (literalIntegerDualGaugeQuotientEquivChord R c) := by
  classical
  refine Quotient.inductionOn c ?_
  intro α
  let T := sourceRootedTree R.side
  let n := quotientClassToChord R (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α)
  have hn : n = literalIntegerDualGaugeQuotientEquivChord R
      (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α) := rfl
  rw [integerDualGaugeWeight, Quotient.lift_mk, integerDualFieldWeight]
  change Real.exp (-(1 / (2 * β)) * literalCurlEnergy R α) = _
  rw [dualBaseWeight, dualPrimalWeight]
  rw [literalCurlEnergy_eq_reducedChord_quadratic]
  rw [← hn]
  let K := reducedChordMatrix T (sourceFinitePoissonModel (B := R.side) R.origin)
  have hA : sourceChordMatrix (B := R.side) β =
      ((2 * Real.pi * β)⁻¹) • K := by rfl
  have hquad :
      (∑ i : T.Chord, ∑ j : T.Chord,
          (n i : ℝ) * sourceChordMatrix (B := R.side) β i j * (n j : ℝ)) =
        (1 / (2 * Real.pi * β)) * dotProduct (fun q => (n q : ℝ))
          (K.mulVec (fun q => (n q : ℝ))) := by
    rw [hA]
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    field_simp [ne_of_gt hβ, Real.pi_ne_zero]
    ring
  simp only [Real.exp_eq_exp]
  rw [hquad]
  simp [Finset.sum_const_zero]
  field_simp [ne_of_gt hβ, Real.pi_ne_zero]
  rfl

theorem sourcePartition_eq_chordNormalizer (R : RectBox4) (β : ℝ) (hβ : 0 < β) :
    integerDualPartitionFunction R β hβ =
      dualBaseNormalizer (sourceChordMatrix (B := R.side) β) := by
  classical
  let E := literalIntegerDualGaugeQuotientEquivChord R
  let Z := integerDualPartitionFunction R β hβ
  have hZ := (integerDualPartitionFunction_spec R β hβ).1
  calc
    Z = ∑' c : IntegerDualGaugeQuotient R, integerDualGaugeWeight R β hβ c :=
      hZ.tsum_eq.symm
    _ = ∑' n : (sourceRootedTree R.side).Chord → ℤ,
        integerDualGaugeWeight R β hβ (E.symm n) := by
      exact (E.symm.tsum_eq (fun c => integerDualGaugeWeight R β hβ c)).symm
    _ = ∑' n : (sourceRootedTree R.side).Chord → ℤ,
        dualBaseWeight (sourceChordMatrix (B := R.side) β) n := by
      apply tsum_congr
      intro n
      rw [sourceWeight_eq_chord R β hβ (E.symm n)]
      simp [E]
    _ = dualBaseNormalizer (sourceChordMatrix (B := R.side) β) := rfl


noncomputable def sourceQuotientToIntegerDualModel (R : RectBox4) :
    Surface.IntegerDualGaugeQuotient R ≃
      FroehlichSpencer.FS82.SourceModels.IntegerDualModel.IntegerDualGaugeQuotient R where
  toFun := Quotient.map id (by
    intro α α' h
    exact h)
  invFun := Quotient.map id (by
    intro α α' h
    exact h)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro α
    rfl
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro α
    rfl


theorem source_inCube_iff (N : ℕ) (hN : 0 < N) (p : GlobalPlaquette) :
    inCube (cubeRegion N hN) p ↔ PlaquetteInCube N p := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨⟨d.1, d.2⟩, ?_⟩
    rw [FroehlichSpencer.FS82.Surface.c1Cell_bridge] at hd
    change Cubical.dualCellEmbedding (cubeOrigin N) d.1 = p.1
    exact hd
  · rintro ⟨q, hq⟩
    refine ⟨⟨q.1, q.2⟩, ?_⟩
    rw [FroehlichSpencer.FS82.Surface.c1Cell_bridge]
    change Cubical.dualCellEmbedding (cubeOrigin N) q.1 = p.1
    exact hq

theorem pmf_map_equiv_apply {α : Type*} {γ : Type*}
    (E : α ≃ γ) (p : PMF α) (y : γ) :
    PMF.map E p y = p (E.symm y) := by
  rw [PMF.map_apply]
  rw [tsum_eq_single (E.symm y)]
  · simp
  · intro x hx
    have hne : y ≠ E x := by
      intro he
      apply hx
      exact E.injective (by simpa using he.symm)
    simp [hne]

theorem sourceQuotientPMF_map_eq_chord (R : RectBox4) (β : ℝ) (hβ : 0 < β) :
    PMF.map ((sourceQuotientToIntegerDualModel R).trans
        (literalIntegerDualGaugeQuotientEquivChord R))
      (sourceQuotientPMF R β hβ) =
      dualChordPMF (sourceChordMatrix (B := R.side) β)
        (scaledChordMatrix_posDef _ _ hβ) := by
  classical
  let A := sourceChordMatrix (B := R.side) β
  have hA : A.PosDef := scaledChordMatrix_posDef _ _ hβ
  let E := (sourceQuotientToIntegerDualModel R).trans
    (literalIntegerDualGaugeQuotientEquivChord R)
  apply PMF.ext
  intro n
  rw [pmf_map_equiv_apply E]
  rw [sourceQuotientPMF_apply]
  rw [sourceWeight_eq_chord R β hβ (E.symm n)]
  rw [sourcePartition_eq_chordNormalizer R β hβ]
  have hE : literalIntegerDualGaugeQuotientEquivChord R (E.symm n) = n := by
    change E (E.symm n) = n
    exact E.apply_symm_apply n
  rw [hE]
  change ENNReal.ofReal (dualBaseWeight A n / dualBaseNormalizer A) =
    ENNReal.ofReal (dualBaseWeight A n) / ENNReal.ofReal (dualBaseNormalizer A)
  rw [ENNReal.ofReal_div_of_pos (dualBaseNormalizer_pos A hA)]


end FroehlichSpencer.FS82.SurfaceInfinite
