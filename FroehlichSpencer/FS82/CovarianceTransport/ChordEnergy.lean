module
public import FroehlichSpencer.FS82.CovarianceTransport.QuotientChord
public import FroehlichSpencer.FS82.SourceInterface.GaussianExistence
public import FroehlichSpencer.FS82.Gaussian.LatticePoincare

/-!
# Curl energy in rooted-tree chord coordinates

The reduced chord matrix is the compression of the source Hodge operator to
zero-on-tree fields. This module identifies its quadratic form with the full
literal curl energy and records the co-closed pairing identity.
-/

@[expose] public section

open scoped BigOperators
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.SourceModels.IntegerDualModel
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Surface.IntegerGaugeTransport
open FroehlichSpencer.FS82.Surface.GaugeCurrentEquivalence
open FroehlichSpencer.FS82.SourceInterface

namespace FroehlichSpencer.FS82.SourceCovarianceBridge

local instance sourceRelationEquivalenceGateEnergy : SourceRelationEquivalenceGate :=
  ⟨FroehlichSpencer.FS82.SourceInterfaceResults.sourceIntegerGaugeRelation_isEquivalence_gate⟩
local instance pairingInvariantGateEnergy : PairingInvariantGate :=
  ⟨FroehlichSpencer.FS82.SourceInterfaceTheorems.integerDualPairing_respectsGauge_gate⟩


abbrev literalIntegerDualGaugeQuotient (R : RectBox4) := IntegerDualGaugeQuotient R

variable (R : RectBox4)

/-- The real link field obtained by extending integer chord data by zero on
the rooted-tree links. -/
noncomputable def sourceChordField
    (n : (sourceRootedTree R.side).Chord → ℤ) :
    EuclideanSpace ℝ (SourcePoissonEdge R.side) :=
  WithLp.toLp 2 (fun e => (((sourceRootedTree R.side).extendChord n e : ℤ) : ℝ))

/-- The literal surface curl energy of an integer edge field. -/
noncomputable def literalCurlEnergy (α : IntegerDualField R) : ℝ :=
  ∑ c ∈ (integerLatticeCurl R α).support,
    ((integerLatticeCurl R α c : ℤ) : ℝ) ^ 2

theorem chordEmbedding_mulVec_eq_sourceChordField
  (n : (sourceRootedTree R.side).Chord → ℤ) :
    (chordEmbeddingMatrix (sourceRootedTree R.side)).mulVec (fun c => (n c : ℝ)) =
      fun e => sourceChordField R n e := by
  classical
  funext e
  by_cases ht : e ∈ Set.range (sourceRootedTree R.side).treeEdge
  · obtain ⟨w, rfl⟩ := ht
    rw [chordEmbeddingMatrix_mulVec_at_tree]
    have htree : (sourceRootedTree R.side).treeEdge w ∈
        Set.range (sourceRootedTree R.side).treeEdge := ⟨w, rfl⟩
    change 0 = (((sourceRootedTree R.side).extendChord n
      ((sourceRootedTree R.side).treeEdge w) : ℤ) : ℝ)
    rw [RootedTreeGauge.extendChord, dite_eq_left htree]
    simp
  · let c : (sourceRootedTree R.side).Chord := ⟨e, ht⟩
    have hc := chordEmbeddingMatrix_mulVec_at_chord (sourceRootedTree R.side)
      (fun c => (n c : ℝ)) c
    change (chordEmbeddingMatrix (sourceRootedTree R.side)).mulVec
        (fun c => (n c : ℝ)) e =
      (((sourceRootedTree R.side).extendChord n e : ℤ) : ℝ)
    rw [RootedTreeGauge.extendChord, dite_eq_right ht]
    simpa [c] using hc

theorem reducedChord_quadratic_eq_d1_norm_sq
    (n : (sourceRootedTree R.side).Chord → ℤ) :
    dotProduct (fun c => (n c : ℝ))
        ((reducedChordMatrix (sourceRootedTree R.side)
          (sourceFinitePoissonModel (B := R.side) R.origin)).mulVec
            (fun c => (n c : ℝ))) =
      ‖(latticeExactOneComplex (B := R.side) R.origin).d₁
          (sourceChordField R n)‖ ^ 2 := by
  let T := sourceRootedTree R.side
  let M := sourceFinitePoissonModel (B := R.side) R.origin
  let τ := sourceChordField R n
  have hEmb := chordEmbedding_mulVec_eq_sourceChordField R n
  have hK : M.K.mulVec ((chordEmbeddingMatrix T).mulVec (fun c => (n c : ℝ))) =
      (latticeStencilOperator R.origin τ).ofLp := by
    change (sourcePoissonMatrix (B := R.side) R.origin).mulVec _ = _
    rw [hEmb]
    exact sourcePoissonMatrix_mulVec R.origin (fun e => τ e)
  have hK' : M.K.mulVec (fun e => τ e) =
      (latticeStencilOperator R.origin τ).ofLp := by
    rw [← hEmb]
    exact hK
  calc
    dotProduct (fun c => (n c : ℝ))
        ((reducedChordMatrix T M).mulVec (fun c => (n c : ℝ))) =
      dotProduct ((chordEmbeddingMatrix T).mulVec (fun c => (n c : ℝ)))
        (M.K.mulVec ((chordEmbeddingMatrix T).mulVec (fun c => (n c : ℝ)))) :=
          reducedChord_energy_eq T M (fun c => (n c : ℝ))
    _ = inner ℝ τ (latticeStencilOperator R.origin τ) := by
      rw [hEmb, hK']
      rw [PiLp.inner_apply]
      rw [dotProduct]
      simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ‖(latticeExactOneComplex (B := R.side) R.origin).d₁ τ‖ ^ 2 :=
      latticeStencil_inner_eq_d1_norm_sq R.origin τ

private theorem literalCurlEnergy_eq_sourceD1_norm_sq (α : IntegerDualField R) :
    literalCurlEnergy R α =
      ‖sourceDualD₁ (sourceCurlInput R α)‖ ^ 2 := by
  classical
  let J := integerLatticeCurl_mem_sourceClosedIntegerCurrent R α
  have hcoeff (p : DualPlaquettes R) :
      (closedCurrentCoordinates R J p : ℝ) ^ 2 =
        (sourceDualD₁ (sourceCurlInput R α)
          ((plaquettesEquivSource R) p) : ℝ) ^ 2 := by
    let c := dualCellEmbeddingC1 R p.1
    let f := (plaquettesEquivSource R) p
    have hcoords : closedCurrentCoordinates R J p = J.1 c := by
      change closedCurrentCoordinatesFinsupp R J p = J.1 c
      simp [closedCurrentCoordinatesFinsupp, dualPlaquetteLatticeEmbedding, c]
    have hcurl := congrArg (fun q : Cubical.RealLatticeChain 4 => q c)
      (literalCurl_cast_eq_sourceCurl R α)
    have hcell : c =
        Cubical.dualCellEmbedding (B := R.side) R.origin f.1 := by
      dsimp [c, f, plaquettesEquivSource, IntegerGaugeTransport.plaquettesEquivSource]
      rw [← c1Cell_bridge R]
      rfl
    have hsign :
        (((integerLatticeCurl R α c : ℤ) : ℝ)) =
          latticeCellOrientationSign c *
            (sourceDualD₁ (sourceCurlInput R α) f) := by
      change ((integerLatticeCurl R α c : ℤ) : ℝ) = _ at hcurl
      rw [latticeOrientationSignTwist_apply, hcell,
        GaugeCurrentEquivalence.sourcePhysicalDualZeroExtension_apply_embedding] at hcurl
      have hD : (sourceDualTwoToChain
          (sourceDualD₁ (sourceCurlInput R α))) f.1 =
          sourceDualD₁ (sourceCurlInput R α) f := by
        change embedDualSubtype sourceDualTwoEmbedding
          (Gaussian.euclideanToFinsupp (sourceDualD₁ (sourceCurlInput R α)))
          (sourceDualTwoEmbedding f) = _
        rw [embedDualSubtype_apply_at_image]
        simp [Gaussian.euclideanToFinsupp]
      rw [hD] at hcurl
      rw [← hcell] at hcurl
      exact hcurl
    rw [hcoords, show J.1 c = integerLatticeCurl R α c by rfl]
    calc
      (↑(integerLatticeCurl R α c)) ^ 2 =
          (latticeCellOrientationSign c *
            (sourceDualD₁ (sourceCurlInput R α) f)) ^ 2 := by rw [hsign]
      _ = (sourceDualD₁ (sourceCurlInput R α) f) ^ 2 := by
        rw [mul_pow, latticeCellOrientationSign_sq]
        ring
  calc
    literalCurlEnergy R α =
        ∑ p : DualPlaquettes R, ((closedCurrentCoordinates R J p : ℝ) ^ 2) := by
          dsimp [literalCurlEnergy, J]
          exact closedCurrent_sqnorm_eq_coordinates R J
    _ = ∑ p : DualPlaquettes R,
        (sourceDualD₁ (sourceCurlInput R α)
          ((plaquettesEquivSource R) p) : ℝ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hcoeff p
    _ = ∑ f : SourceDualTwoCells R.side,
        (sourceDualD₁ (sourceCurlInput R α) f : ℝ) ^ 2 := by
          exact (Equiv.sum_comp (plaquettesEquivSource R).symm _).symm
    _ = ‖sourceDualD₁ (sourceCurlInput R α)‖ ^ 2 := by
          rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
          simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
          apply Finset.sum_congr rfl
          intro f hf
          ring

theorem literalCurlEnergy_eq_reducedChord_quadratic
    (α : IntegerDualField R) :
    literalCurlEnergy R α =
      dotProduct
        (fun c => ((quotientClassToChord R
          (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α) c : ℤ) : ℝ))
        ((reducedChordMatrix (sourceRootedTree R.side)
          (sourceFinitePoissonModel (B := R.side) R.origin)).mulVec
          (fun c => ((quotientClassToChord R
            (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α) c : ℤ) : ℝ))) := by
  let n := quotientClassToChord R
    (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α)
  have hext : (sourceRootedTree R.side).extendChord n =
      sourceRootNormalize R α := by
    have h := (sourceRootedTree R.side).extend_restrictChord
      (rootNormalize_treeGauge R α)
    simpa [n, quotientClassToChord, sourceRootNormalize] using h
  have hfield : sourceChordField R n =
      literalFieldRealVector R (rootNormalize R α) := by
    ext e
    change (((sourceRootedTree R.side).extendChord n e : ℤ) : ℝ) = _
    rw [hext]
    change ((rootNormalizeSource R α e : ℤ) : ℝ) = _
    simp [literalFieldRealVector, sourceFieldOfLiteral, castIntegerFinsupp,
      Gaussian.finsuppToEuclidean, rootNormalize, IntegerGaugeTransport.linksEquivSource]
    rfl
  have hd1 : sourceDualD₁ (sourceCurlInput R (rootNormalize R α)) =
      (latticeExactOneComplex (B := R.side) R.origin).d₁
        (sourceChordField R n) := by
    change sourceDualD₁ (sourceDualTLinear
      (literalFieldRealVector R (rootNormalize R α))) = _
    rw [← hfield]
    rfl
  calc
    literalCurlEnergy R α = literalCurlEnergy R (rootNormalize R α) := by
      simp [literalCurlEnergy, rootNormalize_integerCurl_eq]
    _ = ‖sourceDualD₁ (sourceCurlInput R (rootNormalize R α))‖ ^ 2 :=
      literalCurlEnergy_eq_sourceD1_norm_sq R (rootNormalize R α)
    _ = ‖(latticeExactOneComplex (B := R.side) R.origin).d₁
          (sourceChordField R n)‖ ^ 2 := by rw [hd1]
    _ = dotProduct (fun c => (n c : ℝ))
          ((reducedChordMatrix (sourceRootedTree R.side)
            (sourceFinitePoissonModel (B := R.side) R.origin)).mulVec
              (fun c => (n c : ℝ))) :=
      (reducedChord_quadratic_eq_d1_norm_sq R n).symm

private theorem weighted_sum_treeGauge_chords
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (T : RootedTreeGauge V E) (a : E → ℤ) (b : E → ℝ)
    (ha : RootedTreeGauge.InTreeGauge T a) :
    (∑ e : E, (a e : ℝ) * b e) =
      ∑ c : T.Chord, (a c.1 : ℝ) * b c.1 := by
  classical
  calc
    (∑ e : E, (a e : ℝ) * b e) =
        ∑ s : T.Chord ⊕ {x : V // x ≠ T.root},
          (a ((T.edgeSplitEquiv).symm s) : ℝ) * b ((T.edgeSplitEquiv).symm s) :=
      (Equiv.sum_comp (T.edgeSplitEquiv).symm
        (fun e => (a e : ℝ) * b e)).symm
    _ = (∑ c : T.Chord, (a c.1 : ℝ) * b c.1) +
        ∑ x : {x : V // x ≠ T.root},
          (a (T.treeEdge x) : ℝ) * b (T.treeEdge x) := by
      rw [Fintype.sum_sum_type]
      simp only [RootedTreeGauge.edgeSplitEquiv_symm_inl,
        RootedTreeGauge.edgeSplitEquiv_symm_inr]
    _ = ∑ c : T.Chord, (a c.1 : ℝ) * b c.1 := by
      have htree :
          (∑ x : {x : V // x ≠ T.root},
            (a (T.treeEdge x) : ℝ) * b (T.treeEdge x)) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        rw [ha x]
        simp
      rw [htree, add_zero]

private theorem sourceRootNormalize_eq_extendChord
    (α : IntegerDualField R)
    (n : (sourceRootedTree R.side).Chord → ℤ)
    (hn : n = quotientClassToChord R
      (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α)) :
    (sourceRootedTree R.side).extendChord n = sourceRootNormalize R α := by
  subst n
  have h := (sourceRootedTree R.side).extend_restrictChord
    (rootNormalize_treeGauge R α)
  simpa [quotientClassToChord, sourceRootNormalize] using h

theorem integerDualPairing_eq_chord_pairing (μ : W R)
    (c : literalIntegerDualGaugeQuotient R) :
    integerDualPairing R μ c =
      ∑ q : (sourceRootedTree R.side).Chord,
        sourceChordTest (literalWEquivCoClosed R μ) q *
          ((quotientClassToChord R c q : ℤ) : ℝ) := by
  classical
  refine Quotient.inductionOn c ?_
  intro α
  let T := sourceRootedTree R.side
  let μsrc := literalWEquivCoClosed R μ
  let n := quotientClassToChord R
    (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α)
  have hrel : sourceIntegerGaugeRelation R α (rootNormalize R α) :=
    GaugeCurrentEquivalence.sourceCurl_eq_implies_gauge R α (rootNormalize R α)
      (rootNormalize_integerCurl_eq R α)
  have hpair := FroehlichSpencer.FS82.SourceInterfaceTheorems.integerDualPairing_respectsGauge_gate
    R μ α (rootNormalize R α) hrel
  have hnorm : T.extendChord n = sourceRootNormalize R α :=
    sourceRootNormalize_eq_extendChord R α n rfl
  change (∑ e : DualLinks R, (α e : ℝ) * (μ : RealDualField R) e) = _
  rw [hpair]
  have hsource :
      (∑ e : DualLinks R,
        (rootNormalize R α e : ℝ) * (μ : RealDualField R) e) =
      ∑ e : SourcePoissonEdge R.side,
        ((sourceRootNormalize R α e : ℤ) : ℝ) * sourceLinkValues μsrc e := by
    refine (Equiv.sum_comp (linksEquivSource R).symm _).symm.trans ?_
    apply Finset.sum_congr rfl
    intro e he
    rfl
  rw [hsource]
  rw [weighted_sum_treeGauge_chords T (sourceRootNormalize R α)
    (sourceLinkValues μsrc) (rootNormalize_treeGauge R α)]
  have hchord (q : T.Chord) :
      sourceRootNormalize R α q.1 = n q := by
    have h := congrFun hnorm q.1
    simpa [RootedTreeGauge.extendChord, q.2] using h.symm
  apply Finset.sum_congr rfl
  intro q hq
  rw [hchord]
  change (↑(n q) : ℝ) * sourceLinkValues μsrc q.1 =
    sourceLinkValues μsrc q.1 * ↑(n q)
  ring

end FroehlichSpencer.FS82.SourceCovarianceBridge
end
