module

public import FroehlichSpencer.FS82.SurfaceInfiniteProof.CurvatureIdentities
public import Mathlib.Tactic
@[expose] public section

open MeasureTheory
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.SourceCovarianceBridge
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.SourceTreeChart
open FroehlichSpencer.FS82.Surface.IntegerGaugeTransport
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Poisson

namespace FroehlichSpencer.FS82.SurfaceInfinite

abbrev ChartAssignments (B : Cubical.Box 4) := (sourceRootedTree B).Chord → ℤ

noncomputable def sourceToCubeChart (N : ℕ) (hN : 0 < N) :
    IntegerDualGaugeQuotient (cubeRegion N hN) ≃ ChartAssignments (cube N) := by
  let R := cubeRegion N hN
  have hside : R.side = cube N := rfl
  let htype : ChartAssignments R.side = ChartAssignments (cube N) := congrArg ChartAssignments hside
  exact ((sourceQuotientToIntegerDualModel R).trans (literalIntegerDualGaugeQuotientEquivChord R)).trans
    (Equiv.cast htype)

theorem measure_toPMF_map_eq {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [Countable β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → β) (hf : Measurable f) :
    (μ.map f).toPMF = PMF.map f μ.toPMF := by
  apply PMF.toMeasure_injective
  calc
    ((μ.map f).toPMF).toMeasure = μ.map f := by
      exact Measure.toPMF_toMeasure (μ.map f)
    _ = μ.toPMF.toMeasure.map f := by rw [Measure.toPMF_toMeasure]
    _ = (PMF.map f μ.toPMF).toMeasure := PMF.toMeasure_map f μ.toPMF hf

theorem cubeCurvatureLaw_eq_pmfMap (R : RectBox4) (β : ℝ) (hβ : 0 < β)
    (P : Finset GlobalPlaquette) (hP : ∀ p ∈ P, inCube R p) :
    cubeCurvatureLaw R β hβ P hP =
      PMF.map (cubeCurvatureMap R P hP) (sourceQuotientPMF R β hβ) := by
  let : IsProbabilityMeasure (discreteDualMeasure R β hβ) :=
    discreteDualMeasure_isProbabilityMeasure R β hβ
  change ((discreteDualMeasure R β hβ).map (cubeCurvatureMap R P hP)).toPMF = _
  exact measure_toPMF_map_eq (discreteDualMeasure R β hβ)
    (cubeCurvatureMap R P hP) (by fun_prop)

theorem cubeCurvatureMap_eq_internal (N : ℕ) (hN : 0 < N)
    (P : Finset GlobalPlaquette)
    (hP : ∀ p ∈ P, inCube (cubeRegion N hN) p) :
    cubeCurvatureMap (cubeRegion N hN) P hP =
      Infinite.cubeCurvatureMap N P
        (fun p hp => (source_inCube_iff N hN p).mp (hP p hp)) ∘
        ⇑(sourceToCubeChart N hN) := by
  classical
  let R := cubeRegion N hN
  let hPI : ∀ p ∈ P, Infinite.PlaquetteInCube N p :=
    fun p hp => (source_inCube_iff N hN p).mp (hP p hp)
  funext c p
  refine Quotient.inductionOn c ?_
  intro α
  let d : DualPlaquettes R := Classical.choose (hP p.1 p.2)
  have hd : dualCellEmbeddingC1 R d.1 = p.1 := Classical.choose_spec (hP p.1 p.2)
  let q : SourceDualTwoCells (cube N) :=
    cubePlaquettePreimage N p.1 (hPI p.1 p.2)
  have hq : cubePlaquetteEmbedding N q = p.1.1 :=
    cubePlaquetteEmbedding_preimage N p.1 (hPI p.1 p.2)
  have hsame : (plaquettesEquivSource R d) = q := by
    apply Subtype.ext
    apply (Cubical.dualCellEmbedding (B := cube N) (cubeOrigin N)).injective
    calc
      Cubical.dualCellEmbedding (B := cube N) (cubeOrigin N)
          (plaquettesEquivSource R d).1 = p.1 := by
        change Cubical.dualCellEmbedding (B := R.side) R.origin
          (plaquettesEquivSource R d).1 = p.1
        rw [← c1Cell_bridge R]
        exact hd
      _ = cubePlaquetteEmbedding N q := hq.symm
  let n := sourceToCubeChart N hN
      (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α)
  have hcoord := chartCurrent_cast R α d
  have hn : n = quotientClassToChord R
      ((sourceQuotientToIntegerDualModel R) (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α)) := rfl
  have hcoord' := hcoord
  have hsignp : sourceIntegerCellSign (dualCellEmbeddingC1 R d.1) =
      sourceIntegerCellSign p.1.1 := congrArg sourceIntegerCellSign hd
  rw [hsignp, hsame, ← hn] at hcoord'
  have hsource :
      (cubeCurvatureMap R P hP (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α) p : ℝ) =
        (integerChordCurvature n q : ℝ) := by
    simp only [cubeCurvatureMap, Int.cast_mul]
    exact_mod_cast hcoord'
  have htarget :
      Infinite.cubeCurvatureMap N P hPI n p =
        integerChordCurvature n q := by
    change integerChordCurvature n q = integerChordCurvature n q
    rfl
  have htargetCast : (integerChordCurvature n q : ℝ) =
      (Infinite.cubeCurvatureMap N P hPI n p : ℝ) := by
    exact_mod_cast htarget.symm
  exact_mod_cast hsource.trans htargetCast


theorem sourceQuotientPMF_map_eq_cubeChart (N : ℕ) (hN : 0 < N)
    (β : ℝ) (hβ : 0 < β) :
    PMF.map (⇑(sourceToCubeChart N hN))
      (sourceQuotientPMF (cubeRegion N hN) β hβ) =
      Infinite.cubeDualChordPMF N β hβ := by
  change PMF.map ((sourceQuotientToIntegerDualModel (cubeRegion N hN)).trans
      (literalIntegerDualGaugeQuotientEquivChord (cubeRegion N hN)))
      (sourceQuotientPMF (cubeRegion N hN) β hβ) =
    Infinite.cubeDualChordPMF N β hβ
  rw [Infinite.cubeDualChordPMF]
  exact sourceQuotientPMF_map_eq_chord (cubeRegion N hN) β hβ

theorem cubeCurvatureLaw_eq_internal (N : ℕ) (hN : 0 < N)
    (β : ℝ) (hβ : 0 < β) (P : Finset GlobalPlaquette)
    (hP : ∀ p ∈ P, inCube (cubeRegion N hN) p) :
    cubeCurvatureLaw (cubeRegion N hN) β hβ P hP =
      Infinite.cubeLocalCurvaturePMF N β hβ P
        (fun p hp => (source_inCube_iff N hN p).mp (hP p hp)) := by
  let P' : Finset Infinite.GlobalIntegerPlaquette := P
  let hPI : ∀ p ∈ P', Infinite.PlaquetteInCube N p :=
    fun p hp => (source_inCube_iff N hN p).mp (hP p hp)
  change cubeCurvatureLaw (cubeRegion N hN) β hβ P hP =
    Infinite.cubeLocalCurvaturePMF N β hβ P' hPI
  let E := ⇑(sourceToCubeChart N hN)
  let F := Infinite.cubeCurvatureMap N P' hPI
  have hcomp : PMF.map F (PMF.map E (sourceQuotientPMF (cubeRegion N hN) β hβ)) =
      PMF.map (F ∘ E) (sourceQuotientPMF (cubeRegion N hN) β hβ) :=
    PMF.map_comp E (sourceQuotientPMF (cubeRegion N hN) β hβ) F
  have hcurv : PMF.map (cubeCurvatureMap (cubeRegion N hN) P hP)
      (sourceQuotientPMF (cubeRegion N hN) β hβ) =
      PMF.map F (PMF.map E (sourceQuotientPMF (cubeRegion N hN) β hβ)) := by
    rw [cubeCurvatureMap_eq_internal N hN P hP]
    change PMF.map (F ∘ E) (sourceQuotientPMF (cubeRegion N hN) β hβ) = _
    exact hcomp.symm
  rw [cubeCurvatureLaw_eq_pmfMap, hcurv]
  rw [sourceQuotientPMF_map_eq_cubeChart N hN β hβ]
  rfl

end FroehlichSpencer.FS82.SurfaceInfinite
