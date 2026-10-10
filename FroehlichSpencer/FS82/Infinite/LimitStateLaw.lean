/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.CategoryTheory.Types.Basic
public import FroehlichSpencer.FS82.Root.SourceMoment
public import FroehlichSpencer.FS82.Infinite.CubeExhaustion
public import FroehlichSpencer.FS82.Gaussian.SourceTreeChartLaw
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.CategoryTheory.Types.Basic

/-!
# Finite cube dual laws and their local curvature coordinates

The finite source law is the normalized discrete Gaussian on tree-gauge
integer chord fields. Its local observables are the integer curls of the
canonical tree-zero representative.
-/

@[expose] public section

open Filter Topology
open scoped BigOperators

namespace FroehlichSpencer.FS82.Infinite

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.SourceTreeChart
open FroehlichSpencer.FS82.Gaussian.TreeGaugeQuotient
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Root

theorem pmf_toMeasure_eq_sum_dirac {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] (p : PMF α) :
    p.toMeasure = MeasureTheory.Measure.sum
      (fun x : α => p x • MeasureTheory.Measure.dirac x) := by
  ext s hs
  rw [PMF.toMeasure_apply_eq_tsum p s, MeasureTheory.Measure.sum_apply _ hs]
  simp only [MeasureTheory.Measure.smul_apply, smul_eq_mul]
  congr 1
  funext x
  by_cases hx : x ∈ s <;> simp [hx]

theorem pmf_integrable_of_summable_norm {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] {p : PMF α} {f : α → ℝ}
    (hs : Summable (fun x => (p x).toReal * ‖f x‖)) :
    MeasureTheory.Integrable f p.toMeasure := by
  rw [pmf_toMeasure_eq_sum_dirac]
  have hiff := MeasureTheory.integrable_sum_dirac_iff
    (f := f) (x := fun x : α => x) (c := p) (fun x => p.apply_ne_top x)
  exact hiff.mpr hs

theorem pmf_map_integrable_of_summable_norm {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
    [Countable α] {p : PMF α} (f : α → β) (g : β → ℝ)
    (hf : Measurable f) (hg : MeasureTheory.StronglyMeasurable g)
    (hs : Summable (fun x => (p x).toReal * ‖g (f x)‖)) :
    MeasureTheory.Integrable g (p.map f).toMeasure := by
  have hsource : MeasureTheory.Integrable (fun x => g (f x)) p.toMeasure :=
    pmf_integrable_of_summable_norm hs
  rw [← PMF.toMeasure_map f p hf]
  exact (MeasureTheory.integrable_map_measure hg.aestronglyMeasurable
    hf.aemeasurable).2 hsource

theorem pmf_map_integral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Countable α]
    (p : PMF α) (f : α → β) (g : β → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hs : Summable (fun x => (p x).toReal * ‖g (f x)‖)) :
    ∫ y, g y ∂(p.map f).toMeasure = ∫ x, g (f x) ∂p.toMeasure := by
  have hsource : MeasureTheory.Integrable (fun x => g (f x)) p.toMeasure :=
    pmf_integrable_of_summable_norm hs
  have htarget : MeasureTheory.Integrable g (p.map f).toMeasure := by
    rw [← PMF.toMeasure_map f p hf]
    exact (MeasureTheory.integrable_map_measure hg.aestronglyMeasurable
      hf.aemeasurable).2 hsource
  calc
    ∫ y, g y ∂(p.map f).toMeasure = ∫ y, g y ∂p.toMeasure.map f := by
      rw [PMF.toMeasure_map f p hf]
    _ = ∫ x, g (f x) ∂p.toMeasure :=
      MeasureTheory.integral_map_of_stronglyMeasurable hf hg.stronglyMeasurable

theorem pmf_exp_tail_bound {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] (p : PMF α) (X : α → ℝ) (s R C : ℝ)
    (hs : 0 < s) (hX : Measurable X)
    (hint : MeasureTheory.Integrable (fun x => Real.exp (s * X x)) p.toMeasure)
    (hmgf : ∫ x, Real.exp (s * X x) ∂p.toMeasure ≤ C) :
    p.toMeasure {x | R ≤ X x} ≤ ENNReal.ofReal (C * Real.exp (-s * R)) := by
  let Y : α → ENNReal := fun x => ENNReal.ofReal (Real.exp (s * X x))
  let ε : ENNReal := ENNReal.ofReal (Real.exp (s * R))
  have hY : Measurable Y := by
    change Measurable (fun x => ENNReal.ofReal (Real.exp (s * X x)))
    fun_prop
  have hε0 : ε ≠ 0 := by
    dsimp [ε]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hεtop : ε ≠ ⊤ := by simp [ε]
  have hevent : {x | ε ≤ Y x} = {x | R ≤ X x} := by
    ext x
    change (ENNReal.ofReal (Real.exp (s * R)) ≤
      ENNReal.ofReal (Real.exp (s * X x))) ↔ R ≤ X x
    rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _), Real.exp_le_exp]
    constructor
    · intro hx
      nlinarith
    · intro hx
      exact mul_le_mul_of_nonneg_left hx hs.le
  have hlin : (∫⁻ x, Y x ∂p.toMeasure) =
      ENNReal.ofReal (∫ x, Real.exp (s * X x) ∂p.toMeasure) := by
    dsimp [Y]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (MeasureTheory.ae_of_all _ fun x => (Real.exp_pos _).le)]
  have hlinBound : (∫⁻ x, Y x ∂p.toMeasure) ≤ ENNReal.ofReal C := by
    rw [hlin]
    exact ENNReal.ofReal_le_ofReal hmgf
  have hmarkov : p.toMeasure {x | ε ≤ Y x} ≤
      (∫⁻ x, Y x ∂p.toMeasure) / ε :=
    MeasureTheory.meas_ge_le_lintegral_div hY.aemeasurable hε0 hεtop
  rw [hevent] at hmarkov
  calc
    p.toMeasure {x | R ≤ X x} ≤ (∫⁻ x, Y x ∂p.toMeasure) / ε := hmarkov
    _ ≤ ENNReal.ofReal C / ε := ENNReal.div_le_div_right hlinBound ε
    _ = ENNReal.ofReal (C * Real.exp (-s * R)) := by
      dsimp [ε]
      rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
      congr 1
      rw [show -s * R = -(s * R) by ring, Real.exp_neg, div_eq_mul_inv]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The untitled finite dual weight on integer chord fields. -/
noncomputable def dualBaseWeight (A : Matrix ι ι ℝ) (n : ι → ℤ) : ℝ :=
  dualPrimalWeight A (fun _ => 0) 0 n

theorem dualBaseWeight_summable (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    Summable (dualBaseWeight A) := by
  have hs := Poisson.summable_primal_quadratic_exp A hA (fun _ => 0)
  have heq (n : ι → ℤ) :
      Poisson.primalQuadraticExp A (fun _ => 0) n =
        (dualBaseWeight A n : ℂ) := by
    have h := testedPrimalTerm_eq_ofReal A (fun _ => 0) 0 n
    simp [Poisson.primalQuadraticExp, dualBaseWeight, dualPrimalWeight] 
  have habs : Summable (fun n : ι → ℤ => |dualBaseWeight A n|) := by
    have hnorm := hs.norm
    refine hnorm.congr ?_
    intro n
    rw [heq]
    simp [Complex.norm_real]
  exact Summable.of_norm (f := dualBaseWeight A) habs

omit [DecidableEq ι] in
theorem dualBaseWeight_pos (A : Matrix ι ι ℝ) (n : ι → ℤ) :
    0 < dualBaseWeight A n := by
  exact Real.exp_pos _

noncomputable def dualBaseNormalizer (A : Matrix ι ι ℝ) : ℝ :=
  ∑' n : ι → ℤ, dualBaseWeight A n

theorem dualBaseNormalizer_pos (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    0 < dualBaseNormalizer A := by
  unfold dualBaseNormalizer
  exact (dualBaseWeight_summable A hA).tsum_pos
    (fun n => (dualBaseWeight_pos A n).le) (0 : ι → ℤ) (Real.exp_pos _)

/-- The genuine finite dual probability law in chord coordinates. -/
noncomputable def dualChordPMF (A : Matrix ι ι ℝ) (hA : A.PosDef) : PMF (ι → ℤ) := by
  let Z : ENNReal := ENNReal.ofReal (dualBaseNormalizer A)
  have hZ0 : Z ≠ 0 := (ENNReal.ofReal_pos.mpr (dualBaseNormalizer_pos A hA)).ne'
  have hZtop : Z ≠ ⊤ := by simp [Z]
  have hsum : ∑' n : ι → ℤ, ENNReal.ofReal (dualBaseWeight A n) = Z := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (dualBaseWeight_pos A n).le)
      (dualBaseWeight_summable A hA)]
    rfl
  refine ⟨fun n => ENNReal.ofReal (dualBaseWeight A n) / Z, ?_⟩
  rw [ENNReal.summable.hasSum_iff]
  calc
    ∑' n : ι → ℤ, ENNReal.ofReal (dualBaseWeight A n) / Z
      = (∑' n : ι → ℤ, ENNReal.ofReal (dualBaseWeight A n)) / Z := by
          simp_rw [div_eq_mul_inv]
          exact ENNReal.tsum_mul_right
    _ = Z / Z := by rw [hsum]
    _ = 1 := ENNReal.div_self hZ0 hZtop

/-- The centered cube's finite dual law, using the source matrix of (2.93). -/
noncomputable def cubeDualChordPMF (N : ℕ) (β : ℝ) (hβ : 0 < β) :
    PMF ((sourceRootedTree (cube N)).Chord → ℤ) :=
  dualChordPMF (sourceChordMatrix (B := cube N) β)
    (scaledChordMatrix_posDef _ _ hβ)

/-- Integer coefficient of one chord in the source curl coordinate. -/
noncomputable def integerRawCurlCoefficient {B : Box 4}
    (p : SourceDualTwoCells B)
    (e : (sourceRootedTree B).Chord) : ℤ :=
  if sourceCurlCoefficient p e.1 = 1 then 1
  else if sourceCurlCoefficient p e.1 = -1 then -1 else 0

theorem integerRawCurlCoefficient_cast {B : Box 4}
    (p : SourceDualTwoCells B)
    (e : (sourceRootedTree B).Chord) :
    (integerRawCurlCoefficient p e : ℝ) = sourceCurlCoefficient p e.1 := by
  classical
  unfold integerRawCurlCoefficient
  rcases sourceCurlCoefficient_trichotomy p e.1 with hzero | hone | hminus
  · have h1 : sourceCurlCoefficient p e.1 ≠ 1 := by rw [hzero]; norm_num
    have hm : sourceCurlCoefficient p e.1 ≠ -1 := by rw [hzero]; norm_num
    rw [ite_eq_right h1, ite_eq_right hm]
    norm_num
    exact hzero.symm
  · rw [ite_eq_left hone]
    norm_num
    exact hone.symm
  · have h1 : sourceCurlCoefficient p e.1 ≠ 1 := by rw [hminus]; norm_num
    rw [ite_eq_right h1, ite_eq_left hminus]
    norm_num
    exact hminus.symm

/-- The physical-link coefficient includes the C2 orientation sign. -/
noncomputable def integerCurlCoefficient {B : Box 4}
    (p : SourceDualTwoCells B)
    (e : (sourceRootedTree B).Chord) : ℤ :=
  integerRawCurlCoefficient p e * sourceIntegerOrientationSign e.1

theorem integerCurlCoefficient_cast {B : Box 4}
    (p : SourceDualTwoCells B)
    (e : (sourceRootedTree B).Chord) :
    (integerCurlCoefficient p e : ℝ) =
      (sourceDualT e.1 : ℝ) * sourceCurlCoefficient p e.1 := by
  rw [integerCurlCoefficient, Int.cast_mul, integerRawCurlCoefficient_cast,
    sourceIntegerOrientationSign_eq_sourceDualT]
  ring

/-- Physical source curl of a tree-gauge chord configuration. -/
noncomputable def sourceTreeChartPhysicalCurlLinear {B : Box 4}
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B)) :
    (T.Chord → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (SourceDualTwoCells B) :=
  (sourceTreeChartCurlLinear (B := B) T).comp
    (sourceChordOrientationLinear (B := B) T)

theorem sourceTreeChartPhysicalCurlLinear_apply {B : Box 4}
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (x : T.Chord → ℝ) (p : SourceDualTwoCells B) :
    sourceTreeChartPhysicalCurlLinear T x p =
      ∑ e : T.Chord,
        (sourceDualT e.1 : ℝ) * sourceCurlCoefficient p e.1 * x e := by
  change sourceTreeChartCurlLinear T (sourceChordOrientationLinear T x) p = _
  rw [sourceTreeChartCurlLinear_apply]
  apply Finset.sum_congr rfl
  intro e he
  calc
    sourceTreeChartCurlCoefficient T p e * sourceChordOrientationLinear T x e =
        sourceCurlCoefficient p e.1 *
          (dualCellOrientationSign e.1.1 * x e) := by
            rw [sourceTreeChartCurlCoefficient_eq_sourceCurlCoefficient]
            simp [sourceChordOrientationLinear]
    _ = (sourceDualT e.1 : ℝ) * sourceCurlCoefficient p e.1 * x e := by
          rw [sourceDualT_cast_eq_orientationSign]
          ring

/-- The integer curvature of a tree-gauge chord field at a finite source
plaquette. -/
noncomputable def integerChordCurvature {B : Box 4}
    (n : (sourceRootedTree B).Chord → ℤ)
    (p : SourceDualTwoCells B) : ℤ :=
  ∑ e : (sourceRootedTree B).Chord, integerCurlCoefficient p e * n e

theorem integerChordCurvature_cast_chartCurl {B : Box 4}
    (n : (sourceRootedTree B).Chord → ℤ)
    (p : SourceDualTwoCells B) :
    (integerChordCurvature n p : ℝ) =
      sourceTreeChartPhysicalCurlLinear (B := B) (sourceRootedTree B)
        (fun e => (n e : ℝ)) p := by
  rw [integerChordCurvature, sourceTreeChartPhysicalCurlLinear_apply]
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Int.cast_mul, integerCurlCoefficient_cast]

/-- Curvature on the finite physical link quotient, evaluated in source
plaquette coordinates. -/
noncomputable def physicalCurlClassCurvatureAt {B : Box 4}
    (p : SourceDualTwoCells B) :
    EuclideanSpace ℝ (SourceDualOneCells B) ⧸
      ((Gaussian.latticeExactOneComplex (B := B) Cubical.originZero)).d₁.ker →ₗ[ℝ] ℝ := by
  let C := (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero)
  let f : EuclideanSpace ℝ (SourceDualOneCells B) →ₗ[ℝ] ℝ :=
    { toFun := fun x => C.d₁ x p
      map_add' := by intro x y; simp
      map_smul' := by intro r x; simp }
  exact C.d₁.ker.liftQ f (by
    intro x hx
    simp only [LinearMap.mem_ker] at hx
    simp [f, hx])

@[simp] theorem physicalCurlClassCurvatureAt_mk {B : Box 4}
    (p : SourceDualTwoCells B) (x : EuclideanSpace ℝ (SourceDualOneCells B)) :
    physicalCurlClassCurvatureAt p (Submodule.Quotient.mk x) =
      ((Gaussian.latticeExactOneComplex (B := B) Cubical.originZero)).d₁ x p := by
  simp [physicalCurlClassCurvatureAt]


theorem sourceDualTLinear_extendChords_eq_orientation {B : Box 4}
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (x : T.Chord → ℝ) :
    sourceDualTLinear (B := B)
        (sourceFunctionToEuclidean (extendChordsLinear T x)) =
      sourceFunctionToEuclidean
        (extendChordsLinear T (sourceChordOrientationLinear T x)) := by
  classical
  ext f
  by_cases ht : f ∈ Set.range T.treeEdge
  · obtain ⟨v, rfl⟩ := ht
    simp [sourceDualTLinear_apply, sourceFunctionToEuclidean,
      extendChordsLinear, RootedTreeGauge.extendChord]
  · have hchordValue (z : T.Chord → ℝ) :
        extendChordsLinear T z f = z ⟨f, ht⟩ := by
      have h := congrFun (treeChordMap_extendChords T z) ⟨f, ht⟩
      rw [treeChordMap, LinearMap.comp_apply, treeNormalize_extendChords] at h
      change extendChordsLinear T z f = _ at h
      exact h
    simp [sourceDualTLinear_apply, sourceFunctionToEuclidean,
      sourceChordOrientationLinear, hchordValue]

/-- The integer chart curvature is the physical finite curl of its tree-zero
representative, and so descends to the exact gauge quotient. -/
theorem sourceTreeChartPhysicalCurl_eq_quotientCurvature {B : Box 4}
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (p : SourceDualTwoCells B) (x : T.Chord → ℝ) :
    sourceTreeChartPhysicalCurlLinear T x p =
      physicalCurlClassCurvatureAt p
        (Submodule.Quotient.mk
          (sourceFunctionToEuclidean (extendChordsLinear T x))) := by
  rw [physicalCurlClassCurvatureAt_mk]
  change sourceDualD₁
      (sourceFunctionToEuclidean (extendChordsLinear T
        (sourceChordOrientationLinear T x))) p =
    sourceDualD₁ (sourceDualTLinear
      (sourceFunctionToEuclidean (extendChordsLinear T x))) p
  exact congrArg (fun y => sourceDualD₁ y p)
    (sourceDualTLinear_extendChords_eq_orientation T x).symm

noncomputable def coClosedCurlAdjointTest {V E P : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype P] [DecidableEq P]
    (C : Gaussian.ExactOneComplex V E P) (p : P) : Gaussian.coClosed C := by
  have hcomp : C.d₀.adjoint.comp C.d₁.adjoint = 0 := by
    rw [← LinearMap.adjoint_comp, C.complex]
    simp
  refine ⟨C.d₁.adjoint (EuclideanSpace.single p 1), ?_⟩
  apply LinearMap.mem_ker.mpr
  change (C.d₀.adjoint.comp C.d₁.adjoint) (EuclideanSpace.single p 1) = 0
  rw [hcomp]
  simp

/-- The co-closed source test representing a single curvature coordinate. -/
noncomputable def sourcePlaquetteTest {B : Box 4}
    (p : SourceDualTwoCells B) :
    FroehlichSpencer.FS82.Moment.SourceConstructor.SourceW B :=
  coClosedCurlAdjointTest
    (FroehlichSpencer.FS82.Moment.SourceConstructor.sourceLatticeComplex (B := B)) p

theorem sourcePlaquetteTest_chordValue {B : Box 4}
    (p : SourceDualTwoCells B) (e : (sourceRootedTree B).Chord) :
    sourceChordTest (sourcePlaquetteTest p) e =
      (sourceDualT e.1 : ℝ) * sourceCurlCoefficient p e.1 := by
  classical
  let C := FroehlichSpencer.FS82.Moment.SourceConstructor.sourceLatticeComplex (B := B)
  have hcoord (x : EuclideanSpace ℝ (SourceDualOneCells B)) :
      x e.1 = inner ℝ x (EuclideanSpace.single e.1 1) := by
    simp [PiLp.inner_apply]
  change (sourcePlaquetteTest p : EuclideanSpace ℝ (SourceDualOneCells B)) e.1 = _
  rw [hcoord]
  change inner ℝ ((coClosedCurlAdjointTest C p : Gaussian.coClosed C) :
      EuclideanSpace ℝ (SourceDualOneCells B)) (EuclideanSpace.single e.1 1) = _
  change inner ℝ (C.d₁.adjoint (EuclideanSpace.single p 1))
      (EuclideanSpace.single e.1 1) = _
  rw [LinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply]
  simp [C, Gaussian.latticeExactOneComplex, LinearMap.comp_apply,
    sourceDualTLinear_apply, sourceDualD₁_eq_sourceCurl_sum,
    EuclideanSpace.single, mul_comm]
  rw [sourceDualT_cast_eq_orientationSign]
  ring

/-- The covariance of a single physical curl coordinate test is at most one,
uniformly over the cube. -/
theorem sourcePlaquetteTest_covariance_le_one {B : Box 4}
    (p : SourceDualTwoCells B) :
    Gaussian.quotientCovarianceQuadratic
      (FroehlichSpencer.FS82.Moment.SourceConstructor.sourceLatticeComplex (B := B))
      (sourcePlaquetteTest p) ≤ 1 := by
  classical
  let C := FroehlichSpencer.FS82.Moment.SourceConstructor.sourceLatticeComplex
    (B := B)
  change Gaussian.quotientCovarianceQuadratic C (sourcePlaquetteTest p) ≤ 1
  have hgreatest := quotientCovarianceQuadratic_isGreatest_variational C
    (sourcePlaquetteTest p)
  obtain ⟨φ, hφ⟩ := hgreatest.1
  rw [← hφ]
  have hbound (ψ : EuclideanSpace ℝ (SourceDualOneCells B)) :
      finiteVariationalObjective C (sourcePlaquetteTest p) ψ ≤ 1 := by
    change 2 * inner ℝ (sourcePlaquetteTest p : EuclideanSpace ℝ (SourceDualOneCells B)) ψ -
        ‖C.d₁ ψ‖ ^ 2 ≤ 1
    have hadj : inner ℝ (sourcePlaquetteTest p : EuclideanSpace ℝ (SourceDualOneCells B)) ψ =
        inner ℝ (EuclideanSpace.single p (1 : ℝ)) (C.d₁ ψ) := by
      change inner ℝ ((coClosedCurlAdjointTest C p : Gaussian.coClosed C) :
          EuclideanSpace ℝ (SourceDualOneCells B)) ψ = _
      change inner ℝ (C.d₁.adjoint (EuclideanSpace.single p 1)) ψ = _
      exact LinearMap.adjoint_inner_left C.d₁ ψ (EuclideanSpace.single p 1)
    rw [hadj]
    have hnorm' : ‖(EuclideanSpace.single p (1 : ℝ) :
        EuclideanSpace ℝ (SourceDualTwoCells B))‖ ^ 2 = 1 := by simp
    nlinarith [norm_sub_sq_real
      (EuclideanSpace.single p (1 : ℝ) : EuclideanSpace ℝ (SourceDualTwoCells B))
      (C.d₁ ψ)]
  exact hbound φ

theorem dualPrimalWeight_summable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (τ : ι → ℝ) (t : ℝ) :
    Summable (dualPrimalWeight A τ t) := by
  have hs := Poisson.summable_primal_quadratic_exp A hA
    (Poisson.realTiltParameter τ t)
  have heq (n : ι → ℤ) :
      Poisson.primalQuadraticExp A (Poisson.realTiltParameter τ t) n =
        (dualPrimalWeight A τ t n : ℂ) := by
    have h := testedPrimalTerm_eq_ofReal A τ t n
    have htilt : Poisson.testedPrimalTerm A τ t n =
        Poisson.primalQuadraticExp A (Poisson.realTiltParameter τ t) n := by
      unfold Poisson.testedPrimalTerm Poisson.primalQuadraticExp Poisson.realTiltParameter
      apply congrArg Complex.exp
      congr 1
      calc
        (t : ℂ) * ∑ i, (τ i : ℂ) * (n i : ℂ) =
            ∑ i, (t : ℂ) * ((τ i : ℂ) * (n i : ℂ)) := by rw [Finset.mul_sum]
        _ = ∑ i, (2 * Real.pi : ℂ) *
            (((t * τ i / (2 * Real.pi) : ℝ) : ℂ) * (n i : ℂ)) := by
          apply Fintype.sum_congr
          intro i
          push_cast
          have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
          field_simp [hpi]
        _ = (2 * Real.pi : ℂ) *
            ∑ i, (((t * τ i / (2 * Real.pi) : ℝ) : ℂ) * (n i : ℂ)) :=
              (Finset.mul_sum ..).symm
    rw [← htilt, h]
  have habs : Summable (fun n : ι → ℤ => |dualPrimalWeight A τ t n|) := by
    have hnorm := hs.norm
    refine hnorm.congr ?_
    intro n
    rw [heq]
    simp [Complex.norm_real]
  exact Summable.of_norm (f := dualPrimalWeight A τ t) habs

theorem dualChordPMF_apply_toReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (n : ι → ℤ) :
    (dualChordPMF A hA n).toReal = dualBaseWeight A n / dualBaseNormalizer A := by
  change (ENNReal.ofReal (dualBaseWeight A n) /
    ENNReal.ofReal (dualBaseNormalizer A)).toReal = _
  rw [ENNReal.toReal_div]
  rw [ENNReal.toReal_ofReal (le_of_lt (dualBaseWeight_pos A n))]
  rw [ENNReal.toReal_ofReal (le_of_lt (dualBaseNormalizer_pos A hA))]

theorem dualChordPMF_exp_linear_weighted_summable {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : A.PosDef) (τ : ι → ℝ) (t : ℝ) :
    Summable (fun n : ι → ℤ => (dualChordPMF A hA n).toReal *
      ‖Real.exp (t * ∑ i, τ i * (n i : ℝ))‖) := by
  have hterm (n : ι → ℤ) :
      (dualChordPMF A hA n).toReal *
          ‖Real.exp (t * ∑ i, τ i * (n i : ℝ))‖ =
        dualPrimalWeight A τ t n / dualBaseNormalizer A := by
    rw [dualChordPMF_apply_toReal, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hw : dualBaseWeight A n * Real.exp (t * ∑ i, τ i * (n i : ℝ)) =
        dualPrimalWeight A τ t n := by
      simp [dualBaseWeight, dualPrimalWeight, Real.exp_add]
    rw [← hw]
    ring
  have hsTilt := dualPrimalWeight_summable A hA τ t
  have hsTerm : Summable (fun n : ι → ℤ =>
      dualPrimalWeight A τ t n / dualBaseNormalizer A) := by
    simpa [div_eq_mul_inv] using hsTilt.mul_right (dualBaseNormalizer A)⁻¹
  refine hsTerm.congr ?_
  intro n
  exact (hterm n).symm

theorem dualChordPMF_exp_linear_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (τ : ι → ℝ) (t : ℝ) :
    ∫ n, Real.exp (t * ∑ i, τ i * (n i : ℝ)) ∂(dualChordPMF A hA).toMeasure =
      dualMoment A τ t := by
  let p := dualChordPMF A hA
  let f : (ι → ℤ) → ℝ := fun n => Real.exp (t * ∑ i, τ i * (n i : ℝ))
  have hweight (n : ι → ℤ) :
      dualBaseWeight A n * f n = dualPrimalWeight A τ t n := by
    simp [f, dualBaseWeight, dualPrimalWeight, Real.exp_add]
  have hdenom : dualBaseNormalizer A = ∑' n : ι → ℤ, dualPrimalWeight A τ 0 n := by
    unfold dualBaseNormalizer
    apply tsum_congr
    intro n
    simp [dualBaseWeight, dualPrimalWeight]
  have hterm (n : ι → ℤ) :
      (p n).toReal * ‖f n‖ =
        dualPrimalWeight A τ t n / dualBaseNormalizer A := by
    rw [dualChordPMF_apply_toReal, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← hweight]
    ring
  have hsTilt := dualPrimalWeight_summable A hA τ t
  have hsTerm : Summable (fun n : ι → ℤ =>
      dualPrimalWeight A τ t n / dualBaseNormalizer A) := by
    simpa [div_eq_mul_inv] using hsTilt.mul_right (dualBaseNormalizer A)⁻¹
  have hsInt : Summable (fun n : ι → ℤ => (p n).toReal * ‖f n‖) := by
    refine hsTerm.congr ?_
    intro n
    exact (hterm n).symm
  have hint : MeasureTheory.Integrable f p.toMeasure :=
    pmf_integrable_of_summable_norm hsInt
  have hsum := PMF.integral_eq_tsum p f hint
  have hmomentSum : (∑' n : ι → ℤ, dualPrimalWeight A τ t n) /
      dualBaseNormalizer A = dualMoment A τ t := by
    unfold dualMoment
    rw [← hdenom]
  calc
    ∫ n, Real.exp (t * ∑ i, τ i * (n i : ℝ)) ∂p.toMeasure =
        ∑' n : ι → ℤ, (p n).toReal • f n := by
          simpa [p, f] using hsum
    _ = ∑' n : ι → ℤ,
        dualPrimalWeight A τ t n / dualBaseNormalizer A := by
          apply tsum_congr
          intro n
          rw [smul_eq_mul, show (p n).toReal * f n = (p n).toReal * ‖f n‖ by
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]]
          exact hterm n
    _ = (∑' n : ι → ℤ, dualPrimalWeight A τ t n) /
        dualBaseNormalizer A := by
          rw [tsum_div_const]
    _ = dualMoment A τ t := hmomentSum

/-- A global degree-two lattice cell, serving as a plaquette index in the
centered exhaustion. -/
abbrev GlobalIntegerPlaquette := {p : LatticeCell 4 // latticeCellDegree p = 2}

/-- A global plaquette belongs to a centered finite cube when it is the square-cover
image of a finite source plaquette. -/
def PlaquetteInCube (N : ℕ) (p : GlobalIntegerPlaquette) : Prop :=
  ∃ q : SourceDualTwoCells (cube N), cubePlaquetteEmbedding N q = p.1

/-- Every finite family of global plaquettes is contained in every
sufficiently large centered cube. -/
theorem exists_cube_threshold_for_plaquettes (P₀ : Finset GlobalIntegerPlaquette) :
    ∃ N₀, ∀ N ≥ N₀, ∀ p ∈ P₀, PlaquetteInCube N p := by
  classical
  let R : ℕ := ∑ p ∈ P₀, cubeCellRadius p.1
  refine ⟨R + 2, ?_⟩
  intro N hN p hp
  have hrad : cubeCellRadius p.1 ≤ R := by
    dsimp [R]
    exact Finset.single_le_sum (s := P₀)
      (f := fun q : GlobalIntegerPlaquette => cubeCellRadius q.1)
      (fun q hq => Nat.zero_le _) hp
  have hcoord : ∀ i : Fin 4, cubeCoordMagnitude (p.1 i) < N := by
    intro i
    have hle : cubeCoordMagnitude (p.1 i) ≤ cubeCellRadius p.1 := by
      unfold cubeCellRadius
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin 4 => cubeCoordMagnitude (p.1 j))
        (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
    omega
  let q : SourceDualTwoCells (cube N) :=
    ⟨cubeDualCellPreimage N p.1 hcoord, by
      rw [cubeDualCellPreimage_degree]
      exact p.2⟩
  refine ⟨q, ?_⟩
  exact cubeDualCellPreimage_embedding N p.1 hcoord


noncomputable def cubePlaquettePreimage (N : ℕ) (p : GlobalIntegerPlaquette)
    (hp : PlaquetteInCube N p) : SourceDualTwoCells (cube N) :=
  Classical.choose hp

theorem cubePlaquetteEmbedding_preimage (N : ℕ) (p : GlobalIntegerPlaquette)
    (hp : PlaquetteInCube N p) :
    cubePlaquetteEmbedding N (cubePlaquettePreimage N p hp) = p.1 :=
  Classical.choose_spec hp

/-- Curvature at a global plaquette, evaluated by its unique finite source
coordinate. -/
noncomputable def cubeIntegerCurvatureAt (N : ℕ)
    (n : (sourceRootedTree (cube N)).Chord → ℤ)
    (p : GlobalIntegerPlaquette) (hp : PlaquetteInCube N p) : ℤ :=
  integerChordCurvature n (cubePlaquettePreimage N p hp)

/-- The coordinate map on any finite family of plaquettes contained in the
cube. -/
noncomputable def cubeCurvatureMap (N : ℕ) (P₀ : Finset GlobalIntegerPlaquette)
    (hP₀ : ∀ p ∈ P₀, PlaquetteInCube N p)
    (n : (sourceRootedTree (cube N)).Chord → ℤ) : P₀ → ℤ :=
  fun p => cubeIntegerCurvatureAt N n p.1 (hP₀ p.1 p.2)

/-- Push the finite dual probability law to the local integer curvatures. -/
noncomputable def cubeLocalCurvaturePMF (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (P₀ : Finset GlobalIntegerPlaquette)
    (hP₀ : ∀ p ∈ P₀, PlaquetteInCube N p) : PMF (P₀ → ℤ) :=
  (cubeDualChordPMF N β hβ).map (cubeCurvatureMap N P₀ hP₀)

/-- Restriction of local curvature configurations to a smaller plaquette set. -/
def restrictCurvature {P₀ P₁ : Finset GlobalIntegerPlaquette}
    (hP : P₀ ⊆ P₁) (x : P₁ → ℤ) : P₀ → ℤ :=
  fun p => x ⟨p.1, hP p.2⟩


theorem cubeLocalCurvaturePMF_consistent (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (P₀ P₁ : Finset GlobalIntegerPlaquette) (hP : P₀ ⊆ P₁)
    (hP₁ : ∀ p ∈ P₁, PlaquetteInCube N p) :
    PMF.map (restrictCurvature hP) (cubeLocalCurvaturePMF N β hβ P₁ hP₁) =
      cubeLocalCurvaturePMF N β hβ P₀ (fun p hp => hP₁ p (hP hp)) := by
  rw [cubeLocalCurvaturePMF, cubeLocalCurvaturePMF, PMF.map_comp]
  have hfun : restrictCurvature hP ∘ cubeCurvatureMap N P₁ hP₁ =
      cubeCurvatureMap N P₀ (fun p hp => hP₁ p (hP hp)) := by
    funext n p
    unfold restrictCurvature cubeCurvatureMap cubeIntegerCurvatureAt
    congr 1
  rw [hfun]

theorem integerChordCurvature_eq_sourceTest {B : Box 4}
    (n : (sourceRootedTree B).Chord → ℤ) (p : SourceDualTwoCells B) :
    (integerChordCurvature n p : ℝ) =
      ∑ e, sourceChordTest (sourcePlaquetteTest p) e * (n e : ℝ) := by
  rw [integerChordCurvature, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Int.cast_mul, integerCurlCoefficient_cast, sourcePlaquetteTest_chordValue]

theorem cubeLocalCurvaturePMF_coordinate_exp_moment (N : ℕ) (β t : ℝ)
    (hβ : 0 < β) (P : Finset GlobalIntegerPlaquette)
    (hP : ∀ p ∈ P, PlaquetteInCube N p) (p : P) :
    ∫ x, Real.exp (t * (x p : ℝ)) ∂
        (cubeLocalCurvaturePMF N β hβ P hP).toMeasure =
      sourceDualMoment β
        (sourcePlaquetteTest (cubePlaquettePreimage N p.1 (hP p.1 p.2))) t := by
  classical
  let q := cubePlaquettePreimage N p.1 (hP p.1 p.2)
  let T := sourcePlaquetteTest q
  let A := sourceChordMatrix (B := cube N) β
  have hA : A.PosDef := scaledChordMatrix_posDef _ _ hβ
  let c : ((sourceRootedTree (cube N)).Chord → ℤ) → (P → ℤ) :=
    cubeCurvatureMap N P hP
  let g : (P → ℤ) → ℝ := fun x => Real.exp (t * (x p : ℝ))
  have hc : Measurable c := by
    fun_prop (disch := aesop) [cubeCurvatureMap, cubeIntegerCurvatureAt,
      integerChordCurvature]
  have hg : Measurable g := by fun_prop
  have hcomp (n : (sourceRootedTree (cube N)).Chord → ℤ) :
      g (c n) = Real.exp (t * ∑ e, sourceChordTest T e * (n e : ℝ)) := by
    change Real.exp (t * (integerChordCurvature n q : ℝ)) = _
    rw [integerChordCurvature_eq_sourceTest]
  have hs0 := dualChordPMF_exp_linear_weighted_summable A hA
    (sourceChordTest T) t
  have hs : Summable (fun n : (sourceRootedTree (cube N)).Chord → ℤ =>
      (cubeDualChordPMF N β hβ n).toReal * ‖g (c n)‖) := by
    refine hs0.congr ?_
    intro n
    rw [cubeDualChordPMF, ← hcomp n]
  have hmap := pmf_map_integral (cubeDualChordPMF N β hβ) c g hc hg hs
  rw [cubeLocalCurvaturePMF, hmap]
  calc
    ∫ n, g (c n) ∂(cubeDualChordPMF N β hβ).toMeasure =
        ∫ n, Real.exp (t * ∑ e, sourceChordTest T e * (n e : ℝ)) ∂
          (cubeDualChordPMF N β hβ).toMeasure := by
            apply MeasureTheory.integral_congr_ae
            exact MeasureTheory.ae_of_all _ hcomp
    _ = dualMoment A (sourceChordTest T) t := by
      rw [cubeDualChordPMF]
      exact dualChordPMF_exp_linear_integral A hA (sourceChordTest T) t
    _ = sourceDualMoment β T t := by rfl

theorem cubeLocalCurvaturePMF_coordinate_exp_integrable (N : ℕ) (β t : ℝ)
    (hβ : 0 < β) (P : Finset GlobalIntegerPlaquette)
    (hP : ∀ p ∈ P, PlaquetteInCube N p) (p : P) :
    MeasureTheory.Integrable (fun x : P → ℤ => Real.exp (t * (x p : ℝ)))
      (cubeLocalCurvaturePMF N β hβ P hP).toMeasure := by
  classical
  let q := cubePlaquettePreimage N p.1 (hP p.1 p.2)
  let T := sourcePlaquetteTest q
  let A := sourceChordMatrix (B := cube N) β
  have hA : A.PosDef := scaledChordMatrix_posDef _ _ hβ
  let c : ((sourceRootedTree (cube N)).Chord → ℤ) → (P → ℤ) :=
    cubeCurvatureMap N P hP
  let g : (P → ℤ) → ℝ := fun x => Real.exp (t * (x p : ℝ))
  have hc : Measurable c := by
    fun_prop (disch := aesop) [cubeCurvatureMap, cubeIntegerCurvatureAt,
      integerChordCurvature]
  have hg : Measurable g := by fun_prop
  have hcomp (n : (sourceRootedTree (cube N)).Chord → ℤ) :
      g (c n) = Real.exp (t * ∑ e, sourceChordTest T e * (n e : ℝ)) := by
    change Real.exp (t * (integerChordCurvature n q : ℝ)) = _
    rw [integerChordCurvature_eq_sourceTest]
  have hs0 := dualChordPMF_exp_linear_weighted_summable A hA
    (sourceChordTest T) t
  have hs : Summable (fun n : (sourceRootedTree (cube N)).Chord → ℤ =>
      (cubeDualChordPMF N β hβ n).toReal * ‖g (c n)‖) := by
    refine hs0.congr ?_
    intro n
    rw [cubeDualChordPMF, ← hcomp n]
  exact pmf_map_integrable_of_summable_norm c g hc hg.stronglyMeasurable hs

noncomputable def cubeCurvaturePMFTotal (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (P : Finset GlobalIntegerPlaquette) : PMF (P → ℤ) := by
  classical
  by_cases hP : ∀ p ∈ P, PlaquetteInCube N p
  · exact cubeLocalCurvaturePMF N β hβ P hP
  · exact PMF.pure (fun _ => 0)

theorem cubeCurvaturePMFTotal_eventually_consistent (β : ℝ) (hβ : 0 < β)
    (P₀ P₁ : Finset GlobalIntegerPlaquette) (hP : P₀ ⊆ P₁) :
    ∃ N₀, ∀ N ≥ N₀,
      PMF.map (restrictCurvature hP) (cubeCurvaturePMFTotal N β hβ P₁) =
        cubeCurvaturePMFTotal N β hβ P₀ := by
  classical
  obtain ⟨N₀, hN₀⟩ := exists_cube_threshold_for_plaquettes P₁
  refine ⟨N₀, ?_⟩
  intro N hN
  have hP₁N : ∀ p ∈ P₁, PlaquetteInCube N p := hN₀ N hN
  have hP₀N : ∀ p ∈ P₀, PlaquetteInCube N p := fun p hp => hP₁N p (hP hp)
  rw [cubeCurvaturePMFTotal, dite_eq_left hP₁N,
    cubeCurvaturePMFTotal, dite_eq_left hP₀N]
  exact cubeLocalCurvaturePMF_consistent N β hβ P₀ P₁ hP hP₁N

theorem cubeCurvaturePMFTotal_coordinate_exp_integrable (N : ℕ) (β t : ℝ)
    (hβ : 0 < β) (P : Finset GlobalIntegerPlaquette) (p : P) :
    MeasureTheory.Integrable (fun x : P → ℤ => Real.exp (t * (x p : ℝ)))
      (cubeCurvaturePMFTotal N β hβ P).toMeasure := by
  classical
  by_cases hP : ∀ p ∈ P, PlaquetteInCube N p
  · unfold cubeCurvaturePMFTotal
    rw [dite_eq_left hP]
    exact cubeLocalCurvaturePMF_coordinate_exp_integrable N β t hβ P hP p
  · unfold cubeCurvaturePMFTotal
    rw [dite_eq_right hP]
    have hd := MeasureTheory.integrable_dirac
      (a := fun _ : P => (0 : ℤ))
      (f := fun x : P → ℤ => Real.exp (t * (x p : ℝ))) (by simp)
    simpa [PMF.toMeasure_pure] using hd

theorem cubeLocalCurvaturePMF_coordinate_exp_le (N : ℕ) (β t : ℝ)
    (hβ : 0 < β) (P : Finset GlobalIntegerPlaquette)
    (hP : ∀ p ∈ P, PlaquetteInCube N p) (p : P) :
    ∫ x, Real.exp (t * (x p : ℝ)) ∂
        (cubeLocalCurvaturePMF N β hβ P hP).toMeasure ≤
      Real.exp (t ^ 2 * β / 2) := by
  let q := cubePlaquettePreimage N p.1 (hP p.1 p.2)
  calc
    ∫ x, Real.exp (t * (x p : ℝ)) ∂
        (cubeLocalCurvaturePMF N β hβ P hP).toMeasure =
      sourceDualMoment β (sourcePlaquetteTest q) t :=
        cubeLocalCurvaturePMF_coordinate_exp_moment N β t hβ P hP p
    _ ≤ Real.exp ((t ^ 2 * β / 2) *
        Gaussian.quotientCovarianceQuadratic
          (FroehlichSpencer.FS82.Moment.SourceConstructor.sourceLatticeComplex
            (B := cube N)) (sourcePlaquetteTest q)) := by
      exact sourceDualMoment_le_gaussian hβ (sourcePlaquetteTest q) t
    _ ≤ Real.exp (t ^ 2 * β / 2) := by
      apply Real.exp_le_exp.mpr
      have hcov := sourcePlaquetteTest_covariance_le_one q
      have hcoef : 0 ≤ t ^ 2 * β / 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hcov hcoef]

theorem cubeCurvaturePMFTotal_coordinate_exp_le (N : ℕ) (β t : ℝ)
    (hβ : 0 < β) (P : Finset GlobalIntegerPlaquette) (p : P) :
    ∫ x, Real.exp (t * (x p : ℝ)) ∂(cubeCurvaturePMFTotal N β hβ P).toMeasure ≤
      Real.exp (t ^ 2 * β / 2) := by
  classical
  by_cases hP : ∀ p ∈ P, PlaquetteInCube N p
  · unfold cubeCurvaturePMFTotal
    rw [dite_eq_left hP]
    exact cubeLocalCurvaturePMF_coordinate_exp_le N β t hβ P hP p
  · unfold cubeCurvaturePMFTotal
    rw [dite_eq_right hP]
    have hexp : 1 ≤ Real.exp (t ^ 2 * β / 2) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      positivity
    rw [PMF.toMeasure_pure]
    simpa using hexp

theorem cubeCurvaturePMFTotal_coordinate_tail (N : ℕ) (β : ℝ)
    (hβ : 0 < β) (P : Finset GlobalIntegerPlaquette) (p : P)
    (s R : ℝ) (hs : 0 < s) :
    (cubeCurvaturePMFTotal N β hβ P).toMeasure
        {x | R ≤ (x p : ℝ)} ≤
      ENNReal.ofReal (Real.exp (s ^ 2 * β / 2) * Real.exp (-s * R)) ∧
    (cubeCurvaturePMFTotal N β hβ P).toMeasure
        {x | R ≤ -(x p : ℝ)} ≤
      ENNReal.ofReal (Real.exp (s ^ 2 * β / 2) * Real.exp (-s * R)) := by
  let law := cubeCurvaturePMFTotal N β hβ P
  let X : (P → ℤ) → ℝ := fun x => (x p : ℝ)
  have hX : Measurable X := by
    change Measurable (fun x : P → ℤ => (x p : ℝ))
    fun_prop
  have hXneg : Measurable (fun x : P → ℤ => -X x) := by
    change Measurable (fun x : P → ℤ => -(x p : ℝ))
    fun_prop
  have hIntPos := cubeCurvaturePMFTotal_coordinate_exp_integrable N β s hβ P p
  have hMomPos := cubeCurvaturePMFTotal_coordinate_exp_le N β s hβ P p
  have htailPos := pmf_exp_tail_bound law X s R (Real.exp (s ^ 2 * β / 2))
    hs hX hIntPos hMomPos
  have hIntNeg0 := cubeCurvaturePMFTotal_coordinate_exp_integrable N β (-s) hβ P p
  have hMomNeg0 := cubeCurvaturePMFTotal_coordinate_exp_le N β (-s) hβ P p
  have hfn : (fun x : P → ℤ => Real.exp (s * -X x)) =
      (fun x => Real.exp ((-s) * (x p : ℝ))) := by
    funext x
    congr 1
    simp [X]
  have hIntNeg : MeasureTheory.Integrable (fun x : P → ℤ => Real.exp (s * -X x))
      law.toMeasure := hfn ▸ hIntNeg0
  have hMomNeg : ∫ x, Real.exp (s * -X x) ∂law.toMeasure ≤
      Real.exp (s ^ 2 * β / 2) := by
    rw [hfn]
    have hcoeff : (-s) ^ 2 * β / 2 = s ^ 2 * β / 2 := by ring
    rw [hcoeff] at hMomNeg0
    exact hMomNeg0
  have htailNeg := pmf_exp_tail_bound law (fun x => -X x) s R
    (Real.exp (s ^ 2 * β / 2)) hs hXneg hIntNeg hMomNeg
  constructor
  · exact htailPos
  · exact htailNeg

def curvatureCoordinateBox {P : Type*} (K : ℕ) : Set (P → ℤ) :=
  {x | ∀ p, x p ∈ Set.Icc (-(K : ℤ)) (K : ℤ)}

theorem curvatureCoordinateBox_finite {P : Type*} [Fintype P] [DecidableEq P]
    (K : ℕ) : (curvatureCoordinateBox (P := P) K).Finite := by
  classical
  have hpi : (Set.univ.pi (fun _ : P =>
      (Set.Icc (-(K : ℤ)) (K : ℤ) : Set ℤ))).Finite :=
    Set.Finite.pi (fun _ : P => Set.finite_Icc (-(K : ℤ)) (K : ℤ))
  have heq : curvatureCoordinateBox (P := P) K =
      Set.univ.pi (fun _ : P => (Set.Icc (-(K : ℤ)) (K : ℤ) : Set ℤ)) := by
    ext x
    simp [curvatureCoordinateBox, Pi.le_def, forall_and]
  rw [heq]
  exact hpi

def curvatureCoordinateBad {P : Type*} (K : ℕ) (i : P × Bool) : Set (P → ℤ) :=
  if i.2 then {x | ((K + 1 : ℕ) : ℝ) ≤ (x i.1 : ℝ)}
  else {x | ((K + 1 : ℕ) : ℝ) ≤ -(x i.1 : ℝ)}

theorem cubeCurvaturePMFTotal_uniform_tight (β : ℝ) (hβ : 0 < β)
    (P : Finset GlobalIntegerPlaquette) :
    ∀ ε : ℝ, 0 < ε →
      ∃ S : Finset (P → ℤ), ∀ N,
        1 - ε ≤ ∑ x ∈ S, (cubeCurvaturePMFTotal N β hβ P x).toReal := by
  classical
  intro ε hε
  let C : ℝ := Real.exp (β / 2)
  let A : ℝ := (Fintype.card (P × Bool) : ℝ) * C
  have hA : 0 ≤ A := by positivity
  have hsum : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have harg : Tendsto (fun k : ℕ => -((k : ℝ) + 1)) atTop atBot := by
    exact (tendsto_neg_atBot_iff.mpr hsum)
  have hdecay : Tendsto (fun k : ℕ => Real.exp (-((k : ℝ) + 1))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp harg
  have hδ : 0 < ε / (A + 1) := by positivity
  have hev : ∀ᶠ k : ℕ in atTop,
      Real.exp (-((k : ℝ) + 1)) < ε / (A + 1) :=
    hdecay.eventually (Iio_mem_nhds hδ)
  obtain ⟨K, hK⟩ := Filter.Eventually.exists hev
  have hAexp : A * Real.exp (-((K : ℝ) + 1)) < ε := by
    calc
      A * Real.exp (-((K : ℝ) + 1)) ≤
          (A + 1) * Real.exp (-((K : ℝ) + 1)) := by
            exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ < (ε / (A + 1)) * (A + 1) :=
        by
          calc
            _ = Real.exp (-((K : ℝ) + 1)) * (A + 1) := by ring
            _ < (ε / (A + 1)) * (A + 1) :=
              mul_lt_mul_of_pos_right hK (show 0 < A + 1 by linarith)
      _ = ε := by field_simp
  let box := curvatureCoordinateBox (P := P) K
  have hboxFinite := curvatureCoordinateBox_finite (P := P) K
  let S := hboxFinite.toFinset
  have hS : (S : Set (P → ℤ)) = box := hboxFinite.coe_toFinset
  have hBadCover (x : P → ℤ) (hx : x ∈ boxᶜ) :
      x ∈ ⋃ i : P × Bool, curvatureCoordinateBad K i := by
    have hnot : ∃ p : P,
        x p < -(K : ℤ) ∨ (K : ℤ) < x p := by
      by_contra h
      push Not at h
      apply hx
      intro p
      rw [Set.mem_Icc]
      exact ⟨h p |>.1, h p |>.2⟩
    rcases hnot with ⟨p, hlow | hhigh⟩
    · have hi : ((K + 1 : ℕ) : ℤ) ≤ -x p := by omega
      have hir : ((K + 1 : ℕ) : ℝ) ≤ -(x p : ℝ) := by exact_mod_cast hi
      refine Set.mem_iUnion.mpr ⟨(p, false), ?_⟩
      simpa [curvatureCoordinateBad] using hir
    · have hi : ((K + 1 : ℕ) : ℤ) ≤ x p := by omega
      have hir : ((K + 1 : ℕ) : ℝ) ≤ (x p : ℝ) := by exact_mod_cast hi
      refine Set.mem_iUnion.mpr ⟨(p, true), ?_⟩
      simpa [curvatureCoordinateBad] using hir
  have htail (N : ℕ) (i : P × Bool) :
      (cubeCurvaturePMFTotal N β hβ P).toMeasure (curvatureCoordinateBad K i) ≤
        ENNReal.ofReal (C * Real.exp (-((K : ℝ) + 1))) := by
    rcases i with ⟨p, b⟩
    cases b
    · simpa [curvatureCoordinateBad, C] using
        (cubeCurvaturePMFTotal_coordinate_tail N β hβ P p 1 ((K : ℝ) + 1)
          one_pos).2
    · simpa [curvatureCoordinateBad, C] using
        (cubeCurvaturePMFTotal_coordinate_tail N β hβ P p 1 ((K : ℝ) + 1)
          one_pos).1
  have hunion (N : ℕ) :
      (cubeCurvaturePMFTotal N β hβ P).toMeasure (⋃ i : P × Bool,
          curvatureCoordinateBad K i) ≤ ENNReal.ofReal (A * Real.exp (-((K : ℝ) + 1))) := by
    calc
      _ ≤ ∑' i : P × Bool,
          (cubeCurvaturePMFTotal N β hβ P).toMeasure (curvatureCoordinateBad K i) :=
        MeasureTheory.measure_iUnion_le _
      _ = ∑ i : P × Bool,
          (cubeCurvaturePMFTotal N β hβ P).toMeasure (curvatureCoordinateBad K i) := by
        rw [tsum_fintype]
      _ ≤ ∑ i : P × Bool, ENNReal.ofReal (C * Real.exp (-((K : ℝ) + 1))) :=
        Finset.sum_le_sum fun i hi => htail N i
      _ = ENNReal.ofReal (A * Real.exp (-((K : ℝ) + 1))) := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · congr 1
          simp [A, C, Finset.sum_const, nsmul_eq_mul]
          ring
        · intro i hi
          positivity
  refine ⟨S, ?_⟩
  intro N
  have htailBox : (cubeCurvaturePMFTotal N β hβ P).toMeasure boxᶜ ≤
      ENNReal.ofReal ε := by
    calc
      _ ≤ (cubeCurvaturePMFTotal N β hβ P).toMeasure
          (⋃ i : P × Bool, curvatureCoordinateBad K i) :=
        MeasureTheory.measure_mono (by
          intro x hx
          exact hBadCover x hx)
      _ ≤ ENNReal.ofReal (A * Real.exp (-((K : ℝ) + 1))) := hunion N
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hAexp.le
  let μ := (cubeCurvaturePMFTotal N β hβ P).toMeasure
  have hSmeas : MeasurableSet box := hboxFinite.measurableSet
  have hμSle : μ box ≤ 1 := by
    calc
      μ box ≤ μ Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := by simp [μ]
  have hμSne : μ box ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hμSle ENNReal.one_lt_top)
  have hcompl : μ boxᶜ = 1 - μ box := by
    rw [MeasureTheory.measure_compl hSmeas hμSne]
    simp [μ]
  have hcomplTop : μ boxᶜ ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt htailBox ENNReal.ofReal_lt_top)
  have hcomplReal : (μ boxᶜ).toReal = 1 - (μ box).toReal := by
    rw [hcompl, ENNReal.toReal_sub_of_le hμSle ENNReal.one_ne_top]
    simp [ENNReal.toReal_one]
  have hcomplRealLe : (μ boxᶜ).toReal ≤ ε := by
    have h := (ENNReal.toReal_le_toReal hcomplTop (ENNReal.ofReal_ne_top)).2 htailBox
    simpa [ENNReal.toReal_ofReal (le_of_lt hε)] using h
  have hcomplLe : 1 - (μ box).toReal ≤ ε := by
    rw [← hcomplReal]
    exact hcomplRealLe
  have hmass : 1 - ε ≤ (μ box).toReal := by linarith
  have hsumReal : (μ box).toReal =
      ∑ x ∈ S, (cubeCurvaturePMFTotal N β hβ P x).toReal := by
    dsimp [μ]
    rw [← hS, PMF.toMeasure_apply_finset]
    rw [ENNReal.toReal_sum (fun x hx =>
      (cubeCurvaturePMFTotal N β hβ P).apply_ne_top x)]
  rw [← hsumReal]
  exact hmass

end FroehlichSpencer.FS82.Infinite
