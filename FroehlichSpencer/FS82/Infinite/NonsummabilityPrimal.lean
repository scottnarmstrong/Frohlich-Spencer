/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Infinite.NonsummabilityRoot
public import FroehlichSpencer.FS82.Wilson.PrimalFieldStrength
public import FroehlichSpencer.FS82.Wilson.PerimeterChordBridge
public import FroehlichSpencer.FS82.Infinite.LimitStateLaw
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Passing the dual-curvature root through a primal observable bridge

The finite-volume primal insertion and normalized dual-curvature identities
are proved in `Wilson.PrimalFieldStrength`.
-/

@[expose] public section

open Filter Topology
open MeasureTheory
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Infinite.Fourier
open FroehlichSpencer.FS82.Moment.Comparison
open FroehlichSpencer.FS82.Wilson
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.SourceTreeChart
open FroehlichSpencer.FS82.Gaussian.TreeGaugeQuotient
open FroehlichSpencer.FS82.Moment.SourceConstructor

namespace FroehlichSpencer.FS82.Infinite.Nonsummability

private theorem primal_pmf_toReal_measure_finset
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] [DecidableEq α] (p : PMF α) (T : Finset α) :
    (p.toMeasure (T : Set α)).toReal = ∑ x ∈ T, (p x).toReal := by
  rw [PMF.toMeasure_apply_finset, ENNReal.toReal_sum
    (fun x hx => p.apply_ne_top x)]

private theorem primal_integrable_square_of_fourth
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (X : α → ℝ) (hX : AEStronglyMeasurable X μ)
    (hfour : Integrable (fun x => X x ^ 4) μ) :
    Integrable (fun x => X x ^ 2) μ := by
  have hdom : Integrable (fun x => 1 + X x ^ 4) μ :=
    (integrable_const (1 : ℝ)).add hfour
  have hmeas : AEStronglyMeasurable (fun x => X x ^ 2) μ := by
    fun_prop
  apply hdom.mono' hmeas
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (sq_nonneg (X x))]
  nlinarith [sq_nonneg (X x ^ 2 - 1 / 2)]

private theorem primal_sq_le_exp_abs (x : ℝ) :
    x ^ 2 ≤ 4 * Real.exp |x| := by
  let u := |x|
  have hu : 0 ≤ u := abs_nonneg x
  have hlin : u / 2 + 1 ≤ Real.exp (u / 2) := Real.add_one_le_exp _
  have hnonneg : 0 ≤ u / 2 + 1 := by positivity
  have hsq : (u / 2 + 1) ^ 2 ≤ Real.exp (u / 2) ^ 2 := by
    nlinarith [mul_self_le_mul_self hnonneg hlin]
  have hexp : Real.exp (u / 2) ^ 2 = Real.exp u := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring_nf
  have hpoly : u ^ 2 ≤ 4 * (u / 2 + 1) ^ 2 := by nlinarith
  have hx2 : x ^ 2 = u ^ 2 := by simp [u, sq_abs]
  calc
    x ^ 2 = u ^ 2 := hx2
    _ ≤ 4 * (u / 2 + 1) ^ 2 := hpoly
    _ ≤ 4 * Real.exp (u / 2) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 4 * Real.exp u := by rw [hexp]
    _ = 4 * Real.exp |x| := rfl

private theorem primal_exp_abs_le (x : ℝ) :
    Real.exp |x| ≤ Real.exp x + Real.exp (-x) := Real.exp_abs_le x

private theorem primal_fourth_le_exp_abs (x : ℝ) :
    x ^ 4 ≤ 256 * Real.exp |x| := by
  have hhalf := primal_sq_le_exp_abs (x / 2)
  have habs : |x / 2| = |x| / 2 := by simp [abs_div]
  rw [habs] at hhalf
  have hsq : x ^ 2 ≤ 16 * Real.exp (|x| / 2) := by
    nlinarith [hhalf]
  have hsquare := mul_self_le_mul_self (sq_nonneg x) hsq
  calc
    x ^ 4 = (x ^ 2) * (x ^ 2) := by ring
    _ ≤ (16 * Real.exp (|x| / 2)) ^ 2 := by nlinarith [hsquare]
    _ = 256 * Real.exp (|x| / 2) ^ 2 := by ring
    _ = 256 * Real.exp |x| := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring_nf

private theorem primal_cubeCoordinate_fourthMoment_bound
    (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (P : Finset GlobalIntegerPlaquette) (p : P) :
    Integrable (fun ω : P → ℤ => (ω p : ℝ) ^ 4)
        (cubeCurvaturePMFTotal N β hβ P).toMeasure ∧
      ∫ ω, (ω p : ℝ) ^ 4 ∂(cubeCurvaturePMFTotal N β hβ P).toMeasure ≤
        512 * Real.exp (β / 2) := by
  let ν := (cubeCurvaturePMFTotal N β hβ P).toMeasure
  let X : (P → ℤ) → ℝ := fun ω => (ω p : ℝ)
  have hplus := cubeCurvaturePMFTotal_coordinate_exp_integrable
    N β 1 hβ P p
  have hminus := cubeCurvaturePMFTotal_coordinate_exp_integrable
    N β (-1) hβ P p
  have hdom : Integrable (fun ω => 256 *
      (Real.exp (X ω) + Real.exp (-X ω))) ν := by
    simpa [ν, X, smul_eq_mul, mul_add] using (hplus.add hminus).const_mul 256
  have hXmeas : Measurable X := by fun_prop
  have hXfourMeas : AEStronglyMeasurable (fun ω => X ω ^ 4) ν :=
    (hXmeas.pow_const 4).aestronglyMeasurable
  have hfour : Integrable (fun ω => X ω ^ 4) ν := by
    apply hdom.mono' hXfourMeas
    filter_upwards [] with ω
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ X ω ^ 4)]
    calc
      X ω ^ 4 ≤ 256 * Real.exp |X ω| := by
        exact primal_fourth_le_exp_abs (X ω)
      _ ≤ 256 * (Real.exp (X ω) + Real.exp (-X ω)) := by
        exact mul_le_mul_of_nonneg_left (primal_exp_abs_le (X ω)) (by norm_num)
  have hplusBound := cubeCurvaturePMFTotal_coordinate_exp_le
    N β 1 hβ P p
  have hminusBound := cubeCurvaturePMFTotal_coordinate_exp_le
    N β (-1) hβ P p
  have hplus' : Integrable (fun ω => Real.exp (X ω)) ν := by
    simpa [ν, X] using hplus
  have hminus' : Integrable (fun ω => Real.exp (-X ω)) ν := by
    simpa [ν, X, neg_mul] using hminus
  have hbound : ∫ ω, X ω ^ 4 ∂ν ≤ 512 * Real.exp (β / 2) := by
    calc
      ∫ ω, X ω ^ 4 ∂ν ≤ ∫ ω,
          256 * (Real.exp (X ω) + Real.exp (-X ω)) ∂ν :=
            MeasureTheory.integral_mono hfour hdom (fun ω =>
              calc
                X ω ^ 4 ≤ 256 * Real.exp |X ω| := primal_fourth_le_exp_abs (X ω)
                _ ≤ 256 * (Real.exp (X ω) + Real.exp (-X ω)) :=
                  mul_le_mul_of_nonneg_left (primal_exp_abs_le (X ω)) (by norm_num))
      _ = 256 * (∫ ω, Real.exp (X ω) ∂ν +
          ∫ ω, Real.exp (-X ω) ∂ν) := by
            rw [integral_const_mul, integral_add hplus' hminus']
      _ ≤ 512 * Real.exp (β / 2) := by
        have hp : ∫ ω, Real.exp (X ω) ∂ν ≤ Real.exp (β / 2) := by
          simpa [ν, X] using hplusBound
        have hm : ∫ ω, Real.exp (-X ω) ∂ν ≤ Real.exp (β / 2) := by
          simpa [ν, X, neg_mul] using hminusBound
        nlinarith
  refine ⟨?_, ?_⟩
  · simpa [ν, X] using hfour
  · simpa [ν, X] using hbound

private theorem primal_integrable_product_square_of_fourth
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (X Y : α → ℝ)
    (hXmeas : AEStronglyMeasurable X μ)
    (hYmeas : AEStronglyMeasurable Y μ)
    (hX : Integrable (fun x => X x ^ 4) μ)
    (hY : Integrable (fun x => Y x ^ 4) μ) :
    Integrable (fun x => (X x * Y x) ^ 2) μ := by
  have hdom : Integrable (fun x => (1 / 2 : ℝ) * (X x ^ 4 + Y x ^ 4)) μ :=
    (hX.add hY).const_mul (1 / 2)
  have hmeas : AEStronglyMeasurable (fun x => (X x * Y x) ^ 2) μ :=
    ((hXmeas.mul hYmeas).pow 2)
  apply hdom.mono' hmeas
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (sq_nonneg (X x * Y x))]
  nlinarith [sq_nonneg (X x ^ 2 - Y x ^ 2)]

private theorem primal_pmf_mass_summable {α : Type*} [Countable α]
    (p : PMF α) : Summable (fun x => (p x).toReal) := by
  apply ENNReal.summable_toReal
  rw [p.tsum_coe]
  exact ENNReal.one_ne_top

private theorem primal_pmf_integrable_of_secondMoment
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] (p : PMF α) (f : α → ℝ)
    (hsq : Summable (fun x => (p x).toReal * (f x) ^ 2)) :
    Integrable f p.toMeasure := by
  have hmass := primal_pmf_mass_summable p
  have hnormBound (x : α) : ‖f x‖ ≤ 1 + (f x) ^ 2 := by
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|f x| - 1 / 2), sq_abs (f x)]
  have hdom : Summable (fun x => (p x).toReal * (1 + (f x) ^ 2)) := by
    simpa [mul_add] using hmass.add hsq
  have hnorm : Summable (fun x => (p x).toReal * ‖f x‖) :=
    Summable.of_nonneg_of_le
      (fun x => mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _))
      (fun x => mul_le_mul_of_nonneg_left (hnormBound x) ENNReal.toReal_nonneg)
      hdom
  exact pmf_integrable_of_summable_norm hnorm

private noncomputable def primalFiniteShiftAverageWeight (n : ℕ) : ENNReal :=
  ((Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n} : ℕ) : ENNReal)⁻¹

private theorem primalFiniteShiftAverageWeight_ne_zero (n : ℕ) :
    primalFiniteShiftAverageWeight n ≠ 0 := by
  unfold primalFiniteShiftAverageWeight
  apply ENNReal.inv_ne_zero.mpr
  exact ENNReal.natCast_ne_top _

private theorem primalFiniteShiftAverageWeight_ne_top (n : ℕ) :
    primalFiniteShiftAverageWeight n ≠ ⊤ := by
  unfold primalFiniteShiftAverageWeight
  apply ENNReal.inv_ne_top.mpr
  have hcard : 0 < Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n} :=
    Fintype.card_pos_iff.mpr ⟨⟨0, zero_mem_latticeShiftBox n⟩⟩
  exact_mod_cast (Nat.ne_of_gt hcard)

private theorem primal_finiteShiftAverage_toMeasure_eq
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] [DecidableEq α]
    (n : ℕ) (f : LatticeShift → PMF α) :
    (finiteShiftAverage n f).toMeasure =
      ∑ a ∈ latticeShiftBox n,
        primalFiniteShiftAverageWeight n • (f a).toMeasure := by
  classical
  apply MeasureTheory.Measure.ext
  intro s hs
  rw [finiteShiftAverage, PMF.toMeasure_bind_apply _ _ _ hs]
  let w := primalFiniteShiftAverageWeight n
  have hterm (a : LatticeShift) :
      latticeShiftUniform n a * (f a).toMeasure s =
        (if a ∈ latticeShiftBox n then w else 0) * (f a).toMeasure s := by
    rw [latticeShiftUniform_apply]
    simp [w, primalFiniteShiftAverageWeight]
  calc
    (∑' a : LatticeShift,
        latticeShiftUniform n a * (f a).toMeasure s) =
      ∑' a : LatticeShift,
        (if a ∈ latticeShiftBox n then w else 0) * (f a).toMeasure s := by
          apply tsum_congr
          intro a
          exact hterm a
    _ = ∑ a ∈ latticeShiftBox n,
        (if a ∈ latticeShiftBox n then w else 0) * (f a).toMeasure s := by
          apply tsum_eq_sum
          intro a ha
          simp [ha]
    _ = ∑ a ∈ latticeShiftBox n,
        primalFiniteShiftAverageWeight n • (f a).toMeasure s := by
          apply Finset.sum_congr rfl
          intro a ha
          simp [ha, w, primalFiniteShiftAverageWeight]
  rw [MeasureTheory.Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro a ha
  rw [MeasureTheory.Measure.smul_apply, smul_eq_mul]

private theorem primal_finiteShiftAverage_integral
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] [DecidableEq α]
    (n : ℕ) (f : LatticeShift → PMF α) (g : α → ℝ)
    (hfi : ∀ a, Integrable g (f a).toMeasure) :
    Integrable g (finiteShiftAverage n f).toMeasure ∧
      ∫ x, g x ∂(finiteShiftAverage n f).toMeasure =
        (Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n} : ℝ)⁻¹ *
          ∑ a ∈ latticeShiftBox n, ∫ x, g x ∂(f a).toMeasure := by
  classical
  rw [primal_finiteShiftAverage_toMeasure_eq]
  have hsumInt : Integrable g
      (∑ a ∈ latticeShiftBox n,
        primalFiniteShiftAverageWeight n • (f a).toMeasure) := by
    rw [MeasureTheory.integrable_finsetSum_measure]
    intro a ha
    rw [MeasureTheory.integrable_smul_measure
      (primalFiniteShiftAverageWeight_ne_zero n) (primalFiniteShiftAverageWeight_ne_top n)]
    exact hfi a
  constructor
  · exact hsumInt
  · rw [MeasureTheory.integral_finsetSum_measure]
    · simp only [MeasureTheory.integral_smul_measure, smul_eq_mul]
      simp [primalFiniteShiftAverageWeight, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, ← Finset.mul_sum]
    · intro a ha
      rw [MeasureTheory.integrable_smul_measure
        (primalFiniteShiftAverageWeight_ne_zero n) (primalFiniteShiftAverageWeight_ne_top n)]
      exact hfi a

private theorem primal_integral_finsetEq
    (ν : CurvatureCylinderState) {P Q : Finset GlobalIntegerPlaquette}
    (hPQ : P = Q) (f : (P → ℤ) → ℝ)
    (hf' : StronglyMeasurable f) :
    ∫ x, f x ∂(ν.law P).toMeasure =
      ∫ y, f ((curvatureAssignmentCastEquiv hPQ).symm y)
        ∂(ν.law Q).toMeasure := by
  let e := curvatureAssignmentCastEquiv hPQ
  have hmap : PMF.map e (ν.law P) = ν.law Q :=
    curvatureCylinderLaw_map_finsetEq ν hPQ
  have he : Measurable e := by fun_prop
  let g : (Q → ℤ) → ℝ := fun y => f (e.symm y)
  have hg : StronglyMeasurable g := by fun_prop
  calc
    ∫ x, f x ∂(ν.law P).toMeasure =
        ∫ x, g (e x) ∂(ν.law P).toMeasure := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by simp [g]
    _ = ∫ y, g y ∂(PMF.map e (ν.law P)).toMeasure := by
      rw [← PMF.toMeasure_map e (ν.law P) he]
      exact (MeasureTheory.integral_map_of_stronglyMeasurable he hg).symm
    _ = ∫ y, g y ∂(ν.law Q).toMeasure := by rw [hmap]
    _ = ∫ y, f (e.symm y) ∂(ν.law Q).toMeasure := rfl

private theorem primalSubtypeSumPair {α : Type*} [DecidableEq α]
    (x y : α) (hxy : x ≠ y) (s : Finset α) (hs : s = {x, y})
    (f : {z // z ∈ s} → ℝ) :
    (∑ z : s, f z) = f ⟨x, by rw [hs]; simp⟩ + f ⟨y, by rw [hs]; simp⟩ := by
  classical
  let e : {z // z ∈ s} ≃ {z // z ∈ ({x, y} : Finset α)} :=
    Equiv.subtypeEquivRight (fun z => by rw [hs])
  let g : α → ℝ := fun z =>
    if hz : z ∈ ({x, y} : Finset α) then f (e.symm ⟨z, hz⟩) else 0
  calc
    (∑ z : s, f z) =
        ∑ z : {z // z ∈ ({x, y} : Finset α)}, f (e.symm z) := by
          exact Fintype.sum_equiv e _ _ (by
            intro z
            change f z = f (e.symm (e z))
            rw [Equiv.symm_apply_apply])
    _ = ∑ z ∈ ({x, y} : Finset α), g z := by
      have hfun : (fun z : {z // z ∈ ({x, y} : Finset α)} =>
          f (e.symm z)) = fun z => g z.1 := by
        funext z
        change f (e.symm z) =
          (if hz : z.1 ∈ ({x, y} : Finset α) then
            f (e.symm ⟨z.1, hz⟩) else 0)
        rw [dite_eq_left z.2]
      rw [hfun]
      exact (Finset.sum_subtype ({x, y} : Finset α)
        (fun _ => Iff.rfl) g).symm
    _ = g x + g y := by simp [hxy]
    _ = f ⟨x, by rw [hs]; simp⟩ + f ⟨y, by rw [hs]; simp⟩ := by
      have hx : e.symm ⟨x, by simp⟩ = ⟨x, by rw [hs]; simp⟩ := by
        apply Subtype.ext
        rfl
      have hy : e.symm ⟨y, by simp⟩ = ⟨y, by rw [hs]; simp⟩ := by
        apply Subtype.ext
        rfl
      simp [g, hx, hy]

private theorem primal_sourceWilsonMode_toExactField
    {B : Cubical.Box 4} (S : Cubical.Chain 4 B)
    (hS : Cubical.homogeneousSupport S 2) (m : SourceWilsonModes S) :
    ∃ x : SourceIntegerDualGaugeClass B,
      integerStarMap S + x.1 = integerStarMap (plaquetteModeChain m.1) := by
  let p : Cubical.Chain 4 B := plaquetteModeChain m.1 - S
  have hpHom : Cubical.homogeneousSupport p 2 := by
    intro c hc
    have hp : c ∈ (plaquetteModeChain m.1).support ∨ c ∈ S.support := by
      by_contra h
      have hA : c ∉ (plaquetteModeChain m.1).support := fun hA => h (Or.inl hA)
      have hB : c ∉ S.support := fun hB => h (Or.inr hB)
      have hA0 := Finsupp.notMem_support_iff.mp hA
      have hB0 := Finsupp.notMem_support_iff.mp hB
      exact (Finsupp.mem_support_iff.mp hc) (by simp [p, hA0, hB0])
    rcases hp with hpq | hps
    · exact plaquetteModeChain_homogeneousSupport m.1 c hpq
    · exact hS c hps
  have hboundaryEq := (plaquetteModeDivergence_eq_boundary m.1 S hS).1 m.2
  have hclosed : Cubical.boundary p = 0 := by
    dsimp [p]
    rw [map_sub, hboundaryEq]
    simp
  let q : DualIntegerChain B := integerStarMap p
  have hqDegree : dualIntegerHomogeneousSupport q 2 :=
    integerStarMap_homogeneousSupport p 2 hpHom
  have hqDegree' : ∀ c ∈ q.support, Cubical.dualCellDegree c = 2 :=
    (dualIntegerHomogeneousSupport_iff q 2).mp hqDegree
  have hclosedStar : Cubical.boundary (integerStarMapInverse q) = 0 := by
    simpa [q, integerStarMapInverse_starMap] using hclosed
  obtain ⟨a, ha⟩ := exists_sourceIntegerDualOneField_of_closedDualChain
    q hqDegree' hclosedStar
  refine ⟨⟨sourceIntegerDualOneDifferential a, ⟨a, rfl⟩⟩, ?_⟩
  change integerStarMap S +
      integerDualExteriorDifference
        (FroehlichSpencer.FS82.Wilson.sourceIntegerDualOneChain a) = _
  rw [ha]
  dsimp [q, p]
  rw [map_sub]
  abel

private noncomputable def primal_sourceWilsonModesEquiv
    {B : Cubical.Box 4} (S : Cubical.Chain 4 B)
    (hS : Cubical.homogeneousSupport S 2) :
    SourceIntegerDualGaugeClass B ≃ SourceWilsonModes S := by
  classical
  refine Equiv.ofBijective (sourceExactFieldToWilsonMode S hS) ⟨?_, ?_⟩
  · intro x y hxy
    have hstar := congrArg (fun m : SourceWilsonModes S =>
      integerStarMap (plaquetteModeChain m.1)) hxy
    rw [sourceExactFieldToWilsonMode_star S hS x,
      sourceExactFieldToWilsonMode_star S hS y] at hstar
    have hx : integerStarMap S + x.1 = integerStarMap S + y.1 := hstar
    have hxy' : x.1 = y.1 := add_left_cancel hx
    exact Subtype.ext hxy'
  · intro m
    obtain ⟨x, hx⟩ := primal_sourceWilsonMode_toExactField S hS m
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply funext
    intro p
    have hstar := sourceExactFieldToWilsonMode_star S hS x
    have hchain : plaquetteModeChain
        (sourceExactFieldToWilsonMode S hS x).1 = plaquetteModeChain m.1 := by
      calc
        plaquetteModeChain (sourceExactFieldToWilsonMode S hS x).1 =
            integerStarMapInverse
              (integerStarMap (plaquetteModeChain
                (sourceExactFieldToWilsonMode S hS x).1) : DualIntegerChain B) := by
              rw [integerStarMapInverse_starMap]
        _ = integerStarMapInverse (integerStarMap S + x.1) := by rw [hstar]
        _ = integerStarMapInverse (integerStarMap (plaquetteModeChain m.1)) := by
          congr 1
        _ = plaquetteModeChain m.1 := integerStarMapInverse_starMap _
    have hp := congrArg (fun q : Cubical.Chain 4 B => q p.1) hchain
    simpa only [plaquetteModeChain_apply] using hp

private theorem primal_integerChordCurvature_eq_gaugeClass
    {B : Cubical.Box 4} (n : (sourceRootedTree B).Chord → ℤ)
    (p : SourceDualTwoCells B) :
    integerChordCurvature n p = (chordGaugeClass n).1 p.1 := by
  have hcast : (integerChordCurvature n p : ℝ) =
      ((chordGaugeClass n).1 p.1 : ℝ) := by
    rw [integerChordCurvature_cast_chartCurl, chordGaugeClass_cast]
    let T := sourceRootedTree B
    have hext : realLinkField (T.extendChord n) =
        sourceFunctionToEuclidean (extendChordsLinear T (fun e => (n e : ℝ))) := by
      ext e
      by_cases ht : e ∈ Set.range T.treeEdge
      · rcases ht with ⟨w, hwe⟩
        subst e
        have hleft : T.extendChord n (T.treeEdge w) = 0 :=
          extendChord_treeEdge n w
        have hright : T.extendChord (fun a => (n a : ℝ))
            (T.treeEdge w) = 0 :=
          extendChordsLinear_mem_treeGauge T (fun a => (n a : ℝ)) w
        change ((T.extendChord n (T.treeEdge w) : ℤ) : ℝ) =
          T.extendChord (fun a => (n a : ℝ)) (T.treeEdge w)
        rw [hleft, hright]
        norm_num
      · change ((T.extendChord n e : ℤ) : ℝ) =
          T.extendChord (fun a => (n a : ℝ)) e
        simp [RootedTreeGauge.extendChord, ht]
    have hphysical := sourceTreeChartPhysicalCurl_eq_quotientCurvature
      T p (fun e => (n e : ℝ))
    rw [hphysical, physicalCurlClassCurvatureAt_mk, hext]
  exact_mod_cast hcast

public def primalDualCellOfPrimal {B : Cubical.Box 4}
    (p : PrimalPlaquettes B) : SourceDualTwoCells B :=
  ⟨Cubical.primalDualCellEquiv p.1, by
    have h := Cubical.star_complementary_degree p.1
    omega⟩

private theorem primal_integerStarMap_plaquetteMode_apply
    {B : Cubical.Box 4} (m : PrimalPlaquettes B → ℤ)
    (p : PrimalPlaquettes B) :
    integerStarMap (plaquetteModeChain m)
        (Cubical.primalDualCellEquiv p.1) = m p := by
  simp [integerStarMap, Finsupp.equivMapDomain_apply, plaquetteModeChain_apply]

private theorem primal_dualChordPMF_curvatureProduct_integrable
    {B : Cubical.Box 4} (β : ℝ) (hβ : 0 < β)
    (p q : SourceDualTwoCells B) :
    Integrable
      (fun n : (sourceRootedTree B).Chord → ℤ =>
        (integerChordCurvature n p : ℝ) * (integerChordCurvature n q : ℝ))
      (dualChordPMF (sourceChordMatrix (B := B) β)
        (scaledChordMatrix_posDef _ _ hβ)).toMeasure := by
  classical
  let A := sourceChordMatrix (B := B) β
  let hA : A.PosDef := scaledChordMatrix_posDef _ _ hβ
  let μp := sourcePlaquetteTest p
  let μq := sourcePlaquetteTest q
  let X : ((sourceRootedTree B).Chord → ℤ) → ℝ :=
    fun n => integerChordCurvature n p
  let Y : ((sourceRootedTree B).Chord → ℤ) → ℝ :=
    fun n => integerChordCurvature n q
  let τ (s t : ℝ) : (sourceRootedTree B).Chord → ℝ := fun e =>
    s * sourceChordTest μp e + t * sourceChordTest μq e
  have hX (n : (sourceRootedTree B).Chord → ℤ) :
      X n = ∑ e, sourceChordTest μp e * (n e : ℝ) := by
    simpa [X, μp] using integerChordCurvature_eq_sourceTest n p
  have hY (n : (sourceRootedTree B).Chord → ℤ) :
      Y n = ∑ e, sourceChordTest μq e * (n e : ℝ) := by
    simpa [Y, μq] using integerChordCurvature_eq_sourceTest n q
  have hlinear (s t : ℝ) (n : (sourceRootedTree B).Chord → ℤ) :
      s * X n + t * Y n = ∑ e, τ s t e * (n e : ℝ) := by
    rw [hX n, hY n]
    dsimp [τ]
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    ring
  let pμf := dualChordPMF A hA
  have hexpSummable (s t : ℝ) :
      Summable (fun n => (pμf n).toReal *
        ‖Real.exp (s * X n + t * Y n)‖) := by
    have hbase := dualChordPMF_exp_linear_weighted_summable A hA
      (τ s t) 1
    refine hbase.congr ?_
    intro n
    rw [hlinear s t n]
    simp [pμf, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hXbound (n : (sourceRootedTree B).Chord → ℤ) :
      |X n| ≤ Real.exp (X n) + Real.exp (-X n) := by
    calc
      |X n| ≤ Real.exp |X n| := by
        nlinarith [Real.add_one_le_exp |X n|, abs_nonneg (X n)]
      _ ≤ Real.exp (X n) + Real.exp (-X n) := Real.exp_abs_le (X n)
  have hYbound (n : (sourceRootedTree B).Chord → ℤ) :
      |Y n| ≤ Real.exp (Y n) + Real.exp (-Y n) := by
    calc
      |Y n| ≤ Real.exp |Y n| := by
        nlinarith [Real.add_one_le_exp |Y n|, abs_nonneg (Y n)]
      _ ≤ Real.exp (Y n) + Real.exp (-Y n) := Real.exp_abs_le (Y n)
  have hdom (n : (sourceRootedTree B).Chord → ℤ) :
      ‖X n * Y n‖ ≤ Real.exp (X n + Y n) + Real.exp (X n - Y n) +
        Real.exp (-X n + Y n) + Real.exp (-X n - Y n) := by
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |X n| * |Y n| ≤
          (Real.exp (X n) + Real.exp (-X n)) *
            (Real.exp (Y n) + Real.exp (-Y n)) :=
              mul_le_mul (hXbound n) (hYbound n) (abs_nonneg _) (by positivity)
      _ = Real.exp (X n) * Real.exp (Y n) +
          Real.exp (X n) * Real.exp (-Y n) +
          Real.exp (-X n) * Real.exp (Y n) +
          Real.exp (-X n) * Real.exp (-Y n) := by ring
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
  have hpp : Summable (fun n => (pμf n).toReal * Real.exp (X n + Y n)) := by
    simpa [pμf, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      (hexpSummable 1 1)
  have hpm : Summable (fun n => (pμf n).toReal * Real.exp (X n - Y n)) := by
    simpa [pμf, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), sub_eq_add_neg] using
      (hexpSummable 1 (-1))
  have hmp : Summable (fun n => (pμf n).toReal * Real.exp (-X n + Y n)) := by
    simpa [pμf, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_one] using
      (hexpSummable (-1) 1)
  have hmm : Summable (fun n => (pμf n).toReal * Real.exp (-X n - Y n)) := by
    simpa [pμf, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), sub_eq_add_neg] using
      (hexpSummable (-1) (-1))
  have hdomSummable : Summable (fun n => (pμf n).toReal *
      (Real.exp (X n + Y n) + Real.exp (X n - Y n) +
        Real.exp (-X n + Y n) + Real.exp (-X n - Y n))) := by
    simpa [mul_add, add_assoc] using hpp.add (hpm.add (hmp.add hmm))
  have hweight : Summable (fun n => (pμf n).toReal * ‖X n * Y n‖) := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _))
      (fun n => mul_le_mul_of_nonneg_left (hdom n) ENNReal.toReal_nonneg)
    exact hdomSummable
  have hInt := pmf_integrable_of_summable_norm (p := pμf)
    (f := fun n => X n * Y n) hweight
  simpa [pμf, A, X, Y] using hInt

/--
The zero-current Wilson partition is exactly the normalizer of the
tree-gauge chord law.
-/
theorem dualWilsonPartition_zero_eq_dualBaseNormalizer
    {B : Cubical.Box 4} (β : ℝ) (hβ : 0 < β) :
    dualWilsonPartition (B := B) β 0 =
      dualBaseNormalizer (sourceChordMatrix (B := B) β) := by
  let hzero : Cubical.homogeneousSupport (0 : Cubical.Chain 4 B) 2 := by
    intro c hc
    simp at hc
  let e := (chordGaugeClassEquiv (B := B)).trans
    (primal_sourceWilsonModesEquiv (0 : Cubical.Chain 4 B) hzero)
  have hstar (n : (sourceRootedTree B).Chord → ℤ) :
    integerStarMap (plaquetteModeChain (e n).1) = (chordGaugeClass n).1 := by
    have he : e n = sourceExactFieldToWilsonMode
        (0 : Cubical.Chain 4 B) hzero (chordGaugeClass n) := by
      change sourceExactFieldToWilsonMode (0 : Cubical.Chain 4 B) hzero
        (chordGaugeClassEquiv n) = _
      rw [chordGaugeClassEquiv_apply]
    rw [he]
    simpa only [map_zero, zero_add] using sourceExactFieldToWilsonMode_star
      (0 : Cubical.Chain 4 B) hzero (chordGaugeClass n)
  have hweight (n : (sourceRootedTree B).Chord → ℤ) :
      dualGaussianProduct β (e n).1 =
        dualBaseWeight (sourceChordMatrix (B := B) β) n := by
    calc
      dualGaussianProduct β (e n).1 =
          sourceDualGaugeClassWeight β (chordGaugeClass n) := by
            rw [dualGaussianProduct_eq_integerDualNormSq, hstar]
            rfl
      _ = dualPrimalWeight (sourceChordMatrix (B := B) β)
          (fun _ => 0) 0 n := chordGaugeClass_weight hβ (fun _ => 0) n
      _ = dualBaseWeight (sourceChordMatrix (B := B) β) n := by
            rfl
  calc
    dualWilsonPartition (B := B) β 0 =
        ∑' m : SourceWilsonModes (0 : Cubical.Chain 4 B),
          dualGaussianProduct β m.1 :=
      dualWilsonPartition_eq_sourceWilsonModes_sum β 0
    _ = ∑' n : (sourceRootedTree B).Chord → ℤ,
        dualBaseWeight (sourceChordMatrix (B := B) β) n := by
      rw [← Equiv.tsum_eq e (fun m => dualGaussianProduct β m.1)]
      apply tsum_congr
      exact hweight
    _ = dualBaseNormalizer (sourceChordMatrix (B := B) β) := rfl

/--
The complementary-cell map is the cubical star; C4
then identifies the `{2,3}` primal field strength with the `{0,1}` dual
curvature, with one coordinate sign at each insertion.
-/
theorem finiteDualCurvatureCorrelation_eq_chordLaw
    {B : Cubical.Box 4} (β : ℝ) (hβ : 0 < β)
    (p q : PrimalPlaquettes B) :
    finiteDualCurvatureCorrelation β p q =
      ((∫ n : (sourceRootedTree B).Chord → ℤ,
        (integerChordCurvature n (primalDualCellOfPrimal p) : ℝ) *
          (integerChordCurvature n (primalDualCellOfPrimal q) : ℝ)
        ∂(dualChordPMF (sourceChordMatrix (B := B) β)
          (scaledChordMatrix_posDef _ _ hβ)).toMeasure : ℝ) : ℂ) := by
  classical
  let A := sourceChordMatrix (B := B) β
  let hA : A.PosDef := scaledChordMatrix_posDef _ _ hβ
  let μ := dualChordPMF A hA
  let hzero : Cubical.homogeneousSupport (0 : Cubical.Chain 4 B) 2 := by
    intro c hc
    simp at hc
  let e := (chordGaugeClassEquiv (B := B)).trans
    (primal_sourceWilsonModesEquiv (0 : Cubical.Chain 4 B) hzero)
  have hstar (n : (sourceRootedTree B).Chord → ℤ) :
      integerStarMap (plaquetteModeChain (e n).1) = (chordGaugeClass n).1 := by
    have he : e n = sourceExactFieldToWilsonMode
        (0 : Cubical.Chain 4 B) hzero (chordGaugeClass n) := by
      change sourceExactFieldToWilsonMode (0 : Cubical.Chain 4 B) hzero
        (chordGaugeClassEquiv n) = _
      rw [chordGaugeClassEquiv_apply]
    rw [he]
    simpa only [map_zero, zero_add] using sourceExactFieldToWilsonMode_star
      (0 : Cubical.Chain 4 B) hzero (chordGaugeClass n)
  have hweight (n : (sourceRootedTree B).Chord → ℤ) :
      dualGaussianProduct β (e n).1 = dualBaseWeight A n := by
    calc
      dualGaussianProduct β (e n).1 =
          sourceDualGaugeClassWeight β (chordGaugeClass n) := by
            rw [dualGaussianProduct_eq_integerDualNormSq, hstar]
            rfl
      _ = dualPrimalWeight A (fun _ => 0) 0 n :=
        chordGaugeClass_weight hβ (fun _ => 0) n
      _ = dualBaseWeight A n := rfl
  have hmodeCurvature (n : (sourceRootedTree B).Chord → ℤ)
      (r : PrimalPlaquettes B) :
      ((e n).1 r : ℝ) =
        (integerChordCurvature n (primalDualCellOfPrimal r) : ℝ) := by
    have heval := congrArg (fun z : DualIntegerChain B =>
      z (Cubical.primalDualCellEquiv r.1)) (hstar n)
    rw [primal_integerStarMap_plaquetteMode_apply] at heval
    have hcurv := primal_integerChordCurvature_eq_gaugeClass n
      (primalDualCellOfPrimal r)
    calc
      ((e n).1 r : ℝ) = ((chordGaugeClass n).1
          (Cubical.primalDualCellEquiv r.1) : ℝ) := by exact_mod_cast heval
      _ = (integerChordCurvature n (primalDualCellOfPrimal r) : ℝ) := by
        exact_mod_cast hcurv.symm
  let X (n : (sourceRootedTree B).Chord → ℤ) : ℝ :=
    integerChordCurvature n (primalDualCellOfPrimal p)
  let Y (n : (sourceRootedTree B).Chord → ℤ) : ℝ :=
    integerChordCurvature n (primalDualCellOfPrimal q)
  have hInt : Integrable (fun n => X n * Y n) μ.toMeasure := by
    simpa [X, Y, μ, A, hA] using
      primal_dualChordPMF_curvatureProduct_integrable β hβ
        (primalDualCellOfPrimal p) (primalDualCellOfPrimal q)
  have hpmfNorm := pmf_summable_norm_of_integrable hInt
  have hZpos : 0 < dualBaseNormalizer A := dualBaseNormalizer_pos A hA
  have hweightNorm : Summable (fun n =>
      dualBaseWeight A n * ‖X n * Y n‖) := by
    have hscale := hpmfNorm.mul_right (dualBaseNormalizer A)
    refine hscale.congr ?_
    intro n
    rw [dualChordPMF_apply_toReal A hA n]
    have hw : 0 < dualBaseWeight A n := dualBaseWeight_pos A n
    field_simp
  have hweightSum : Summable (fun n => dualBaseWeight A n * (X n * Y n)) := by
    apply Summable.of_norm
    refine hweightNorm.congr ?_
    intro n
    calc
      dualBaseWeight A n * ‖X n * Y n‖ =
          ‖dualBaseWeight A n‖ * ‖X n * Y n‖ := by
            rw [Real.norm_of_nonneg (dualBaseWeight_pos A n).le]
      _ = ‖dualBaseWeight A n * (X n * Y n)‖ :=
        (norm_mul _ _).symm
  have hIntTsum :
      (∫ n, X n * Y n ∂μ.toMeasure) =
        ∑' n, (μ n).toReal * (X n * Y n) := by
    simpa [smul_eq_mul] using PMF.integral_eq_tsum μ (fun n => X n * Y n) hInt
  have hratio :
      (∑' n, dualBaseWeight A n * (X n * Y n)) /
          dualBaseNormalizer A = ∫ n, X n * Y n ∂μ.toMeasure := by
    calc
      _ = ∑' n, (dualBaseWeight A n * (X n * Y n)) /
          dualBaseNormalizer A := by rw [← tsum_div_const]
      _ = ∑' n, (μ n).toReal * (X n * Y n) := by
        apply tsum_congr
        intro n
        rw [dualChordPMF_apply_toReal A hA n]
        field_simp
      _ = _ := hIntTsum.symm
  let P : Set (PrimalPlaquettes B → ℤ) :=
    {m | plaquetteModeDivergence m = 0}
  have hzeroFreq : primalSheetLoopFrequency (0 : Cubical.Chain 4 B) = 0 := by
    funext l
    simp [primalSheetLoopFrequency]
  have hmodeNum :
      (∑' m : PrimalPlaquettes B → ℤ,
        ((m p : ℝ) * (m q : ℝ) : ℂ) *
          (dualWilsonTerm β (0 : Cubical.Chain 4 B) m : ℂ)) =
        (↑(∑' n, dualBaseWeight A n * (X n * Y n)) : ℂ) := by
    have hfilter (m : PrimalPlaquettes B → ℤ) :
        ((m p : ℝ) * (m q : ℝ) : ℂ) *
            (dualWilsonTerm β (0 : Cubical.Chain 4 B) m : ℂ) =
          P.indicator (fun z => ((z p : ℝ) * (z q : ℝ) : ℂ) *
            (dualGaussianProduct β z : ℂ)) m := by
      by_cases hm : m ∈ P
      · have hvalid : plaquetteModeDivergence m =
            primalSheetLoopFrequency (0 : Cubical.Chain 4 B) := by
          exact hm.trans hzeroFreq.symm
        rw [Set.indicator_of_mem hm]
        simp [dualWilsonTerm, hvalid]
      · have hinvalid : plaquetteModeDivergence m ≠
            primalSheetLoopFrequency (0 : Cubical.Chain 4 B) := by
          intro h
          apply hm
          change plaquetteModeDivergence m = 0
          rw [hzeroFreq] at h
          exact h
        rw [Set.indicator_of_notMem hm]
        simp [dualWilsonTerm, hinvalid]
    calc
      _ = ∑' m : PrimalPlaquettes B → ℤ,
          P.indicator (fun z => ((z p : ℝ) * (z q : ℝ) : ℂ) *
            (dualGaussianProduct β z : ℂ)) m := by
              apply tsum_congr
              exact hfilter
      _ = ∑' m : SourceWilsonModes (0 : Cubical.Chain 4 B),
          ((m.1 p : ℝ) * (m.1 q : ℝ) : ℂ) *
            (dualGaussianProduct β m.1 : ℂ) := by
              symm
              change (∑' m : {m : PrimalPlaquettes B → ℤ // m ∈ P}, _ ) = _
              exact tsum_subtype P (fun m =>
                ((m p : ℝ) * (m q : ℝ) : ℂ) *
                  (dualGaussianProduct β m : ℂ))
      _ = ∑' n : (sourceRootedTree B).Chord → ℤ,
          ((((e n).1 p : ℝ) * ((e n).1 q : ℝ) : ℝ) : ℂ) *
            (dualGaussianProduct β (e n).1 : ℂ) := by
              calc
                _ = ∑' n : (sourceRootedTree B).Chord → ℤ,
                    (((((e n).1 p : ℝ) : ℂ) *
                      (((e n).1 q : ℝ) : ℂ)) *
                      (dualGaussianProduct β (e n).1 : ℂ)) :=
                      (Equiv.tsum_eq e (fun m : SourceWilsonModes
                        (0 : Cubical.Chain 4 B) =>
                          ((m.1 p : ℝ) * (m.1 q : ℝ) : ℂ) *
                            (dualGaussianProduct β m.1 : ℂ))).symm
                _ = _ := by
                      apply tsum_congr
                      intro n
                      push_cast
                      ring
      _ = (↑(∑' n, dualBaseWeight A n * (X n * Y n)) : ℂ) := by
              have hterm (n : (sourceRootedTree B).Chord → ℤ) :
                  ((((e n).1 p : ℝ) * ((e n).1 q : ℝ) : ℝ) : ℂ) *
                      (dualGaussianProduct β (e n).1 : ℂ) =
                    ((((e n).1 p : ℝ) * ((e n).1 q : ℝ) *
                      dualGaussianProduct β (e n).1 : ℝ) : ℂ) := by
                push_cast
                ring
              calc
                _ = ∑' n, ((((e n).1 p : ℝ) * ((e n).1 q : ℝ) *
                    dualGaussianProduct β (e n).1 : ℝ) : ℂ) := by
                      apply tsum_congr
                      intro n
                      exact hterm n
                _ = (↑(∑' n, ((e n).1 p : ℝ) * ((e n).1 q : ℝ) *
                    dualGaussianProduct β (e n).1) : ℂ) :=
                      (Complex.ofReal_tsum (fun n =>
                        ((e n).1 p : ℝ) * ((e n).1 q : ℝ) *
                          dualGaussianProduct β (e n).1)).symm
                _ = (↑(∑' n, dualBaseWeight A n * (X n * Y n)) : ℂ) := by
                      apply congrArg Complex.ofReal
                      apply tsum_congr
                      intro n
                      rw [hweight n, hmodeCurvature n p, hmodeCurvature n q]
                      simp [X, Y]
                      ring
  have hnumCast :
      (∑' m : PrimalPlaquettes B → ℤ,
        ((m p : ℝ) * (m q : ℝ) : ℂ) *
          (dualWilsonTerm β (0 : Cubical.Chain 4 B) m : ℂ)) =
        (↑(∑' n, dualBaseWeight A n * (X n * Y n)) : ℂ) := hmodeNum
  have hden : (dualWilsonPartition (B := B) β (0 : Cubical.Chain 4 B) : ℂ) =
      (dualBaseNormalizer A : ℂ) := by
    exact_mod_cast (dualWilsonPartition_zero_eq_dualBaseNormalizer β hβ)
  unfold finiteDualCurvatureCorrelation
  rw [hnumCast, hden]
  rw [← Complex.ofReal_div]
  exact congrArg Complex.ofReal hratio

/-- The primal face whose C4 dual is a given finite source dual plaquette.
For a dual `{0,1}` plaquette this has primal axes `{2,3}`. -/
noncomputable def primalPlaquetteOfDual {B : Cubical.Box 4}
    (q : SourceDualTwoCells B) : PrimalPlaquettes B := by
  refine ⟨Cubical.primalDualCellEquiv.symm q.1, ?_⟩
  have h := Cubical.star_complementary_degree
    (Cubical.primalDualCellEquiv.symm q.1)
  have hstar : Cubical.primalDualCellEquiv
      (Cubical.primalDualCellEquiv.symm q.1) = q.1 :=
    Equiv.apply_symm_apply Cubical.primalDualCellEquiv q.1
  rw [hstar, q.2] at h
  omega

noncomputable def primalPlaquetteOfGlobal (N : ℕ)
    (p : GlobalIntegerPlaquette) (hp : PlaquetteInCube N p) :
    PrimalPlaquettes (cube N) :=
  primalPlaquetteOfDual (cubePlaquettePreimage N p hp)

theorem primalPlaquetteOfGlobal_dual (N : ℕ)
    (p : GlobalIntegerPlaquette) (hp : PlaquetteInCube N p) :
    primalDualCellOfPrimal (primalPlaquetteOfGlobal N p hp) =
      cubePlaquettePreimage N p hp := by
  apply Subtype.ext
  change Cubical.primalDualCellEquiv
      (Cubical.primalDualCellEquiv.symm (cubePlaquettePreimage N p hp).1) =
    (cubePlaquettePreimage N p hp).1
  exact Equiv.apply_symm_apply Cubical.primalDualCellEquiv _

/-- The finite-volume field-strength identity is exactly the finite cube
curvature expectation used by the cube exhaustion.  The two C4 orientation
signs occur once at each endpoint and multiply to `+1`. -/
theorem primalFieldStrengthCorrelation_eq_cubeCurvaturePMF
    (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (x y : LatticePoint) (hxy : x ≠ y)
    (hP : ∀ p ∈ spectralPairPlaquettes x y, PlaquetteInCube N p) :
    primalFieldStrengthCorrelation β
        (primalPlaquetteOfGlobal N (spectralPlaquetteAt x)
          (hP (spectralPlaquetteAt x) (by simp [spectralPairPlaquettes])) )
        (primalPlaquetteOfGlobal N (spectralPlaquetteAt y)
          (hP (spectralPlaquetteAt y) (by simp [spectralPairPlaquettes]))) =
      (↑(∫ ω, spectralPairProduct x y ω ∂
        (cubeCurvaturePMFTotal N β hβ (spectralPairPlaquettes x y)).toMeasure) : ℂ) := by
  classical
  let P := spectralPairPlaquettes x y
  let gx := spectralPlaquetteAt x
  let gy := spectralPlaquetteAt y
  let hx : PlaquetteInCube N gx := hP gx (by simp [gx, spectralPairPlaquettes])
  let hy : PlaquetteInCube N gy := hP gy (by simp [gy, spectralPairPlaquettes])
  let qx : SourceDualTwoCells (cube N) := cubePlaquettePreimage N gx hx
  let qy : SourceDualTwoCells (cube N) := cubePlaquettePreimage N gy hy
  let px : PrimalPlaquettes (cube N) := primalPlaquetteOfGlobal N gx hx
  let py : PrimalPlaquettes (cube N) := primalPlaquetteOfGlobal N gy hy
  let μ : PMF ((sourceRootedTree (cube N)).Chord → ℤ) :=
    cubeDualChordPMF N β hβ
  let c : ((sourceRootedTree (cube N)).Chord → ℤ) → P → ℤ :=
    cubeCurvatureMap N P hP
  let ix : P := spectralPairIndex x y x (by simp [spectralPairPlaquettes])
  let iy : P := spectralPairIndex x y y (by simp [spectralPairPlaquettes])
  have hdualx : primalDualCellOfPrimal px = qx := by
    dsimp [px, qx]
    exact primalPlaquetteOfGlobal_dual N gx hx
  have hdualy : primalDualCellOfPrimal py = qy := by
    dsimp [py, qy]
    exact primalPlaquetteOfGlobal_dual N gy hy
  have hcurvx (n : (sourceRootedTree (cube N)).Chord → ℤ) :
      c n ix = integerChordCurvature n qx := by
    change cubeIntegerCurvatureAt N n gx
      (hP gx (by simp [gx, spectralPairPlaquettes])) = _
    dsimp [cubeIntegerCurvatureAt, qx, hx]
  have hcurvy (n : (sourceRootedTree (cube N)).Chord → ℤ) :
      c n iy = integerChordCurvature n qy := by
    change cubeIntegerCurvatureAt N n gy
      (hP gy (by simp [gy, spectralPairPlaquettes])) = _
    dsimp [cubeIntegerCurvatureAt, qy, hy]
  have hcomp (n : (sourceRootedTree (cube N)).Chord → ℤ) :
      spectralPairProduct x y (c n) =
        (integerChordCurvature n qx : ℝ) *
          (integerChordCurvature n qy : ℝ) := by
    dsimp [spectralPairProduct, ix, iy]
    rw [hcurvx, hcurvy]
  have hmeasC : Measurable c := by
    fun_prop (disch := aesop) [cubeCurvatureMap, cubeIntegerCurvatureAt,
      integerChordCurvature]
  have hmeasPair : Measurable (spectralPairProduct x y) := by fun_prop
  have hIntChord := primal_dualChordPMF_curvatureProduct_integrable β hβ qx qy
  have hIntComp : Integrable (fun n => spectralPairProduct x y (c n)) μ.toMeasure := by
    apply hIntChord.congr (ae_of_all _ fun n => ?_)
    rw [hcomp]
  have hsumComp := pmf_summable_norm_of_integrable hIntComp
  have hmapIntegral := pmf_map_integral μ c (spectralPairProduct x y)
    hmeasC hmeasPair hsumComp
  have hlaw : cubeCurvaturePMFTotal N β hβ P = PMF.map c μ := by
    unfold cubeCurvaturePMFTotal
    rw [dite_eq_left hP]
    rfl
  have hreal :
      ∫ ω, spectralPairProduct x y ω ∂(cubeCurvaturePMFTotal N β hβ P).toMeasure =
        ∫ n, (integerChordCurvature n qx : ℝ) *
          (integerChordCurvature n qy : ℝ) ∂μ.toMeasure := by
    rw [hlaw]
    calc
      ∫ ω, spectralPairProduct x y ω ∂(PMF.map c μ).toMeasure =
          ∫ n, spectralPairProduct x y (c n) ∂μ.toMeasure := hmapIntegral
      _ = _ := by
        apply integral_congr_ae
        exact ae_of_all _ hcomp
  have hfinite := finiteDualCurvatureCorrelation_eq_chordLaw β hβ px py
  have hfinite' : finiteDualCurvatureCorrelation β px py =
      (↑(∫ n, (integerChordCurvature n qx : ℝ) *
        (integerChordCurvature n qy : ℝ) ∂μ.toMeasure) : ℂ) := by
    simpa [μ, cubeDualChordPMF, hdualx, hdualy] using hfinite
  calc
    primalFieldStrengthCorrelation β px py = finiteDualCurvatureCorrelation β px py :=
      primalFieldStrengthCorrelation_eq_dual β hβ px py (by
        intro hp
        have hq : qx = qy := by
          rw [← hdualx, ← hdualy]
          exact congrArg primalDualCellOfPrimal hp
        have hglobal : gx = gy := by
          have hEq := congrArg (cubePlaquetteEmbedding N) hq
          rw [cubePlaquetteEmbedding_preimage N gx hx,
            cubePlaquetteEmbedding_preimage N gy hy] at hEq
          exact Subtype.ext hEq
        exact hxy (spectralPlaquetteAt_injective hglobal))
    _ = (↑(∫ n, (integerChordCurvature n qx : ℝ) *
          (integerChordCurvature n qy : ℝ) ∂μ.toMeasure) : ℂ) := hfinite'
    _ = (↑(∫ ω, spectralPairProduct x y ω ∂
          (cubeCurvaturePMFTotal N β hβ P).toMeasure) : ℂ) := by
        rw [hreal]

/-- Total finite cube correlation on the fixed global plaquette pair.  Below
the containment threshold this is only the harmless zero extension in
`cubeCurvaturePMFTotal`; above it, the finite primal identity theorem
identifies it with the Villain field-strength correlation on `cube N`. -/
noncomputable def primalCubePrimalCorrelation
    (N : ℕ) (β : ℝ) (hβ : 0 < β) (x y : LatticePoint) : ℝ :=
  ∫ ω, spectralPairProduct x y ω ∂
    (cubeCurvaturePMFTotal N β hβ (spectralPairPlaquettes x y)).toMeasure

theorem primalCubePrimalCorrelation_eq_primalFieldStrength
    (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (x y : LatticePoint) (hxy : x ≠ y)
    (hP : ∀ p ∈ spectralPairPlaquettes x y, PlaquetteInCube N p) :
    primalCubePrimalCorrelation N β hβ x y =
      (primalFieldStrengthCorrelation β
        (primalPlaquetteOfGlobal N (spectralPlaquetteAt x)
          (hP (spectralPlaquetteAt x) (by simp [spectralPairPlaquettes])))
        (primalPlaquetteOfGlobal N (spectralPlaquetteAt y)
          (hP (spectralPlaquetteAt y) (by simp [spectralPairPlaquettes])))).re := by
  unfold primalCubePrimalCorrelation
  rw [primalFieldStrengthCorrelation_eq_cubeCurvaturePMF N β hβ x y hxy hP]
  simp


/-- Pointwise convergence of countable probability masses passes signed
expectations to the limit when the sequence is tight and has a uniform second
moment. The positive and negative parts are handled separately. -/
theorem pmf_integral_tendsto_of_tight_secondMoment
    {α : Type*} [Countable α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (pn : ℕ → PMF α) (p : PMF α) (f : α → ℝ) (C : ℝ)
    (hpoint : ∀ x, Tendsto (fun n => (pn n x).toReal) atTop
      (𝓝 ((p x).toReal)))
    (htight : ∀ ε : ℝ, 0 < ε → ∃ T : Finset α, ∀ n,
      1 - ε ≤ ∑ x ∈ T, (pn n x).toReal)
    (hsq : ∀ n, Summable (fun x => (pn n x).toReal * (f x) ^ 2))
    (hsqBound : ∀ n, ∑' x, (pn n x).toReal * (f x) ^ 2 ≤ C)
    (hposInt : ∀ n, Integrable (fun x => max (f x) 0) (pn n).toMeasure)
    (hnegInt : ∀ n, Integrable (fun x => max (-f x) 0) (pn n).toMeasure)
    (hposIntLim : Integrable (fun x => max (f x) 0) p.toMeasure)
    (hnegIntLim : Integrable (fun x => max (-f x) 0) p.toMeasure) :
    Tendsto (fun n => ∫ x, f x ∂(pn n).toMeasure) atTop
      (𝓝 (∫ x, f x ∂p.toMeasure)) := by
  classical
  have hposSq (x : α) : (max (f x) 0) ^ 2 ≤ (f x) ^ 2 := by
    have hnonneg : 0 ≤ max (f x) 0 := le_max_right _ _
    have hle : max (f x) 0 ≤ |f x| := max_le_iff.mpr
      ⟨le_abs_self (f x), abs_nonneg _⟩
    nlinarith [sq_abs (f x)]
  have hnegSq (x : α) : (max (-f x) 0) ^ 2 ≤ (f x) ^ 2 := by
    have hnonneg : 0 ≤ max (-f x) 0 := le_max_right _ _
    have hle : max (-f x) 0 ≤ |f x| := max_le_iff.mpr
      ⟨by simpa [abs_neg] using (le_abs_self (-f x)), abs_nonneg _⟩
    nlinarith [sq_abs (f x)]
  have hsqPos (n : ℕ) :
      Summable (fun x => (pn n x).toReal * (max (f x) 0) ^ 2) := by
    apply Summable.of_nonneg_of_le
      (fun x => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
      (fun x => mul_le_mul_of_nonneg_left (hposSq x) ENNReal.toReal_nonneg)
    exact hsq n
  have hsqNeg (n : ℕ) :
      Summable (fun x => (pn n x).toReal * (max (-f x) 0) ^ 2) := by
    apply Summable.of_nonneg_of_le
      (fun x => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
      (fun x => mul_le_mul_of_nonneg_left (hnegSq x) ENNReal.toReal_nonneg)
    exact hsq n
  have hsqPosBound (n : ℕ) :
      ∑' x, (pn n x).toReal * (max (f x) 0) ^ 2 ≤ C := by
    exact le_trans (Summable.tsum_le_tsum (fun x =>
      mul_le_mul_of_nonneg_left (hposSq x) ENNReal.toReal_nonneg)
      (hsqPos n) (hsq n)) (hsqBound n)
  have hsqNegBound (n : ℕ) :
      ∑' x, (pn n x).toReal * (max (-f x) 0) ^ 2 ≤ C := by
    exact le_trans (Summable.tsum_le_tsum (fun x =>
      mul_le_mul_of_nonneg_left (hnegSq x) ENNReal.toReal_nonneg)
      (hsqNeg n) (hsq n)) (hsqBound n)
  have hposConv := FroehlichSpencer.FS82.Infinite.pmf_weighted_tsum_tendsto_of_tight_secondMoment
    pn p (fun x => max (f x) 0) C hpoint htight
      (fun x => le_max_right _ _) hsqPos hsqPosBound
  have hnegConv := FroehlichSpencer.FS82.Infinite.pmf_weighted_tsum_tendsto_of_tight_secondMoment
    pn p (fun x => max (-f x) 0) C hpoint htight
      (fun x => le_max_right _ _) hsqNeg hsqNegBound
  have hposSeq (n : ℕ) :
      ∫ x, max (f x) 0 ∂(pn n).toMeasure =
        ∑' x, (pn n x).toReal * max (f x) 0 := by
    simpa [smul_eq_mul] using PMF.integral_eq_tsum (pn n)
      (fun x => max (f x) 0) (hposInt n)
  have hnegSeq (n : ℕ) :
      ∫ x, max (-f x) 0 ∂(pn n).toMeasure =
        ∑' x, (pn n x).toReal * max (-f x) 0 := by
    simpa [smul_eq_mul] using PMF.integral_eq_tsum (pn n)
      (fun x => max (-f x) 0) (hnegInt n)
  have hposLim :
      ∫ x, max (f x) 0 ∂p.toMeasure =
        ∑' x, (p x).toReal * max (f x) 0 := by
    simpa [smul_eq_mul] using PMF.integral_eq_tsum p
      (fun x => max (f x) 0) hposIntLim
  have hnegLim :
      ∫ x, max (-f x) 0 ∂p.toMeasure =
        ∑' x, (p x).toReal * max (-f x) 0 := by
    simpa [smul_eq_mul] using PMF.integral_eq_tsum p
      (fun x => max (-f x) 0) hnegIntLim
  have hposIntegral : Tendsto
      (fun n => ∫ x, max (f x) 0 ∂(pn n).toMeasure) atTop
      (𝓝 (∫ x, max (f x) 0 ∂p.toMeasure)) := by
    have hseq := hposConv.congr'
      (Filter.Eventually.of_forall fun n => (hposSeq n).symm)
    rw [← hposLim] at hseq
    exact hseq
  have hnegIntegral : Tendsto
      (fun n => ∫ x, max (-f x) 0 ∂(pn n).toMeasure) atTop
      (𝓝 (∫ x, max (-f x) 0 ∂p.toMeasure)) := by
    have hseq := hnegConv.congr'
      (Filter.Eventually.of_forall fun n => (hnegSeq n).symm)
    rw [← hnegLim] at hseq
    exact hseq
  have hsplit (x : α) : f x = max (f x) 0 - max (-f x) 0 := by
    by_cases h : 0 ≤ f x
    · simp [max_eq_left h, max_eq_right (by linarith : -f x ≤ 0)]
    · have h' : f x ≤ 0 := le_of_not_ge h
      simp [max_eq_right h', max_eq_left (by linarith : 0 ≤ -f x)]
  have hseqIntegral (n : ℕ) :
      ∫ x, f x ∂(pn n).toMeasure =
        (∫ x, max (f x) 0 ∂(pn n).toMeasure) -
          ∫ x, max (-f x) 0 ∂(pn n).toMeasure := by
    calc
      _ = ∫ x, (max (f x) 0 - max (-f x) 0) ∂(pn n).toMeasure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => hsplit x
      _ = _ := integral_sub (hposInt n) (hnegInt n)
  have hlimIntegral :
      ∫ x, f x ∂p.toMeasure =
        (∫ x, max (f x) 0 ∂p.toMeasure) -
          ∫ x, max (-f x) 0 ∂p.toMeasure := by
    calc
      _ = ∫ x, (max (f x) 0 - max (-f x) 0) ∂p.toMeasure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => hsplit x
      _ = _ := integral_sub hposIntLim hnegIntLim
  have hsub := hposIntegral.sub hnegIntegral
  have hsub' : Tendsto
      (fun n => (∫ x, max (f x) 0 ∂(pn n).toMeasure) -
        ∫ x, max (-f x) 0 ∂(pn n).toMeasure) atTop
      (𝓝 ((∫ x, max (f x) 0 ∂p.toMeasure) -
        ∫ x, max (-f x) 0 ∂p.toMeasure)) := hsub
  simpa only [hseqIntegral, hlimIntegral] using hsub'

/-- Every two-coordinate product is integrable under a cube projective limit.
Its finite approximants have uniformly bounded second moments by the
coordinate fourth-moment estimate. -/
private theorem primal_cubeLimitPair_integrable
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (x y : LatticePoint) :
    Integrable (spectralPairProduct x y)
      (L.law (spectralPairPlaquettes x y)).toMeasure := by
  classical
  let P := spectralPairPlaquettes x y
  let p : PMF (P → ℤ) := L.law P
  let pn : ℕ → PMF (P → ℤ) := fun k =>
    cubeCurvaturePMFTotal (L.subsequence k) β (rootBeta_pos hβ) P
  let ix : P := spectralPairIndex x y x (by simp [spectralPairPlaquettes])
  let iy : P := spectralPairIndex x y y (by simp [spectralPairPlaquettes])
  let X : (P → ℤ) → ℝ := fun ω => (ω ix : ℝ)
  let Y : (P → ℤ) → ℝ := fun ω => (ω iy : ℝ)
  let f : (P → ℤ) → ℝ := fun ω => X ω * Y ω
  let C : ℝ := 512 * Real.exp (β / 2)
  have hpoint : ∀ z, Tendsto (fun k => (pn k z).toReal) atTop
      (𝓝 ((p z).toReal)) := by
    intro z
    exact L.pointwise P z
  have hsq (k : ℕ) : Summable (fun z => (pn k z).toReal * (f z) ^ 2) := by
    have hX4 := primal_cubeCoordinate_fourthMoment_bound
      (L.subsequence k) β (rootBeta_pos hβ) P ix
    have hY4 := primal_cubeCoordinate_fourthMoment_bound
      (L.subsequence k) β (rootBeta_pos hβ) P iy
    have hprod := primal_integrable_product_square_of_fourth X Y
      (by fun_prop) (by fun_prop) hX4.1 hY4.1
    have hnorm := pmf_summable_norm_of_integrable (p := pn k)
      (f := fun z => (f z) ^ 2) (by simpa [pn] using hprod)
    refine hnorm.congr ?_
    intro z
    rw [Real.norm_of_nonneg (sq_nonneg (f z))]
  have hsqBound (k : ℕ) :
      ∑' z, (pn k z).toReal * (f z) ^ 2 ≤ C := by
    have hX4 := primal_cubeCoordinate_fourthMoment_bound
      (L.subsequence k) β (rootBeta_pos hβ) P ix
    have hY4 := primal_cubeCoordinate_fourthMoment_bound
      (L.subsequence k) β (rootBeta_pos hβ) P iy
    have hprod := primal_integrable_product_square_of_fourth X Y
      (by fun_prop) (by fun_prop) hX4.1 hY4.1
    have hdom : Integrable
        (fun z => (1 / 2 : ℝ) * (X z ^ 4 + Y z ^ 4)) (pn k).toMeasure :=
      (hX4.1.add hY4.1).const_mul (1 / 2)
    have hpointwise (z : P → ℤ) :
        (f z) ^ 2 ≤ (1 / 2 : ℝ) * (X z ^ 4 + Y z ^ 4) := by
      dsimp [f]
      nlinarith [sq_nonneg (X z ^ 2 - Y z ^ 2)]
    have hinter : ∫ z, (f z) ^ 2 ∂(pn k).toMeasure ≤
        ∫ z, (1 / 2 : ℝ) * (X z ^ 4 + Y z ^ 4) ∂(pn k).toMeasure :=
      MeasureTheory.integral_mono hprod hdom hpointwise
    have hdomInt : ∫ z, (1 / 2 : ℝ) * (X z ^ 4 + Y z ^ 4)
        ∂(pn k).toMeasure =
        (1 / 2 : ℝ) * ((∫ z, X z ^ 4 ∂(pn k).toMeasure) +
          ∫ z, Y z ^ 4 ∂(pn k).toMeasure) := by
      rw [integral_const_mul, integral_add hX4.1 hY4.1]
    have hsum : ∫ z, (f z) ^ 2 ∂(pn k).toMeasure =
        ∑' z, (pn k z).toReal * (f z) ^ 2 := by
      simpa [smul_eq_mul] using PMF.integral_eq_tsum (pn k)
        (fun z => (f z) ^ 2) hprod
    calc
      _ = ∫ z, (f z) ^ 2 ∂(pn k).toMeasure := hsum.symm
      _ ≤ ∫ z, (1 / 2 : ℝ) * (X z ^ 4 + Y z ^ 4) ∂(pn k).toMeasure := hinter
      _ = (1 / 2 : ℝ) * ((∫ z, X z ^ 4 ∂(pn k).toMeasure) +
          ∫ z, Y z ^ 4 ∂(pn k).toMeasure) := hdomInt
      _ ≤ C := by dsimp [C]; nlinarith [hX4.2, hY4.2]
  have hlimSq := pmf_secondMoment_bound_of_pointwise
    pn p f C hpoint hsq hsqBound
  have hIntLim : Integrable f p.toMeasure :=
    primal_pmf_integrable_of_secondMoment p f hlimSq.1
  have hfg (ω : P → ℤ) : f ω = spectralPairProduct x y ω := by
    simp [f, X, Y, ix, iy, spectralPairProduct]
  simpa [p, P] using hIntLim.congr (ae_of_all _ hfg)

/-- Pair expectations converge along the selected cube subsequence.  The
coordinate exponential bound supplies uniform fourth moments; Cauchy–Schwarz
then gives the second-moment control needed to pass signed products through
the projective limit. -/
theorem primal_cubeLimitPairCorrelation_tendsto
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (x y : LatticePoint) :
    Tendsto
      (fun k => ∫ ω, spectralPairProduct x y ω ∂
        (cubeCurvaturePMFTotal (L.subsequence k) β (rootBeta_pos hβ)
          (spectralPairPlaquettes x y)).toMeasure)
      atTop
      (𝓝 (∫ ω, spectralPairProduct x y ω ∂
        (L.law (spectralPairPlaquettes x y)).toMeasure)) := by
  classical
  let P := spectralPairPlaquettes x y
  let p : PMF (P → ℤ) := L.law P
  let pn : ℕ → PMF (P → ℤ) := fun k =>
    cubeCurvaturePMFTotal (L.subsequence k) β (rootBeta_pos hβ) P
  let ix : P := spectralPairIndex x y x (by simp [spectralPairPlaquettes])
  let iy : P := spectralPairIndex x y y (by simp [spectralPairPlaquettes])
  let X : (P → ℤ) → ℝ := fun ω => (ω ix : ℝ)
  let Y : (P → ℤ) → ℝ := fun ω => (ω iy : ℝ)
  let f : (P → ℤ) → ℝ := fun ω => X ω * Y ω
  let C : ℝ := 512 * Real.exp (β / 2)
  have hpoint : ∀ z, Tendsto (fun k => (pn k z).toReal) atTop
      (𝓝 ((p z).toReal)) := by
    intro z
    exact L.pointwise P z
  have htight : ∀ ε : ℝ, 0 < ε → ∃ T : Finset (P → ℤ), ∀ k,
      1 - ε ≤ ∑ z ∈ T, (pn k z).toReal := by
    intro ε hε
    obtain ⟨T, hT⟩ :=
      cubeCurvaturePMFTotal_uniform_tight β (rootBeta_pos hβ) P ε hε
    refine ⟨T, ?_⟩
    intro k
    simpa [pn] using hT (L.subsequence k)
  have hsq (k : ℕ) : Summable (fun z => (pn k z).toReal * (f z) ^ 2) := by
    have hX4 := primal_cubeCoordinate_fourthMoment_bound
      (L.subsequence k) β (rootBeta_pos hβ) P ix
    have hY4 := primal_cubeCoordinate_fourthMoment_bound
      (L.subsequence k) β (rootBeta_pos hβ) P iy
    have hprod := primal_integrable_product_square_of_fourth X Y
      (by fun_prop) (by fun_prop) hX4.1 hY4.1
    have hnorm := pmf_summable_norm_of_integrable (p := pn k)
      (f := fun z => (f z) ^ 2) (by simpa [pn] using hprod)
    refine hnorm.congr ?_
    intro z
    rw [Real.norm_of_nonneg (sq_nonneg (f z))]
  have hsqBound (k : ℕ) :
      ∑' z, (pn k z).toReal * (f z) ^ 2 ≤ C := by
    have hX4 := primal_cubeCoordinate_fourthMoment_bound
      (L.subsequence k) β (rootBeta_pos hβ) P ix
    have hY4 := primal_cubeCoordinate_fourthMoment_bound
      (L.subsequence k) β (rootBeta_pos hβ) P iy
    have hprod := primal_integrable_product_square_of_fourth X Y
      (by fun_prop) (by fun_prop) hX4.1 hY4.1
    have hdom : Integrable
        (fun z => (1 / 2 : ℝ) * (X z ^ 4 + Y z ^ 4)) (pn k).toMeasure :=
      (hX4.1.add hY4.1).const_mul (1 / 2)
    have hpointwise (z : P → ℤ) :
        (f z) ^ 2 ≤ (1 / 2 : ℝ) * (X z ^ 4 + Y z ^ 4) := by
      dsimp [f]
      nlinarith [sq_nonneg (X z ^ 2 - Y z ^ 2)]
    have hinter : ∫ z, (f z) ^ 2 ∂(pn k).toMeasure ≤
        ∫ z, (1 / 2 : ℝ) * (X z ^ 4 + Y z ^ 4) ∂(pn k).toMeasure :=
      MeasureTheory.integral_mono hprod hdom hpointwise
    have hdomInt : ∫ z, (1 / 2 : ℝ) * (X z ^ 4 + Y z ^ 4)
        ∂(pn k).toMeasure =
        (1 / 2 : ℝ) * ((∫ z, X z ^ 4 ∂(pn k).toMeasure) +
          ∫ z, Y z ^ 4 ∂(pn k).toMeasure) := by
      rw [integral_const_mul, integral_add hX4.1 hY4.1]
    have hsum : ∫ z, (f z) ^ 2 ∂(pn k).toMeasure =
        ∑' z, (pn k z).toReal * (f z) ^ 2 := by
      simpa [smul_eq_mul] using PMF.integral_eq_tsum (pn k)
        (fun z => (f z) ^ 2) hprod
    calc
      _ = ∫ z, (f z) ^ 2 ∂(pn k).toMeasure := hsum.symm
      _ ≤ ∫ z, (1 / 2 : ℝ) * (X z ^ 4 + Y z ^ 4) ∂(pn k).toMeasure := hinter
      _ = (1 / 2 : ℝ) * ((∫ z, X z ^ 4 ∂(pn k).toMeasure) +
          ∫ z, Y z ^ 4 ∂(pn k).toMeasure) := hdomInt
      _ ≤ C := by
        dsimp [C]
        nlinarith [hX4.2, hY4.2]
  have hlimSq := pmf_secondMoment_bound_of_pointwise
    pn p f C hpoint hsq hsqBound
  have hIntSeq (k : ℕ) : Integrable f (pn k).toMeasure :=
    primal_pmf_integrable_of_secondMoment (pn k) f (hsq k)
  have hIntLim : Integrable f p.toMeasure :=
    primal_pmf_integrable_of_secondMoment p f hlimSq.1
  have hposInt (k : ℕ) : Integrable (fun z => max (f z) 0)
      (pn k).toMeasure := (hIntSeq k).pos_part
  have hnegInt (k : ℕ) : Integrable (fun z => max (-f z) 0)
      (pn k).toMeasure := (hIntSeq k).neg_part
  have hposIntLim : Integrable (fun z => max (f z) 0) p.toMeasure :=
    hIntLim.pos_part
  have hnegIntLim : Integrable (fun z => max (-f z) 0) p.toMeasure :=
    hIntLim.neg_part
  simpa [pn, p, P, f, X, Y, ix, iy, spectralPairProduct] using
    pmf_integral_tendsto_of_tight_secondMoment pn p f C hpoint htight
      hsq hsqBound hposInt hnegInt hposIntLim hnegIntLim

/-- The finite primal correlations converge along the selected cube
subsequence to the first-stage cylinder state `L`. -/
theorem primalCubePrimalCorrelation_tendsto
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (x y : LatticePoint) :
    Tendsto (fun k => primalCubePrimalCorrelation (L.subsequence k) β
      (rootBeta_pos hβ) x y) atTop
      (𝓝 (∫ ω, spectralPairProduct x y ω ∂
        (L.law (spectralPairPlaquettes x y)).toMeasure)) := by
  simpa [primalCubePrimalCorrelation] using
    primal_cubeLimitPairCorrelation_tendsto hβ L x y

/-- The expectation of the square of any finite filling observable converges
along the second, Følner-projective stage.  The fourth-moment estimate gives
uniform integrability, so this identifies actual moments and not only weak
cylinder limits. -/
theorem primal_projectiveAveragedCylinderLimit_fillingSquare_tendsto
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (s : ℕ → ℕ) (S : CurvatureCylinderState)
    (hpoint : ∀ P x, Tendsto
      (fun k => (averagedCylinderLaw (cubeStateToCylinderState L) (s k) P x).toReal)
      atTop (𝓝 ((S.law P x).toReal)))
    (μ : GlobalLinkField) (hμ : globallyCoClosed μ)
    (σ : GlobalPlaquetteField)
    (hfill : globalBoundary (σ : RealLatticeChain 4) =
      (μ : RealLatticeChain 4)) :
    Tendsto
      (fun k => ∫ x, (sourceFillingCurvaturePairing σ x) ^ 2 ∂
        (averagedCylinderLaw (cubeStateToCylinderState L) (s k)
          (fillingCurvatureIndexSet σ)).toMeasure)
      atTop
      (𝓝 (∫ x, (sourceFillingCurvaturePairing σ x) ^ 2 ∂
        (S.law (fillingCurvatureIndexSet σ)).toMeasure)) := by
  classical
  let P := fillingCurvatureIndexSet σ
  let p : PMF (P → ℤ) := S.law P
  let pn : ℕ → PMF (P → ℤ) := fun k =>
    averagedCylinderLaw (cubeStateToCylinderState L) (s k) P
  let X : (P → ℤ) → ℝ := sourceFillingCurvaturePairing σ
  let f : (P → ℤ) → ℝ := fun x => (X x) ^ 2
  let C := 512 * Real.exp ((β / 2) * fourierGreenQuadratic μ)
  have hpoint' : ∀ x, Tendsto (fun k => (pn k x).toReal) atTop
      (𝓝 ((p x).toReal)) := by
    intro x
    exact hpoint P x
  have htight : ∀ ε : ℝ, 0 < ε → ∃ T : Finset (P → ℤ), ∀ k,
      1 - ε ≤ ∑ x ∈ T, (pn k x).toReal := by
    intro ε hε
    let ε' := min ε (1 / 2)
    have hε'pos : 0 < ε' := by dsimp [ε']; positivity
    have hε'le : ε' ≤ ε := min_le_left _ _
    have hε'lt : ε' < 1 := by dsimp [ε']; norm_num
    obtain ⟨K, hK⟩ := cubeCurvatureLimitState_uniform_box_tight
      (rootBeta_pos hβ) L P ε' hε'pos
    let T := (curvatureCoordinateBox_finite (P := P) K).toFinset
    have hTset : (T : Set (P → ℤ)) = curvatureCoordinateBox (P := P) K :=
      (curvatureCoordinateBox_finite (P := P) K).coe_toFinset
    have hsingle (a : LatticeShift) : 1 - ε' ≤
        ∑ x ∈ T,
          (translateCylinderLaw (cubeStateToCylinderState L) a P x).toReal := by
      let P' := translatePlaquettes a P
      let T' := (curvatureCoordinateBox_finite (P := P') K).toFinset
      have hT'set : (T' : Set (P' → ℤ)) = curvatureCoordinateBox (P := P') K :=
        (curvatureCoordinateBox_finite (P := P') K).coe_toFinset
      have hsrc := hK P' (translatePlaquettes_card a P)
      have hsrcMeasure : 1 - ε' ≤
          ((L.law P').toMeasure (curvatureCoordinateBox (P := P') K)).toReal := by
        rw [← hT'set, primal_pmf_toReal_measure_finset]
        simpa [T'] using hsrc
      have hdstMeasure : 1 - ε' ≤
          ((translateCylinderLaw (cubeStateToCylinderState L) a P).toMeasure
            (curvatureCoordinateBox (P := P) K)).toReal := by
        rw [translateCylinderLaw_box_measure]
        exact hsrcMeasure
      rw [← primal_pmf_toReal_measure_finset _ T]
      simpa [T, hTset] using hdstMeasure
    refine ⟨T, ?_⟩
    intro k
    have haverage := finiteShiftAverage_tight_of_uniform_tight (s k)
      (fun a => translateCylinderLaw (cubeStateToCylinderState L) a P)
      T hε'lt hsingle
    exact le_trans (by linarith : 1 - ε ≤ 1 - ε') haverage
  have hfour (k : ℕ) := averagedCylinderLaw_sourceFilling_fourthMoment_bound
    hβ L μ hμ σ hfill (s k)
  have hsq (k : ℕ) : Summable (fun x => (pn k x).toReal * (f x) ^ 2) := by
    have hnorm := pmf_summable_norm_of_integrable (p := pn k)
      (f := fun x => X x ^ 4) (by simpa [pn] using (hfour k).1)
    refine hnorm.congr ?_
    intro x
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ X x ^ 4)]
    simp only [f]
    ring
  have hsqBound (k : ℕ) : ∑' x, (pn k x).toReal * (f x) ^ 2 ≤ C := by
    have hsum : ∫ x, X x ^ 4 ∂(pn k).toMeasure =
        ∑' x, (pn k x).toReal * X x ^ 4 := by
      simpa [smul_eq_mul] using PMF.integral_eq_tsum (pn k)
        (fun x => X x ^ 4) (by simpa [pn] using (hfour k).1)
    calc
      _ = ∫ x, X x ^ 4 ∂(pn k).toMeasure := by
        rw [hsum]
        apply tsum_congr
        intro x
        dsimp [f]
        ring
      _ ≤ C := by simpa [C, pn] using (hfour k).2
  have hlimSq := pmf_secondMoment_bound_of_pointwise
    pn p f C hpoint' hsq hsqBound
  have hmass : Summable (fun x => (p x).toReal) := by
    apply ENNReal.summable_toReal
    rw [p.tsum_coe]
    exact ENNReal.one_ne_top
  have hYoung (x : P → ℤ) : f x ≤ 1 + (f x) ^ 2 := by
    nlinarith [sq_nonneg (f x - 1 / 2)]
  have hweight (q : PMF (P → ℤ)) (hsq' : Summable
      (fun x => (q x).toReal * (f x) ^ 2)) (hmass' : Summable
      (fun x => (q x).toReal)) : Summable
      (fun x => (q x).toReal * f x) := by
    apply Summable.of_nonneg_of_le
      (fun x => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
    · intro x
      exact mul_le_mul_of_nonneg_left (hYoung x) ENNReal.toReal_nonneg
    · simpa [mul_add] using hmass'.add hsq'
  have hIntLim : Integrable f p.toMeasure :=
    pmf_integrable_of_summable_norm (by
      have hw := hweight p hlimSq.1 hmass
      refine hw.congr ?_
      intro x
      rw [Real.norm_of_nonneg (sq_nonneg _)])
  have hIntSeq (k : ℕ) : Integrable f (pn k).toMeasure := by
    have hmassk : Summable (fun x => (pn k x).toReal) := by
      apply ENNReal.summable_toReal
      rw [(pn k).tsum_coe]
      exact ENNReal.one_ne_top
    exact pmf_integrable_of_summable_norm (by
      have hw := hweight (pn k) (hsq k) hmassk
      refine hw.congr ?_
      intro x
      rw [Real.norm_of_nonneg (sq_nonneg _)])
  have hposInt (k : ℕ) : Integrable (fun x => max (f x) 0)
      (pn k).toMeasure := by
    have heq : (fun x => max (f x) 0) = f := by
      funext x
      exact max_eq_left (sq_nonneg (X x))
    rw [heq]
    exact hIntSeq k
  have hnegInt (k : ℕ) : Integrable (fun x => max (-f x) 0)
      (pn k).toMeasure := by
    have heq : (fun x => max (-f x) 0) = fun _ : P → ℤ => 0 := by
      funext x
      exact max_eq_right (neg_nonpos.mpr (sq_nonneg (X x)))
    rw [heq]
    exact integrable_const _
  have hposIntLim : Integrable (fun x => max (f x) 0) p.toMeasure := by
    have heq : (fun x => max (f x) 0) = f := by
      funext x
      exact max_eq_left (sq_nonneg (X x))
    rw [heq]
    exact hIntLim
  have hnegIntLim : Integrable (fun x => max (-f x) 0) p.toMeasure := by
    have heq : (fun x => max (-f x) 0) = fun _ : P → ℤ => 0 := by
      funext x
      exact max_eq_right (neg_nonpos.mpr (sq_nonneg (X x)))
    rw [heq]
    exact integrable_const _
  simpa [pn, p, P, f, X] using
    pmf_integral_tendsto_of_tight_secondMoment pn p f C hpoint' htight hsq
      hsqBound hposInt hnegInt hposIntLim hnegIntLim

/--
Pair sum and difference fillings give uniform fourth moments, and
polarization recovers the product expectation.
-/
theorem primal_pairCorrelation_tendsto
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (s : ℕ → ℕ) (S : CurvatureCylinderState)
    (hpoint : ∀ P x, Tendsto
      (fun k => (averagedCylinderLaw (cubeStateToCylinderState L) (s k) P x).toReal)
      atTop (𝓝 ((S.law P x).toReal)))
    (hinv : ∀ a P, translateCylinderLaw S a P = S.law P)
    (x y : LatticePoint) (hxy : x ≠ y) :
    Tendsto
      (fun k => ∫ ω, spectralPairProduct x y ω ∂
        (averagedCylinderLaw (cubeStateToCylinderState L) (s k)
          (spectralPairPlaquettes x y)).toMeasure)
      atTop (𝓝 (spectralFieldStrengthCorrelation S (y - x))) := by
  classical
  let P := spectralPairPlaquettes x y
  let aPlus := spectralPairSumTest x y
  let aMinus := spectralPairDifferenceTest x y
  let σPlus := spectralCurvatureWindow aPlus
  let σMinus := spectralCurvatureWindow aMinus
  let QPlus := fillingCurvatureIndexSet σPlus
  let QMinus := fillingCurvatureIndexSet σMinus
  have hQPlus : QPlus = P := spectralPairWindow_coordinates_eq hxy
  have hQMinus : QMinus = P := spectralPairDifferenceWindow_coordinates_eq hxy
  let X : (P → ℤ) → ℝ := fun ω =>
    (ω (spectralPairIndex x y x (by simp [spectralPairPlaquettes])) : ℝ)
  let Y : (P → ℤ) → ℝ := fun ω =>
    (ω (spectralPairIndex x y y (by simp [spectralPairPlaquettes])) : ℝ)
  let fPlus : (QPlus → ℤ) → ℝ := fun ω =>
    (sourceFillingCurvaturePairing σPlus ω) ^ 2
  let fMinus : (QMinus → ℤ) → ℝ := fun ω =>
    (sourceFillingCurvaturePairing σMinus ω) ^ 2
  have hxPlus : x ∈ aPlus.support := by
    rw [spectralPairSumTest_support hxy]
    simp
  have hyPlus : y ∈ aPlus.support := by
    rw [spectralPairSumTest_support hxy]
    simp
  have hxMinus : x ∈ aMinus.support := by
    rw [spectralPairDifferenceTest_support hxy]
    simp
  have hyMinus : y ∈ aMinus.support := by
    rw [spectralPairDifferenceTest_support hxy]
    simp
  have hidxPlusX : curvatureIndexCastEquiv hQPlus
      (spectralWindowIndex aPlus ⟨x, hxPlus⟩) =
        spectralPairIndex x y x (by simp [spectralPairPlaquettes]) := by
    apply Subtype.ext
    simp [curvatureIndexCastEquiv_val, spectralWindowIndex, spectralPairIndex]
  have hidxPlusY : curvatureIndexCastEquiv hQPlus
      (spectralWindowIndex aPlus ⟨y, hyPlus⟩) =
        spectralPairIndex x y y (by simp [spectralPairPlaquettes]) := by
    apply Subtype.ext
    simp [curvatureIndexCastEquiv_val, spectralWindowIndex, spectralPairIndex]
  have hidxMinusX : curvatureIndexCastEquiv hQMinus
      (spectralWindowIndex aMinus ⟨x, hxMinus⟩) =
        spectralPairIndex x y x (by simp [spectralPairPlaquettes]) := by
    apply Subtype.ext
    simp [curvatureIndexCastEquiv_val, spectralWindowIndex, spectralPairIndex]
  have hidxMinusY : curvatureIndexCastEquiv hQMinus
      (spectralWindowIndex aMinus ⟨y, hyMinus⟩) =
        spectralPairIndex x y y (by simp [spectralPairPlaquettes]) := by
    apply Subtype.ext
    simp [curvatureIndexCastEquiv_val, spectralWindowIndex, spectralPairIndex]
  have hplusEq :
      (fun ω : P → ℤ => fPlus ((curvatureAssignmentCastEquiv hQPlus).symm ω)) =
        fun ω => (X ω + Y ω) ^ 2 := by
    funext ω
    change (sourceFillingCurvaturePairing σPlus
      ((curvatureAssignmentCastEquiv hQPlus).symm ω)) ^ 2 = _
    rw [spectralWindowIndex_pairing]
    have hsupp : aPlus.support = {x, y} := by
      change (spectralPairSumTest x y).support = _
      exact spectralPairSumTest_support hxy
    change (-(∑ z : aPlus.support, aPlus z.1 *
      ((curvatureAssignmentCastEquiv hQPlus).symm ω
        (spectralWindowIndex aPlus z) : ℝ))) ^ 2 = _
    rw [primalSubtypeSumPair x y hxy aPlus.support hsupp (fun z =>
      aPlus z.1 * ((curvatureAssignmentCastEquiv hQPlus).symm ω
        (spectralWindowIndex aPlus z) : ℝ))]
    rw [show (curvatureAssignmentCastEquiv hQPlus).symm ω
        (spectralWindowIndex aPlus ⟨x, hxPlus⟩) =
          ω (curvatureIndexCastEquiv hQPlus
            (spectralWindowIndex aPlus ⟨x, hxPlus⟩)) by rfl,
      hidxPlusX]
    rw [show (curvatureAssignmentCastEquiv hQPlus).symm ω
        (spectralWindowIndex aPlus ⟨y, hyPlus⟩) =
          ω (curvatureIndexCastEquiv hQPlus
            (spectralWindowIndex aPlus ⟨y, hyPlus⟩)) by rfl,
      hidxPlusY]
    have hxVal : aPlus x = 1 := by simp [aPlus, spectralPairSumTest, hxy]
    have hyVal : aPlus y = 1 := by simp [aPlus, spectralPairSumTest, hxy]
    rw [hxVal, hyVal]
    simp [X, Y]
    ring
  have hminusEq :
      (fun ω : P → ℤ => fMinus ((curvatureAssignmentCastEquiv hQMinus).symm ω)) =
        fun ω => (X ω - Y ω) ^ 2 := by
    funext ω
    change (sourceFillingCurvaturePairing σMinus
      ((curvatureAssignmentCastEquiv hQMinus).symm ω)) ^ 2 = _
    rw [spectralWindowIndex_pairing]
    have hsupp : aMinus.support = {x, y} := by
      change (spectralPairDifferenceTest x y).support = _
      exact spectralPairDifferenceTest_support hxy
    change (-(∑ z : aMinus.support, aMinus z.1 *
      ((curvatureAssignmentCastEquiv hQMinus).symm ω
        (spectralWindowIndex aMinus z) : ℝ))) ^ 2 = _
    rw [primalSubtypeSumPair x y hxy aMinus.support hsupp (fun z =>
      aMinus z.1 * ((curvatureAssignmentCastEquiv hQMinus).symm ω
        (spectralWindowIndex aMinus z) : ℝ))]
    rw [show (curvatureAssignmentCastEquiv hQMinus).symm ω
        (spectralWindowIndex aMinus ⟨x, hxMinus⟩) =
          ω (curvatureIndexCastEquiv hQMinus
            (spectralWindowIndex aMinus ⟨x, hxMinus⟩)) by rfl,
      hidxMinusX]
    rw [show (curvatureAssignmentCastEquiv hQMinus).symm ω
        (spectralWindowIndex aMinus ⟨y, hyMinus⟩) =
          ω (curvatureIndexCastEquiv hQMinus
            (spectralWindowIndex aMinus ⟨y, hyMinus⟩)) by rfl,
      hidxMinusY]
    have hxVal : aMinus x = 1 := by simp [aMinus, spectralPairDifferenceTest, hxy]
    have hyVal : aMinus y = -1 := by simp [aMinus, spectralPairDifferenceTest, hxy]
    rw [hxVal, hyVal]
    simp [X, Y]
    ring
  have hfillPlus : globalBoundary (σPlus : RealLatticeChain 4) =
      (spectralCurvatureWindowSource aPlus : RealLatticeChain 4) := rfl
  have hfillMinus : globalBoundary (σMinus : RealLatticeChain 4) =
      (spectralCurvatureWindowSource aMinus : RealLatticeChain 4) := rfl
  have hcoPlus := spectralCurvatureWindowSource_coClosed aPlus
  have hcoMinus := spectralCurvatureWindowSource_coClosed aMinus
  have hplusConv := primal_projectiveAveragedCylinderLimit_fillingSquare_tendsto
    hβ L s S hpoint (spectralCurvatureWindowSource aPlus) hcoPlus σPlus hfillPlus
  have hminusConv := primal_projectiveAveragedCylinderLimit_fillingSquare_tendsto
    hβ L s S hpoint (spectralCurvatureWindowSource aMinus) hcoMinus σMinus hfillMinus
  have hplusLimInt := spectralCurvatureWindow_pairing_square_integrable
    hβ L s S hpoint aPlus
  have hminusLimInt := spectralCurvatureWindow_pairing_square_integrable
    hβ L s S hpoint aMinus
  have hplusSeqInt (k : ℕ) : Integrable fPlus
      (averagedCylinderLaw (cubeStateToCylinderState L) (s k) QPlus).toMeasure := by
    have hfour := averagedCylinderLaw_sourceFilling_fourthMoment_bound
      hβ L (spectralCurvatureWindowSource aPlus) hcoPlus σPlus hfillPlus (s k)
    exact primal_integrable_square_of_fourth _ (by fun_prop) hfour.1
  have hminusSeqInt (k : ℕ) : Integrable fMinus
      (averagedCylinderLaw (cubeStateToCylinderState L) (s k) QMinus).toMeasure := by
    have hfour := averagedCylinderLaw_sourceFilling_fourthMoment_bound
      hβ L (spectralCurvatureWindowSource aMinus) hcoMinus σMinus hfillMinus (s k)
    exact primal_integrable_square_of_fourth _ (by fun_prop) hfour.1
  let ν := cubeStateToCylinderState L
  have hseqPlus : (fun k => ∫ ω, (X ω + Y ω) ^ 2 ∂
      ((averagedCylinderState ν (s k)).law P).toMeasure) =
      fun k => ∫ ω, fPlus ω ∂(averagedCylinderLaw ν (s k) QPlus).toMeasure := by
    funext k
    calc
      ∫ ω, (X ω + Y ω) ^ 2 ∂((averagedCylinderState ν (s k)).law P).toMeasure =
          ∫ ω, fPlus ((curvatureAssignmentCastEquiv hQPlus).symm ω) ∂
            ((averagedCylinderState ν (s k)).law P).toMeasure := by
              apply integral_congr_ae
              exact ae_of_all _ fun ω => (congrFun hplusEq ω).symm
      _ = ∫ ω, fPlus ω ∂(averagedCylinderLaw ν (s k) QPlus).toMeasure := by
        simpa [averagedCylinderState] using
          (primal_integral_finsetEq (averagedCylinderState ν (s k)) hQPlus
            fPlus (by fun_prop)).symm
  have hlimPlus : ∫ ω, (X ω + Y ω) ^ 2 ∂(S.law P).toMeasure =
      ∫ ω, fPlus ω ∂(S.law QPlus).toMeasure := by
    calc
      _ = ∫ ω, fPlus ((curvatureAssignmentCastEquiv hQPlus).symm ω)
          ∂(S.law P).toMeasure := by
            apply integral_congr_ae
            exact ae_of_all _ fun ω => (congrFun hplusEq ω).symm
      _ = _ := (primal_integral_finsetEq S hQPlus fPlus (by fun_prop)).symm
  have hseqMinus : (fun k => ∫ ω, (X ω - Y ω) ^ 2 ∂
      ((averagedCylinderState ν (s k)).law P).toMeasure) =
      fun k => ∫ ω, fMinus ω ∂(averagedCylinderLaw ν (s k) QMinus).toMeasure := by
    funext k
    calc
      ∫ ω, (X ω - Y ω) ^ 2 ∂((averagedCylinderState ν (s k)).law P).toMeasure =
          ∫ ω, fMinus ((curvatureAssignmentCastEquiv hQMinus).symm ω) ∂
            ((averagedCylinderState ν (s k)).law P).toMeasure := by
              apply integral_congr_ae
              exact ae_of_all _ fun ω => (congrFun hminusEq ω).symm
      _ = ∫ ω, fMinus ω ∂(averagedCylinderLaw ν (s k) QMinus).toMeasure := by
        simpa [averagedCylinderState] using
          (primal_integral_finsetEq (averagedCylinderState ν (s k)) hQMinus
            fMinus (by fun_prop)).symm
  have hlimMinus : ∫ ω, (X ω - Y ω) ^ 2 ∂(S.law P).toMeasure =
      ∫ ω, fMinus ω ∂(S.law QMinus).toMeasure := by
    calc
      _ = ∫ ω, fMinus ((curvatureAssignmentCastEquiv hQMinus).symm ω)
          ∂(S.law P).toMeasure := by
            apply integral_congr_ae
            exact ae_of_all _ fun ω => (congrFun hminusEq ω).symm
      _ = _ := (primal_integral_finsetEq S hQMinus fMinus (by fun_prop)).symm
  have hplusPairConv : Tendsto
      (fun k => ∫ ω, (X ω + Y ω) ^ 2 ∂
        ((averagedCylinderState ν (s k)).law P).toMeasure) atTop
      (𝓝 (∫ ω, (X ω + Y ω) ^ 2 ∂(S.law P).toMeasure)) := by
    rw [hseqPlus, hlimPlus]
    exact hplusConv
  have hminusPairConv : Tendsto
      (fun k => ∫ ω, (X ω - Y ω) ^ 2 ∂
        ((averagedCylinderState ν (s k)).law P).toMeasure) atTop
      (𝓝 (∫ ω, (X ω - Y ω) ^ 2 ∂(S.law P).toMeasure)) := by
    rw [hseqMinus, hlimMinus]
    exact hminusConv
  have hplusPairInt (k : ℕ) : Integrable (fun ω => (X ω + Y ω) ^ 2)
      ((averagedCylinderState ν (s k)).law P).toMeasure := by
    have hEq : (fun ω => (X ω + Y ω) ^ 2) =
        fun ω => fPlus ((curvatureAssignmentCastEquiv hQPlus).symm ω) := by
      funext ω
      exact (congrFun hplusEq ω).symm
    have htrans := spectralIntegrable_finsetEq (averagedCylinderState ν (s k))
      hQPlus fPlus (by simpa [averagedCylinderState] using hplusSeqInt k)
    exact htrans.congr (ae_of_all _ fun ω => by rw [hEq])
  have hminusPairInt (k : ℕ) : Integrable (fun ω => (X ω - Y ω) ^ 2)
      ((averagedCylinderState ν (s k)).law P).toMeasure := by
    have hEq : (fun ω => (X ω - Y ω) ^ 2) =
        fun ω => fMinus ((curvatureAssignmentCastEquiv hQMinus).symm ω) := by
      funext ω
      exact (congrFun hminusEq ω).symm
    have htrans := spectralIntegrable_finsetEq (averagedCylinderState ν (s k))
      hQMinus fMinus (by simpa [averagedCylinderState] using hminusSeqInt k)
    exact htrans.congr (ae_of_all _ fun ω => by rw [hEq])
  have hplusPairIntLim : Integrable (fun ω => (X ω + Y ω) ^ 2)
      (S.law P).toMeasure := by
    have htrans := spectralIntegrable_finsetEq S hQPlus fPlus hplusLimInt
    exact htrans.congr (ae_of_all _ fun ω => by
      rw [show (fun ω : P → ℤ => fPlus
        ((curvatureAssignmentCastEquiv hQPlus).symm ω)) =
          fun ω => (X ω + Y ω) ^ 2 from hplusEq])
  have hminusPairIntLim : Integrable (fun ω => (X ω - Y ω) ^ 2)
      (S.law P).toMeasure := by
    have htrans := spectralIntegrable_finsetEq S hQMinus fMinus hminusLimInt
    exact htrans.congr (ae_of_all _ fun ω => by
      rw [show (fun ω : P → ℤ => fMinus
        ((curvatureAssignmentCastEquiv hQMinus).symm ω)) =
          fun ω => (X ω - Y ω) ^ 2 from hminusEq])
  have hpairEq (ω : P → ℤ) :
      (1 / 4 : ℝ) * ((X ω + Y ω) ^ 2 - (X ω - Y ω) ^ 2) =
        spectralPairProduct x y ω := by
    dsimp [spectralPairProduct, X, Y]
    ring
  have hpairSeqEq : (fun k => ∫ ω, spectralPairProduct x y ω ∂
      ((averagedCylinderState ν (s k)).law P).toMeasure) =
      fun k => (1 / 4 : ℝ) *
        ((∫ ω, (X ω + Y ω) ^ 2 ∂((averagedCylinderState ν (s k)).law P).toMeasure) -
          ∫ ω, (X ω - Y ω) ^ 2 ∂((averagedCylinderState ν (s k)).law P).toMeasure) := by
    funext k
    calc
      ∫ ω, spectralPairProduct x y ω ∂((averagedCylinderState ν (s k)).law P).toMeasure =
          ∫ ω, (1 / 4 : ℝ) *
            ((X ω + Y ω) ^ 2 - (X ω - Y ω) ^ 2) ∂
              ((averagedCylinderState ν (s k)).law P).toMeasure := by
                apply integral_congr_ae
                exact ae_of_all _ fun ω => (hpairEq ω).symm
      _ = _ := by
        rw [integral_const_mul, integral_sub (hplusPairInt k) (hminusPairInt k)]
  have hpairLimEq : ∫ ω, spectralPairProduct x y ω ∂(S.law P).toMeasure =
      (1 / 4 : ℝ) *
        ((∫ ω, (X ω + Y ω) ^ 2 ∂(S.law P).toMeasure) -
          ∫ ω, (X ω - Y ω) ^ 2 ∂(S.law P).toMeasure) := by
    calc
      _ = ∫ ω, (1 / 4 : ℝ) *
          ((X ω + Y ω) ^ 2 - (X ω - Y ω) ^ 2) ∂(S.law P).toMeasure := by
            apply integral_congr_ae
            exact ae_of_all _ fun ω => (hpairEq ω).symm
      _ = _ := by
        rw [integral_const_mul, integral_sub hplusPairIntLim hminusPairIntLim]
  have hproductConv := (hplusPairConv.sub hminusPairConv).const_mul (1 / 4 : ℝ)
  have hfinal : Tendsto
      (fun k => ∫ ω, spectralPairProduct x y ω ∂
        ((averagedCylinderState ν (s k)).law P).toMeasure) atTop
      (𝓝 (∫ ω, spectralPairProduct x y ω ∂(S.law P).toMeasure)) := by
    rw [hpairSeqEq, hpairLimEq]
    exact hproductConv
  have htarget := spectralPairProduct_integral_eq_correlation S hinv x y
  have htarget' : ∫ ω, spectralPairProduct x y ω ∂(S.law P).toMeasure =
      spectralFieldStrengthCorrelation S (y - x) := by simpa [P] using htarget
  rw [← htarget']
  simpa [averagedCylinderState, P] using hfinal

/-- Finite Følner-stage primal correlation, represented on the exact integer
curvature cylinder law obtained from the finite character expansion. -/
noncomputable def primalFølnerPrimalCorrelation
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (s : ℕ → ℕ) (k : ℕ) (d : LatticePoint) : ℝ :=
  ∫ ω, spectralPairProduct 0 d ω ∂
      (averagedCylinderLaw (cubeStateToCylinderState L) (s k)
        (spectralPairPlaquettes 0 d)).toMeasure

private theorem primal_translatePair_integrable_and_integral
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (a : LatticeShift) (x y : LatticePoint) :
    Integrable (spectralPairProduct x y)
        (translateCylinderLaw (cubeStateToCylinderState L) a
          (spectralPairPlaquettes x y)).toMeasure ∧
      ∫ ω, spectralPairProduct x y ω ∂
          (translateCylinderLaw (cubeStateToCylinderState L) a
            (spectralPairPlaquettes x y)).toMeasure =
        ∫ ω, spectralPairProduct (x + latticeShiftPoint a)
          (y + latticeShiftPoint a) ω ∂
            ((cubeStateToCylinderState L).law
              (spectralPairPlaquettes (x + latticeShiftPoint a)
                (y + latticeShiftPoint a))).toMeasure := by
  classical
  let ν := cubeStateToCylinderState L
  let P := spectralPairPlaquettes x y
  let x' := x + latticeShiftPoint a
  let y' := y + latticeShiftPoint a
  let P' := spectralPairPlaquettes x' y'
  let T := translatePlaquettes a P
  have hT : T = P' := by
    dsimp [T, P, P', x', y']
    exact spectralPairPlaquettes_translate a x y
  let U : (T → ℤ) → (P → ℤ) := untranslateCurvatureAssignment a P
  let J : (T → ℤ) → (P' → ℤ) := curvatureAssignmentCastEquiv hT
  let e := curvatureIndexCastEquiv hT
  have hmapU : translateCylinderLaw ν a P = PMF.map U (ν.law T) := rfl
  have hmapJ : PMF.map J (ν.law T) = ν.law P' :=
    curvatureCylinderLaw_map_finsetEq ν hT
  have hidxX :
      translatePlaquetteIndex a P (spectralPairIndex x y x
        (by simp [spectralPairPlaquettes])) =
        e.symm (spectralPairIndex x' y' x'
          (by simp [spectralPairPlaquettes])) := by
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    apply Subtype.ext
    change (curvatureIndexCastEquiv hT
      (translatePlaquetteIndex a P
        (spectralPairIndex x y x (by simp [spectralPairPlaquettes])))).1 = _
    rw [curvatureIndexCastEquiv_val]
    change translatePlaquetteEquiv a (spectralPlaquetteAt x) = _
    exact spectralPlaquetteAt_translate_point a x
  have hidxY :
      translatePlaquetteIndex a P (spectralPairIndex x y y
        (by simp [spectralPairPlaquettes])) =
        e.symm (spectralPairIndex x' y' y'
          (by simp [spectralPairPlaquettes])) := by
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    apply Subtype.ext
    change (curvatureIndexCastEquiv hT
      (translatePlaquetteIndex a P
        (spectralPairIndex x y y (by simp [spectralPairPlaquettes])))).1 = _
    rw [curvatureIndexCastEquiv_val]
    change translatePlaquetteEquiv a (spectralPlaquetteAt y) = _
    exact spectralPlaquetteAt_translate_point a y
  have hpair (ω : T → ℤ) :
      spectralPairProduct x y (U ω) = spectralPairProduct x' y' (J ω) := by
    dsimp [spectralPairProduct, U, untranslateCurvatureAssignment, J]
    simp_rw [hidxX, hidxY]
    rfl
  have hUmeas : Measurable U := by fun_prop
  have hJmeas : Measurable J := by fun_prop
  have hpairMeas : StronglyMeasurable (spectralPairProduct x y) := by fun_prop
  have hpair'Meas : StronglyMeasurable (spectralPairProduct x' y') := by fun_prop
  have hpair'Int : Integrable (spectralPairProduct x' y') (ν.law P').toMeasure :=
    primal_cubeLimitPair_integrable hβ L x' y'
  have hpair'IntMap : Integrable (spectralPairProduct x' y')
      ((ν.law T).toMeasure.map J) := by
    rw [PMF.toMeasure_map J (ν.law T) hJmeas, hmapJ]
    exact hpair'Int
  have hJcompInt : Integrable (fun ω => spectralPairProduct x' y' (J ω))
      (ν.law T).toMeasure := by
    exact (MeasureTheory.integrable_map_measure hpair'Meas.aestronglyMeasurable
      hJmeas.aemeasurable).1 hpair'IntMap
  have hUcompInt : Integrable (fun ω => spectralPairProduct x y (U ω))
      (ν.law T).toMeasure :=
    hJcompInt.congr (ae_of_all _ fun ω => (hpair ω).symm)
  have hpairInt : Integrable (spectralPairProduct x y)
      (translateCylinderLaw ν a P).toMeasure := by
    rw [hmapU, ← PMF.toMeasure_map U (ν.law T) hUmeas]
    exact (MeasureTheory.integrable_map_measure hpairMeas.aestronglyMeasurable
      hUmeas.aemeasurable).2 hUcompInt
  have hmapIntegralU :
      ∫ ω, spectralPairProduct x y ω ∂(translateCylinderLaw ν a P).toMeasure =
        ∫ ω, spectralPairProduct x y (U ω) ∂(ν.law T).toMeasure := by
    rw [hmapU, ← PMF.toMeasure_map U (ν.law T) hUmeas]
    exact MeasureTheory.integral_map_of_stronglyMeasurable hUmeas
      hpairMeas
  have hmapIntegralJ :
      ∫ ω, spectralPairProduct x' y' (J ω) ∂(ν.law T).toMeasure =
        ∫ ω, spectralPairProduct x' y' ω ∂(ν.law P').toMeasure := by
    calc
      _ = ∫ ω, spectralPairProduct x' y' ω ∂(PMF.map J (ν.law T)).toMeasure := by
        rw [← PMF.toMeasure_map J (ν.law T) hJmeas]
        exact (MeasureTheory.integral_map_of_stronglyMeasurable hJmeas
          hpair'Meas).symm
      _ = _ := by rw [hmapJ]
  refine ⟨hpairInt, ?_⟩
  calc
    _ = ∫ ω, spectralPairProduct x y (U ω) ∂(ν.law T).toMeasure := hmapIntegralU
    _ = ∫ ω, spectralPairProduct x' y' (J ω) ∂(ν.law T).toMeasure := by
      apply integral_congr_ae
      exact ae_of_all _ hpair
    _ = _ := hmapIntegralJ

/-- Each Følner-stage correlation is the finite spatial average of the
first-stage cube-limit pair expectations. -/
theorem primalFølnerPrimalCorrelation_eq_shiftAverage_of_cubeLimit
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (n : ℕ) (d : LatticePoint) :
    primalFølnerPrimalCorrelation hβ L (fun k => k) n d =
      (Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n} : ℝ)⁻¹ *
        ∑ a ∈ latticeShiftBox n,
          ∫ ω, spectralPairProduct (latticeShiftPoint a)
            (d + latticeShiftPoint a) ω ∂
              (L.law (spectralPairPlaquettes (latticeShiftPoint a)
                (d + latticeShiftPoint a))).toMeasure := by
  classical
  let ν := cubeStateToCylinderState L
  let P := spectralPairPlaquettes 0 d
  let f : LatticeShift → PMF (P → ℤ) :=
    fun a => translateCylinderLaw ν a P
  let g : (P → ℤ) → ℝ := spectralPairProduct 0 d
  have hfi (a : LatticeShift) : Integrable g (f a).toMeasure := by
    simpa [f, g, P, ν, cubeStateToCylinderState] using
      (primal_translatePair_integrable_and_integral hβ L a 0 d).1
  have havg := primal_finiteShiftAverage_integral n f g hfi
  have hterm (a : LatticeShift) :
      ∫ ω, spectralPairProduct 0 d ω ∂(f a).toMeasure =
        ∫ ω, spectralPairProduct (latticeShiftPoint a)
          (d + latticeShiftPoint a) ω ∂
              (L.law (spectralPairPlaquettes (latticeShiftPoint a)
                (d + latticeShiftPoint a))).toMeasure := by
    have hz : (0 : LatticePoint) + latticeShiftPoint a = latticeShiftPoint a :=
      zero_add _
    have h := (primal_translatePair_integrable_and_integral hβ L a 0 d).2
    rw [hz] at h
    simpa [f, g, P, ν, cubeStateToCylinderState] using h
  unfold primalFølnerPrimalCorrelation
  dsimp [averagedCylinderLaw]
  calc
    _ = (Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n} : ℝ)⁻¹ *
        ∑ a ∈ latticeShiftBox n,
          ∫ ω, spectralPairProduct 0 d ω ∂(f a).toMeasure := by
            simpa [ν, P, f, g] using havg.2
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      exact hterm a


noncomputable def primalFiniteCubeFølnerCorrelation
    (N n : ℕ) (β : ℝ) (hβ : 0 < β) (d : LatticePoint) : ℝ :=
  (Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n} : ℝ)⁻¹ *
    ∑ a ∈ latticeShiftBox n,
      primalCubePrimalCorrelation N β hβ (latticeShiftPoint a)
        (d + latticeShiftPoint a)

/--
For each fixed Følner box, the spatial average of finite cube primal
correlations converges in the first thermodynamic limit to the corresponding
average of the cube-limit state.
-/
theorem primalFiniteCubeFølnerCorrelation_tendsto
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (n : ℕ) (d : LatticePoint) (hd : d ≠ 0) :
    Tendsto (fun j => primalFiniteCubeFølnerCorrelation (L.subsequence j)
      n β (rootBeta_pos hβ) d) atTop
      (𝓝 (primalFølnerPrimalCorrelation hβ L (fun k => k) n d)) := by
  classical
  let c : ℝ :=
    (Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n} : ℝ)⁻¹
  have hsum : Tendsto
      (fun j => ∑ a ∈ latticeShiftBox n,
        primalCubePrimalCorrelation (L.subsequence j) (β := β)
          (rootBeta_pos hβ) (latticeShiftPoint a) (d + latticeShiftPoint a))
      atTop
      (𝓝 (∑ a ∈ latticeShiftBox n,
        ∫ ω, spectralPairProduct (latticeShiftPoint a)
          (d + latticeShiftPoint a) ω ∂
            (L.law (spectralPairPlaquettes (latticeShiftPoint a)
              (d + latticeShiftPoint a))).toMeasure)) := by
    apply tendsto_finsetSum
    intro a ha
    have hxy : latticeShiftPoint a ≠ d + latticeShiftPoint a := by
      intro h
      apply hd
      have := congrArg (fun z : LatticePoint => z - latticeShiftPoint a) h
      simpa using this.symm
    exact primalCubePrimalCorrelation_tendsto hβ L
      (latticeShiftPoint a) (d + latticeShiftPoint a)
  have hsumScaled := hsum.const_mul c
  have havg := primalFølnerPrimalCorrelation_eq_shiftAverage_of_cubeLimit
    hβ L n d
  unfold primalFiniteCubeFølnerCorrelation
  change Tendsto
    (fun j => c * ∑ a ∈ latticeShiftBox n,
      primalCubePrimalCorrelation (L.subsequence j) β (rootBeta_pos hβ)
        (latticeShiftPoint a) (d + latticeShiftPoint a)) atTop
    (𝓝 (primalFølnerPrimalCorrelation hβ L (fun k => k) n d))
  rw [havg]
  simpa [c, mul_comm] using hsumScaled


theorem primalFølnerPrimalCorrelation_tendsto
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (s : ℕ → ℕ) (S : CurvatureCylinderState)
    (hpoint : ∀ P x, Tendsto
      (fun k => (averagedCylinderLaw (cubeStateToCylinderState L) (s k) P x).toReal)
      atTop (𝓝 ((S.law P x).toReal)))
    (hinv : ∀ a P, translateCylinderLaw S a P = S.law P)
    (d : LatticePoint) (hd : d ≠ 0) :
    Tendsto (fun k => primalFølnerPrimalCorrelation hβ L s k d) atTop
      (𝓝 (spectralFieldStrengthCorrelation S d)) := by
  have h := primal_pairCorrelation_tendsto hβ L s S hpoint hinv 0 d (by simpa using hd.symm)
  simpa [primalFølnerPrimalCorrelation] using h

/-- Changing one value cannot change absolute summability on the lattice. -/
theorem summable_abs_iff_of_eq_offOrigin
    (f g : LatticePoint → ℝ)
    (hfg : ∀ x, x ≠ 0 → f x = g x) :
    Summable (fun x => |f x|) ↔ Summable (fun x => |g x|) := by
  have hEq : (fun x => |f x|) =ᶠ[cofinite] fun x => |g x| := by
    filter_upwards [Filter.eventually_cofinite_ne (0 : LatticePoint)] with x hx
    exact congrArg abs (hfg x hx)
  exact summable_congr_cofinite hEq

/-- A dual non-summability result transfers to any correlation agreeing with
the dual one away from the diagonal. -/
theorem not_summable_abs_of_eq_offOrigin
    (f g : LatticePoint → ℝ)
    (hfg : ∀ x, x ≠ 0 → f x = g x)
    (hdual : ¬ Summable (fun x => |g x|)) :
    ¬ Summable (fun x => |f x|) := by
  intro hf
  exact hdual ((summable_abs_iff_of_eq_offOrigin f g hfg).mp hf)


theorem primal_primal_not_absSummable_of_offOrigin_bridge
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (s : ℕ → ℕ) (S : CurvatureCylinderState)
    (hpoint : ∀ P x, Tendsto
      (fun k => (averagedCylinderLaw (cubeStateToCylinderState L) (s k) P x).toReal)
      atTop (𝓝 ((S.law P x).toReal)))
    (hinv : ∀ a P, translateCylinderLaw S a P = S.law P)
    (hβlo : 0 < betaDoublePrime rootPackingCoefficient β)
    (primalCorrelation : LatticePoint → ℝ)
    (hbridge : ∀ x, x ≠ 0 →
      primalCorrelation x = spectralFieldStrengthCorrelation S x) :
    ¬ Summable (fun x => |primalCorrelation x|) := by
  apply not_summable_abs_of_eq_offOrigin primalCorrelation
    (spectralFieldStrengthCorrelation S) hbridge
  exact spectralTranslationInvariantCorrelation_not_absSummable
    hβ L s S hpoint hinv hβlo

/--
The value at the single
diagonal displacement can be the diagonal contact value; it does not enter
the off-origin transfer.
-/
theorem primal_primal_not_absSummable_of_twoStageLimit
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (s : ℕ → ℕ) (S : CurvatureCylinderState)
    (hpoint : ∀ P x, Tendsto
      (fun k => (averagedCylinderLaw (cubeStateToCylinderState L) (s k) P x).toReal)
      atTop (𝓝 ((S.law P x).toReal)))
    (hinv : ∀ a P, translateCylinderLaw S a P = S.law P)
    (hβlo : 0 < betaDoublePrime rootPackingCoefficient β)
    (primalCorrelation : LatticePoint → ℝ)
    (hlimit : ∀ d, d ≠ 0 → Tendsto
      (fun k => primalFølnerPrimalCorrelation hβ L s k d) atTop
      (𝓝 (primalCorrelation d))) :
    ¬ Summable (fun d => |primalCorrelation d|) := by
  have hbridge : ∀ d, d ≠ 0 →
      primalCorrelation d = spectralFieldStrengthCorrelation S d := by
    intro d hd
    exact tendsto_nhds_unique (hlimit d hd)
      (primalFølnerPrimalCorrelation_tendsto hβ L s S hpoint hinv d hd)
  exact primal_primal_not_absSummable_of_offOrigin_bridge
    hβ L s S hpoint hinv hβlo primalCorrelation hbridge

/--
Consequently its absolute spatial sum diverges; a diagonal
contact term changes only the value at the origin.
-/
theorem primal_selectedTwoStagePrimal_not_absSummable
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (s : ℕ → ℕ) (S : CurvatureCylinderState)
    (hpoint : ∀ P x, Tendsto
      (fun k => (averagedCylinderLaw (cubeStateToCylinderState L) (s k) P x).toReal)
      atTop (𝓝 ((S.law P x).toReal)))
    (hinv : ∀ a P, translateCylinderLaw S a P = S.law P)
    (hβlo : 0 < betaDoublePrime rootPackingCoefficient β) :
    ¬ Summable (fun d => |spectralFieldStrengthCorrelation S d|) := by
  apply primal_primal_not_absSummable_of_twoStageLimit
    hβ L s S hpoint hinv hβlo (spectralFieldStrengthCorrelation S)
  intro d hd
  exact primalFølnerPrimalCorrelation_tendsto hβ L s S hpoint hinv d hd

end FroehlichSpencer.FS82.Infinite.Nonsummability

end
