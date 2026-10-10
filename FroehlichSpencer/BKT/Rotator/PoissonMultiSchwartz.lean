/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.SchwartzFourierLattice
public import FroehlichSpencer.BKT.Rotator.SchwartzLatticePeriodization
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Finite-dimensional Poisson summation for Schwartz functions -/

@[expose] public section

open Complex MeasureTheory Set TopologicalSpace
open scoped FourierTransform Pointwise SchwartzMap

noncomputable section

namespace FroehlichSpencer.BKT.Rotator

/-- The integer lattice as an additive subgroup of finite-dimensional real coordinate space. -/
def integerLattice {ι : Type*} : AddSubgroup (ι → ℝ) where
  carrier := {x | ∀ i, ∃ n : ℤ, x i = (n : ℝ)}
  zero_mem' := by intro i; exact ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy i
    obtain ⟨m, hxm⟩ := hx i
    obtain ⟨n, hyn⟩ := hy i
    refine ⟨m + n, ?_⟩
    change x i + y i = ((m + n : ℤ) : ℝ)
    rw [hxm, hyn]
    simp
  neg_mem' := by
    intro x hx i
    obtain ⟨m, hxm⟩ := hx i
    refine ⟨-m, ?_⟩
    change -x i = ((-m : ℤ) : ℝ)
    rw [hxm]
    simp

/-- The half-open product cell for the integer lattice. -/
def integerLatticeFundamentalCell {ι : Type*} : Set (ι → ℝ) :=
  {x | ∀ i, x i ∈ Ioc (0 : ℝ) 1}

theorem integerLatticeFundamentalCell_measurableSet {ι : Type*} [Fintype ι] :
    MeasurableSet (integerLatticeFundamentalCell (ι := ι)) :=
  MeasurableSet.univ_pi' (fun _ : ι => measurableSet_Ioc)

/-- The standard unit cube is a fundamental domain for the integer lattice action. -/
theorem integerLatticeFundamentalCell_fundamentalDomain {ι : Type*} [Fintype ι] :
    IsAddFundamentalDomain (integerLattice (ι := ι))
      (integerLatticeFundamentalCell (ι := ι)) volume := by
  classical
  refine IsAddFundamentalDomain.mk' ?_ ?_
  · rw [integerLatticeFundamentalCell]
    have hm : MeasurableSet {x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} :=
      integerLatticeFundamentalCell_measurableSet
    exact hm.nullMeasurableSet
  · intro x
    let y : ι → ℝ := fun i =>
      (AddCircle.equivIoc (1 : ℝ) (0 : ℝ) (x i : AddCircle (1 : ℝ))).1
    have hy : ∀ i, y i ∈ Ioc (0 : ℝ) 1 := fun i => by
      simpa using (AddCircle.equivIoc (1 : ℝ) (0 : ℝ) (x i : AddCircle (1 : ℝ))).2
    have hcircle : ∀ i, (y i : AddCircle (1 : ℝ)) = (x i : AddCircle (1 : ℝ)) := by
      intro i
      exact AddCircle.coe_equivIoc
    have hshift : ∀ i, ∃ n : ℤ, y i - x i = (n : ℝ) := by
      intro i
      have hzero : ((y i - x i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
        rw [AddCircle.coe_sub, hcircle i]
        simp
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
      exact ⟨n, by simpa using hn.symm⟩
    choose g hg using hshift
    let gR : ι → ℝ := fun i => (g i : ℝ)
    have hgR : gR ∈ integerLattice (ι := ι) := by
      intro i
      exact ⟨g i, rfl⟩
    let gSub : integerLattice (ι := ι) := ⟨gR, hgR⟩
    refine ⟨gSub, ?_, ?_⟩
    · change ∀ i, (gR + x) i ∈ Ioc (0 : ℝ) 1
      intro i
      have hi := hg i
      change y i - x i = (g i : ℝ) at hi
      have heq : gR i + x i = y i := by
        calc
          gR i + x i = y i - x i + x i := by rw [show gR i = (g i : ℝ) by rfl, hi]
          _ = y i := sub_add_cancel _ _
      change gR i + x i ∈ Ioc (0 : ℝ) 1
      rw [heq]
      exact hy i
    · intro g' hg'
      apply Subtype.ext
      funext i
      have h1 : ((((g' : ι → ℝ) + x) i : ℝ) : AddCircle (1 : ℝ)) =
          (x i : AddCircle (1 : ℝ)) := by
        change ((((g' : ι → ℝ) i + x i : ℝ) : AddCircle (1 : ℝ))) = _
        obtain ⟨n, hn⟩ := g'.property i
        have hn0 : ((n : ℝ) : AddCircle (1 : ℝ)) = 0 := by
          apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
          exact ⟨n, by simp⟩
        rw [hn, AddCircle.coe_add, hn0, zero_add]
      have hyEq : gR i + x i = y i := by
        rw [show gR i = (g i : ℝ) by rfl]
        linarith [hg i]
      have h2 : ((gR i + x i : ℝ) : AddCircle (1 : ℝ)) =
          (x i : AddCircle (1 : ℝ)) := by
        rw [hyEq, hcircle i]
      have hy1 : ((g' : ι → ℝ) + x) i ∈ Ioc (0 : ℝ) 1 := by
        change ∀ j, ((g' : ι → ℝ) + x) j ∈ Ioc (0 : ℝ) 1 at hg'
        exact hg' i
      have hy2 : (gR + x) i ∈ Ioc (0 : ℝ) 1 := by
        change gR i + x i ∈ Ioc (0 : ℝ) 1
        rw [hyEq]
        exact hy i
      have heq :=
        (AddCircle.coe_eq_coe_iff_of_mem_Ioc (p := (1 : ℝ)) (a := (0 : ℝ))
          (by simpa using hy1) (by simpa using hy2)).mp (h1.trans h2.symm)
      have heq' : (g' : ι → ℝ) i + x i = gR i + x i := by
        simpa only [Pi.add_apply] using heq
      exact add_right_cancel heq'

/-- The integer lattice is equivalent, as a type, to the finite product of integer coordinates. -/
noncomputable def integerLatticeEquivPiInt {ι : Type*} [Fintype ι] :
    integerLattice (ι := ι) ≃ (ι → ℤ) where
  toFun x i := Classical.choose (x.property i)
  invFun q := ⟨fun i => (q i : ℝ), fun i => ⟨q i, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact (Classical.choose_spec (x.property i)).symm
  right_inv q := by
    funext i
    exact (Int.cast_injective
      (Classical.choose_spec (show ∃ n : ℤ, (q i : ℝ) = (n : ℝ) from ⟨q i, rfl⟩))).symm

instance integerLattice_countable {ι : Type*} [Fintype ι] :
    Countable (integerLattice (ι := ι)) :=
  (integerLatticeEquivPiInt (ι := ι)).countable_iff.mpr inferInstance

/-- The quotient character on the Euclidean cover of the product torus. -/
def integerTorusCharacter {ι : Type*} [Fintype ι] (q : ι → ℤ) (x : ι → ℝ) : ℂ :=
  UnitAddTorus.mFourier (-q) (latticeTorusQuotientMap x)

theorem integerTorusCharacter_eq_exp {ι : Type*} [Fintype ι]
    (q : ι → ℤ) (x : ι → ℝ) :
    integerTorusCharacter q x =
      Complex.exp (((-2 * Real.pi * ∑ i : ι, x i * (q i : ℝ) : ℝ) : ℂ) * Complex.I) := by
  simp only [integerTorusCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    latticeTorusQuotientMap]
  let c : ι → ℂ := fun i => ((-2 * Real.pi * x i * (q i : ℝ) : ℝ) : ℂ) * Complex.I
  have hfactor : ∀ i, fourier (-q i) (x i : AddCircle (1 : ℝ)) = Complex.exp (c i) := by
    intro i
    rw [fourier_coe_apply]
    simp [c]
    ring_nf
  rw [show (∏ i : ι, fourier ((-q) i) ↑(x i)) = ∏ i : ι, Complex.exp (c i) by
    apply Finset.prod_congr rfl
    intro i hi
    exact hfactor i]
  rw [show (∏ i : ι, Complex.exp (c i)) = Complex.exp (∑ i : ι, c i) by
    simpa using (Complex.exp_sum (Finset.univ : Finset ι) c).symm]
  congr 1
  simp only [c]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  apply congrArg (fun z : ℂ => z * Complex.I)
  apply congrArg Complex.ofReal
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (by
    intro i hi
    ring)

theorem integerTorusCharacter_periodic {ι : Type*} [Fintype ι]
    (q z : ι → ℤ) (x : ι → ℝ) :
    integerTorusCharacter q (x + fun i => (z i : ℝ)) = integerTorusCharacter q x := by
  apply congrArg (UnitAddTorus.mFourier (-q))
  funext i
  change ((x i + (z i : ℝ) : ℝ) : AddCircle (1 : ℝ)) = (x i : AddCircle (1 : ℝ))
  rw [AddCircle.coe_add]
  have hz : ((z i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
    exact ⟨z i, by simp⟩
  rw [hz, add_zero]

theorem continuous_integerTorusCharacter {ι : Type*} [Fintype ι] (q : ι → ℤ) :
    Continuous (integerTorusCharacter q) := by
  fun_prop [integerTorusCharacter, latticeTorusQuotientMap]

theorem norm_integerTorusCharacter_le_one {ι : Type*} [Fintype ι]
    (q : ι → ℤ) (x : ι → ℝ) : ‖integerTorusCharacter q x‖ ≤ 1 := by
  rw [integerTorusCharacter]
  calc
    ‖UnitAddTorus.mFourier (-q) (latticeTorusQuotientMap x)‖ ≤
        ‖UnitAddTorus.mFourier (-q)‖ :=
          (UnitAddTorus.mFourier (-q)).norm_coe_le_norm _
    _ = 1 := UnitAddTorus.mFourier_norm

theorem integrable_integerTorusCharacter_mul_schwartz_translate
    {ι : Type*} [Fintype ι] (f : 𝓢(ι → ℝ, ℂ)) (q : ι → ℤ) (v : ι → ℝ) :
    Integrable (fun x => integerTorusCharacter q x * f (x + v)) := by
  have hf := integrable_schwartz_pi f
  have hmp : MeasurePreserving (fun x : ι → ℝ => x + v) volume :=
    measurePreserving_add_right volume v
  have hfshift : Integrable (fun x : ι → ℝ => f (x + v)) := by
    simpa only [Function.comp_def] using
      (hmp.integrable_comp hf.1).mpr hf
  refine hfshift.norm.mono'
    ((continuous_integerTorusCharacter q).aestronglyMeasurable.mul hfshift.1) ?_
  filter_upwards [] with x
  rw [norm_mul]
  calc
    ‖integerTorusCharacter q x‖ * ‖f (x + v)‖ ≤ 1 * ‖f (x + v)‖ :=
      mul_le_mul_of_nonneg_right (norm_integerTorusCharacter_le_one q x)
        (norm_nonneg _)
    _ = ‖f (x + v)‖ := one_mul _

/-- Schwartz decay supplies all domination hypotheses for the unit-cell Poisson argument. -/
theorem poissonSchwartz_cell_domination
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : 𝓢(ι → ℝ, ℂ)) :
    (∀ q : ι → ℤ,
      Integrable (fun x => integerTorusCharacter q x * f x)) ∧
    (∀ q z : ι → ℤ,
      Integrable (fun x => integerTorusCharacter q x *
        f (x + fun i => (z i : ℝ)))
        (volume.restrict (integerLatticeFundamentalCell (ι := ι)))) ∧
    (∀ q : ι → ℤ,
      Summable fun z : ι → ℤ =>
        ∫ x, ‖integerTorusCharacter q x *
          f (x + fun i => (z i : ℝ))‖
          ∂(volume.restrict (integerLatticeFundamentalCell (ι := ι)))) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro q
    simpa using integrable_integerTorusCharacter_mul_schwartz_translate f q 0
  · intro q z
    exact (integrable_integerTorusCharacter_mul_schwartz_translate f q
      (fun i => (z i : ℝ))).integrableOn
  · intro q
    let D : Set (ι → ℝ) := integerLatticeFundamentalCell (ι := ι)
    let μ : Measure (ι → ℝ) := volume.restrict D
    let K : Compacts (ι → ℝ) :=
      ⟨Metric.closedBall (0 : ι → ℝ) 2, isCompact_closedBall _ _⟩
    have hDsub : D ⊆ Metric.closedBall (0 : ι → ℝ) 2 := by
      intro x hx
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hn : ‖x‖ ≤ 1 := (pi_norm_le_iff_of_nonneg (by norm_num : 0 ≤ (1 : ℝ))).2
        (fun i => by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (hx i).1)]
          exact (hx i).2)
      exact (by simpa [dist_eq_norm] using hn.trans (by norm_num : (1 : ℝ) ≤ 2))
    have hμfin : μ Set.univ < ⊤ := by
      rw [show μ Set.univ = volume D by simp [μ, D]]
      exact (measure_mono hDsub).trans_lt (measure_closedBall_lt_top)
    have hlocal := schwartzLatticeShifts_locally_summable f K
    have hlocal' : Summable fun z : ι → ℤ =>
        (μ.real Set.univ) * ‖(schwartzLatticeShift f z).restrict K‖ :=
      hlocal.mul_left (μ.real Set.univ)
    refine Summable.of_nonneg_of_le (fun z => integral_nonneg (fun _ => norm_nonneg _))
      (fun z => ?_) hlocal'
    have htermInt : Integrable (fun x : ι → ℝ =>
        ‖integerTorusCharacter q x * f (x + fun i => (z i : ℝ))‖) μ := by
      exact ((integrable_integerTorusCharacter_mul_schwartz_translate f q
        (fun i => (z i : ℝ))).norm).integrableOn
    have hconstInt : Integrable (fun _ : ι → ℝ =>
        ‖(schwartzLatticeShift f z).restrict K‖) μ :=
      (integrable_const_iff (μ := μ)
        (c := ‖(schwartzLatticeShift f z).restrict K‖)).2
        (Or.inr (show IsFiniteMeasure μ from ⟨hμfin⟩))
    have hpoint : (fun x : ι → ℝ =>
        ‖integerTorusCharacter q x * f (x + fun i => (z i : ℝ))‖) ≤ᵐ[μ]
        (fun _ => ‖(schwartzLatticeShift f z).restrict K‖) := by
      filter_upwards [ae_restrict_mem integerLatticeFundamentalCell_measurableSet] with x hx
      have hxD : x ∈ D := hx
      have hxK : (x : ι → ℝ) ∈ (K : Set (ι → ℝ)) := hDsub hxD
      have hval := ((schwartzLatticeShift f z).restrict K).norm_coe_le_norm ⟨x, hxK⟩
      rw [ContinuousMap.restrict_apply] at hval
      rw [norm_mul]
      calc
        ‖integerTorusCharacter q x‖ * ‖f (x + fun i => (z i : ℝ))‖ ≤
            ‖f (x + fun i => (z i : ℝ))‖ := by
          calc
            _ ≤ 1 * ‖f (x + fun i => (z i : ℝ))‖ :=
              mul_le_mul_of_nonneg_right (norm_integerTorusCharacter_le_one q x)
                (norm_nonneg _)
            _ = _ := one_mul _
        _ = ‖(schwartzLatticeShift f z) x‖ := by simp [schwartzLatticeShift]
        _ ≤ ‖(schwartzLatticeShift f z).restrict K‖ := by
          simpa [schwartzLatticeShift] using hval
    calc
      _ ≤ ∫ x, ‖(schwartzLatticeShift f z).restrict K‖ ∂μ :=
        integral_mono_ae htermInt hconstInt hpoint
      _ = (μ.real Set.univ) * ‖(schwartzLatticeShift f z).restrict K‖ := by
        rw [integral_const]
        simp [smul_eq_mul]

/-- The absolutely integrable summand on the unit fundamental cell for one Fourier mode. -/
def integerTorusCharacterCellTerm {ι : Type*} [Fintype ι]
    (q : ι → ℤ) (f : (ι → ℝ) → ℂ) (z : ι → ℤ) : ℂ :=
  ∫ x in integerLatticeFundamentalCell (ι := ι),
    integerTorusCharacter q x * f (x + fun i => (z i : ℝ)) ∂volume

/-- Unfolding the integer translates of the unit cell recovers the full Euclidean Fourier
integral. -/
theorem integerTorusCharacter_integral_eq_tsum_cellTerm
    {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℂ) (q : ι → ℤ)
    (hglobal : Integrable (fun x => integerTorusCharacter q x * f x)) :
    (∫ x, integerTorusCharacter q x * f x ∂volume) =
      ∑' z : ι → ℤ, integerTorusCharacterCellTerm q f z := by
  classical
  let D := integerLatticeFundamentalCell (ι := ι)
  let e := integerLatticeEquivPiInt (ι := ι)
  let globalF : (ι → ℝ) → ℂ := fun x => integerTorusCharacter q x * f x
  let shiftedIntegral : (ι → ℤ) → ℂ := fun z =>
    ∫ x in D, globalF ((fun i => (z i : ℝ)) + x) ∂volume
  have hfund := integerLatticeFundamentalCell_fundamentalDomain (ι := ι)
  have hfundInt := hfund.integral_eq_tsum'' globalF hglobal
  have hcast (g : integerLattice (ι := ι)) :
      (g : ι → ℝ) = fun i => (e g i : ℝ) := by
    funext i
    exact Classical.choose_spec (g.property i)
  have hsubgroupSum :
      (∑' g : integerLattice (ι := ι),
        ∫ x in D, globalF ((g : ι → ℝ) + x) ∂volume) =
      ∑' z : ι → ℤ, shiftedIntegral z := by
    calc
      _ = ∑' g : integerLattice (ι := ι), shiftedIntegral (e g) := by
        apply tsum_congr
        intro g
        apply setIntegral_congr_fun integerLatticeFundamentalCell_measurableSet
        intro x hx
        rw [hcast]
      _ = ∑' z : ι → ℤ, shiftedIntegral z := e.tsum_eq shiftedIntegral
  have hshift (z : ι → ℤ) : shiftedIntegral z = integerTorusCharacterCellTerm q f z := by
    apply setIntegral_congr_fun integerLatticeFundamentalCell_measurableSet
    intro x hx
    dsimp [shiftedIntegral, globalF, integerTorusCharacterCellTerm]
    rw [show (fun i => (z i : ℝ)) + x = x + fun i => (z i : ℝ) by
      funext i; simp [Pi.add_apply, add_comm]]
    rw [integerTorusCharacter_periodic q z x]
  calc
    _ = ∑' g : integerLattice (ι := ι),
          ∫ x in D, globalF ((g : ι → ℝ) + x) ∂volume := hfundInt
    _ = ∑' z : ι → ℤ, shiftedIntegral z := hsubgroupSum
    _ = ∑' z : ι → ℤ, integerTorusCharacterCellTerm q f z := by
      apply tsum_congr
      exact hshift

/-- A Schwartz periodization's torus Fourier coefficient is the sum of its cell integrals. The
summability hypothesis is exactly the absolute-integrability domination needed to exchange the
lattice sum and the cell integral. -/
theorem schwartzTorusPeriodization_fourierCoeff_eq_cellPeriodizationIntegral
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace (UnitAddTorus ι)] [BorelSpace (UnitAddTorus ι)]
    (f : 𝓢(ι → ℝ, ℂ)) (q : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (schwartzTorusPeriodization f) q =
      ∫ x in integerLatticeFundamentalCell (ι := ι),
        integerTorusCharacter q x * schwartzLatticePeriodization f x ∂volume := by
  classical
  let D := integerLatticeFundamentalCell (ι := ι)
  rw [UnitAddTorus.mFourierCoeff_eq_integral
    (schwartzTorusPeriodization f) q (fun _ => 0)]
  have hD : {x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) (0 + 1)} = D := by
    ext x
    simp [D, integerLatticeFundamentalCell]
  rw [hD]
  apply setIntegral_congr_fun integerLatticeFundamentalCell_measurableSet
  intro x hx
  change UnitAddTorus.mFourier (-q) (latticeTorusQuotientMap x) •
    schwartzTorusPeriodization f (latticeTorusQuotientMap x) =
      integerTorusCharacter q x * schwartzLatticePeriodization f x
  rw [schwartzTorusPeriodization_coe]
  simp [integerTorusCharacter, smul_eq_mul]

/-- The dominated sum/integral exchange for the periodized Schwartz density. -/
theorem schwartzLatticePeriodization_cellIntegral_eq_tsum_cellTerm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : 𝓢(ι → ℝ, ℂ)) (q : ι → ℤ)
    (hterm : ∀ z : ι → ℤ,
      Integrable (fun x => integerTorusCharacter q x *
        f (x + fun i => (z i : ℝ)))
        (volume.restrict (integerLatticeFundamentalCell (ι := ι))))
    (hsum : Summable fun z : ι → ℤ =>
      ∫ x, ‖integerTorusCharacter q x * f (x + fun i => (z i : ℝ))‖
        ∂(volume.restrict (integerLatticeFundamentalCell (ι := ι)))) :
    (∫ x in integerLatticeFundamentalCell (ι := ι),
      integerTorusCharacter q x * schwartzLatticePeriodization f x ∂volume) =
      ∑' z : ι → ℤ, integerTorusCharacterCellTerm q f z := by
  classical
  let μ := volume.restrict (integerLatticeFundamentalCell (ι := ι))
  let F : (ι → ℤ) → (ι → ℝ) → ℂ := fun z x =>
    integerTorusCharacter q x * f (x + fun i => (z i : ℝ))
  have hswap :
      (∑' z : ι → ℤ, ∫ x, F z x ∂μ) =
      ∫ x, ∑' z : ι → ℤ, F z x ∂μ := by
    exact integral_tsum_of_summable_integral_norm
      (ι := ι → ℤ) (α := ι → ℝ) (E := ℂ) (μ := μ) (F := F) hterm hsum
  calc
    (∫ x in integerLatticeFundamentalCell (ι := ι),
      integerTorusCharacter q x * schwartzLatticePeriodization f x ∂volume) =
        ∫ x in integerLatticeFundamentalCell (ι := ι), ∑' z : ι → ℤ,
          integerTorusCharacter q x * f (x + fun i => (z i : ℝ)) ∂volume := by
      apply setIntegral_congr_fun integerLatticeFundamentalCell_measurableSet
      intro x hx
      change integerTorusCharacter q x * schwartzLatticePeriodization f x = _
      rw [schwartzLatticePeriodization_apply]
      rw [← tsum_mul_left]
    _ = ∑' z : ι → ℤ, integerTorusCharacterCellTerm q f z := by
      simpa [integerTorusCharacterCellTerm, μ] using hswap.symm

/-- A Schwartz periodization's torus Fourier coefficient is the sum of its cell integrals under
the explicit absolute-integrability domination. -/
theorem schwartzTorusPeriodization_fourierCoeff_eq_tsum_cellTerm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace (UnitAddTorus ι)] [BorelSpace (UnitAddTorus ι)]
    (f : 𝓢(ι → ℝ, ℂ)) (q : ι → ℤ)
    (hterm : ∀ z : ι → ℤ,
      Integrable (fun x => integerTorusCharacter q x *
        f (x + fun i => (z i : ℝ)))
        (volume.restrict (integerLatticeFundamentalCell (ι := ι))))
    (hsum : Summable fun z : ι → ℤ =>
      ∫ x, ‖integerTorusCharacter q x * f (x + fun i => (z i : ℝ))‖
        ∂(volume.restrict (integerLatticeFundamentalCell (ι := ι)))) :
    UnitAddTorus.mFourierCoeff (schwartzTorusPeriodization f) q =
      ∑' z : ι → ℤ, integerTorusCharacterCellTerm q f z := by
  rw [schwartzTorusPeriodization_fourierCoeff_eq_cellPeriodizationIntegral]
  exact schwartzLatticePeriodization_cellIntegral_eq_tsum_cellTerm f q hterm hsum

/-- The finite-dimensional Poisson summation identity for a Schwartz function, assuming the
standard cellwise absolute-integrability domination required for the lattice sum/integral exchange.
The coefficient sum and lattice-sample sum are both unconditional tsums. -/
theorem poissonSummation_schwartz_pi
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace (UnitAddTorus ι)] [BorelSpace (UnitAddTorus ι)]
    (f : 𝓢(ι → ℝ, ℂ))
    (hglobal : ∀ q : ι → ℤ,
      Integrable (fun x => integerTorusCharacter q x * f x))
    (hterm : ∀ q z : ι → ℤ,
      Integrable (fun x => integerTorusCharacter q x *
        f (x + fun i => (z i : ℝ)))
        (volume.restrict (integerLatticeFundamentalCell (ι := ι))))
    (hsum : ∀ q : ι → ℤ,
      Summable fun z : ι → ℤ =>
        ∫ x, ‖integerTorusCharacter q x * f (x + fun i => (z i : ℝ))‖
          ∂(volume.restrict (integerLatticeFundamentalCell (ι := ι)))) :
    ∑' q : ι → ℤ, multiEuclideanFourierCoefficient f q =
      ∑' z : ι → ℤ, f (fun i => (z i : ℝ)) := by
  have hcoeff (q : ι → ℤ) :
      UnitAddTorus.mFourierCoeff (schwartzTorusPeriodization f) q =
        multiEuclideanFourierCoefficient f q := by
    rw [schwartzTorusPeriodization_fourierCoeff_eq_tsum_cellTerm f q (hterm q) (hsum q)]
    rw [← integerTorusCharacter_integral_eq_tsum_cellTerm f q (hglobal q)]
    rw [multiEuclideanFourierCoefficient]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [integerTorusCharacter_eq_exp]
  exact (tsum_multiEuclideanFourierCoefficient_eq_latticeSamples
    f (schwartzTorusPeriodization f) hcoeff
    (schwartzTorusPeriodization_zero f)
    (summable_multiEuclideanFourierCoefficient_of_schwartz f))

/-- Unconditional finite-dimensional Poisson summation for every Schwartz function on a finite
coordinate space. The cellwise hypotheses of `poissonSummation_schwartz_pi` follow from the
Schwartz decay estimate on a compact neighborhood of the unit cell. -/
theorem poissonSummation_schwartz_pi_unconditional
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace (UnitAddTorus ι)] [BorelSpace (UnitAddTorus ι)]
    (f : 𝓢(ι → ℝ, ℂ)) :
    ∑' q : ι → ℤ, multiEuclideanFourierCoefficient f q =
      ∑' z : ι → ℤ, f (fun i => (z i : ℝ)) := by
  obtain ⟨hglobal, hterm, hsum⟩ := poissonSchwartz_cell_domination f
  exact poissonSummation_schwartz_pi f hglobal hterm hsum

end FroehlichSpencer.BKT.Rotator

end
