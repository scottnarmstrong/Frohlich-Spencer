/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.LatticeSchwartzSummability
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Topology.Algebra.Group.Quotient

/-! # Locally uniform lattice periodization of finite-dimensional Schwartz functions -/

@[expose] public section

open Complex MeasureTheory TopologicalSpace
open scoped SchwartzMap BigOperators
noncomputable section

namespace FroehlichSpencer.BKT.Rotator

noncomputable def schwartzLatticeShift {ι : Type*} [Fintype ι] (f : 𝓢(ι → ℝ, ℂ))
    (q : ι → ℤ) : C(ι → ℝ, ℂ) :=
  ⟨fun x => f (x + fun i => (q i : ℝ)),
   f.continuous.comp (continuous_id.add continuous_const)⟩

theorem schwartzLatticeShifts_locally_summable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : 𝓢(ι → ℝ, ℂ)) (K : Compacts (ι → ℝ)) :
    Summable fun q : ι → ℤ => ‖(schwartzLatticeShift f q).restrict K‖ := by
  classical
  let N : ℕ := 2 * Fintype.card ι
  obtain ⟨C0, h0⟩ := f.decay' 0 0
  obtain ⟨C, hN⟩ := f.decay' N 0
  have h0fun (y : ι → ℝ) : ‖f y‖ ≤ C0 := by
    have h := h0 y
    change ‖f.toFun y‖ ≤ C0
    simpa only [norm_iteratedFDeriv_zero, pow_zero, one_mul] using h
  have hNfun (y : ι → ℝ) : ‖y‖ ^ N * ‖f y‖ ≤ C := by
    have h := hN y
    change ‖y‖ ^ N * ‖f.toFun y‖ ≤ C
    simpa only [norm_iteratedFDeriv_zero] using h
  have hC0 : 0 ≤ C0 := (norm_nonneg (f 0)).trans (h0fun 0)
  have hC : 0 ≤ C := by
    by_cases hNzero : N = 0
    · have h := hNfun 0
      exact (norm_nonneg (f 0)).trans (by simpa [hNzero] using h)
    · have h := hNfun 0
      simpa [hNzero] using h
  let M : ℝ := max (C0 * 2 ^ N) (C * 2 ^ N)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hdecay (y : ι → ℝ) : ‖f y‖ * (1 + ‖y‖) ^ N ≤ M := by
    by_cases hy : ‖y‖ ≤ 1
    · have hpow : (1 + ‖y‖) ^ N ≤ 2 ^ N := by gcongr; linarith
      calc
        ‖f y‖ * (1 + ‖y‖) ^ N ≤ C0 * 2 ^ N := mul_le_mul (h0fun y) hpow (by positivity) (by positivity)
        _ ≤ M := le_max_left _ _
    · have hy1 : 1 ≤ ‖y‖ := le_of_not_ge hy
      have hpow : (1 + ‖y‖) ^ N ≤ 2 ^ N * ‖y‖ ^ N := by
        have h : 1 + ‖y‖ ≤ 2 * ‖y‖ := by linarith
        calc _ ≤ (2 * ‖y‖) ^ N := by gcongr
             _ = _ := by rw [mul_pow]
      calc
        ‖f y‖ * (1 + ‖y‖) ^ N ≤ ‖f y‖ * (2 ^ N * ‖y‖ ^ N) := mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        _ = 2 ^ N * (‖y‖ ^ N * ‖f y‖) := by ring
        _ ≤ C * 2 ^ N := by
          rw [mul_comm (2 ^ N) (‖y‖ ^ N * ‖f y‖)]
          exact mul_le_mul_of_nonneg_right (hNfun y) (by positivity)
        _ ≤ M := le_max_right _ _
  obtain ⟨r, hr⟩ := K.isCompact.isBounded.subset_closedBall (0 : ι → ℝ)
  let R : ℝ := max r 0
  have hR : 0 ≤ R := le_max_right _ _
  have hKR (x : K) : ‖(x : ι → ℝ)‖ ≤ R := by
    have hx := hr x.2
    have hx' : dist (x : ι → ℝ) 0 ≤ r := by simpa [Metric.mem_closedBall] using hx
    have hnorm : ‖(x : ι → ℝ)‖ ≤ r := by simpa [dist_eq_norm] using hx'
    exact hnorm.trans (le_max_left _ _)
  let P (q : ι → ℤ) : ℝ := ∏ i : ι, (1 + |(q i : ℝ)|) ^ 2
  have hPpos (q : ι → ℤ) : 0 < P q := by
    dsimp [P]
    exact Finset.prod_pos fun i hi => by positivity
  have hPbound (q : ι → ℤ) : P q ≤ (1 + ‖fun i => (q i : ℝ)‖) ^ N := by
    dsimp [P, N]
    calc
      ∏ i : ι, (1 + |(q i : ℝ)|) ^ 2 ≤
          ∏ i : ι, (1 + ‖fun j => (q j : ℝ)‖) ^ 2 := by
            apply prod_mono_nonneg_real
            · intro j hj; positivity
            · intro j hj
              have := (pi_norm_le_iff_of_nonneg (norm_nonneg (fun j => (q j : ℝ)))).mp le_rfl j
              have hcoord : |(q j : ℝ)| ≤ ‖fun j => (q j : ℝ)‖ := by
                rw [← Real.norm_eq_abs]
                exact this
              gcongr
      _ = (1 + ‖fun i => (q i : ℝ)‖) ^ (2 * Fintype.card ι) := by simp [Finset.prod_const, pow_mul]
  have hmajor (q : ι → ℤ) : ‖(schwartzLatticeShift f q).restrict K‖ ≤ M * (1 + R) ^ N * (∏ i : ι, latticePhi (q i)) := by
    have hmajor_nonneg : 0 ≤ M * (1 + R) ^ N * (∏ i : ι, latticePhi (q i)) :=
      mul_nonneg (mul_nonneg hM (by positivity))
        (Finset.prod_nonneg fun i hi => latticePhi_nonneg _)
    rw [ContinuousMap.norm_le _ hmajor_nonneg]
    intro x
    rw [ContinuousMap.restrict_apply]
    let u : ι → ℝ := fun i => (q i : ℝ)
    let y : ι → ℝ := (x : ι → ℝ) + u
    have htri : 1 + ‖u‖ ≤ (1 + R) * (1 + ‖y‖) := by
      have hu : ‖u‖ ≤ ‖y‖ + R := by
        calc
          ‖u‖ = ‖y - (x : ι → ℝ)‖ := by congr 1; ext i; simp [y, u]
          _ ≤ ‖y‖ + ‖(x : ι → ℝ)‖ := norm_sub_le _ _
          _ ≤ ‖y‖ + R := by gcongr; exact hKR x
      nlinarith [norm_nonneg y, hR]
    have hP := hPbound q
    have hP' : P q ≤ (1 + R) ^ N * (1 + ‖y‖) ^ N := by
      calc
        P q ≤ (1 + ‖u‖) ^ N := by simpa [u] using hP
        _ ≤ ((1 + R) * (1 + ‖y‖)) ^ N := by gcongr
        _ = (1 + R) ^ N * (1 + ‖y‖) ^ N := by rw [mul_pow]
    have hmul : ‖f y‖ * P q ≤ M * (1 + R) ^ N := by
      calc
        ‖f y‖ * P q ≤ ‖f y‖ * ((1 + R) ^ N * (1 + ‖y‖) ^ N) :=
          mul_le_mul_of_nonneg_left hP' (norm_nonneg _)
        _ = (1 + R) ^ N * (‖f y‖ * (1 + ‖y‖) ^ N) := by ring
        _ ≤ (1 + R) ^ N * M := mul_le_mul_of_nonneg_left (hdecay y) (by positivity)
        _ = M * (1 + R) ^ N := by ring
    have hpoint : ‖f y‖ ≤ M * (1 + R) ^ N / P q := by
      apply (le_div_iff₀ (hPpos q)).2
      simpa [mul_comm] using hmul
    have hphi : (∏ i : ι, latticePhi (q i)) = (P q)⁻¹ := by
      dsimp [P, latticePhi]
      rw [← Finset.prod_inv_distrib]
      congr 1
      funext i
      ring
    rw [schwartzLatticeShift]
    change ‖f y‖ ≤ _
    rw [hphi]
    simpa [div_eq_mul_inv] using hpoint
  have hg : Summable (fun q : ι → ℤ => M * (1 + R) ^ N * ∏ i : ι, latticePhi (q i)) :=
    (summable_pi_prod_phi (ι := ι)).mul_left (M * (1 + R) ^ N)
  exact Summable.of_norm_bounded hg (fun q => by simpa using hmajor q)

/-- The sum of all integer translates of a Schwartz function, as a continuous function in the
compact-open topology. -/
noncomputable def schwartzLatticePeriodization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : 𝓢(ι → ℝ, ℂ)) : C(ι → ℝ, ℂ) :=
  ∑' q : ι → ℤ, schwartzLatticeShift f q

theorem schwartzLatticePeriodization_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : 𝓢(ι → ℝ, ℂ)) (x : ι → ℝ) :
    schwartzLatticePeriodization f x =
      ∑' q : ι → ℤ, f (x + fun i => (q i : ℝ)) := by
  symm
  exact ContinuousMap.tsum_apply
    (ContinuousMap.summable_of_locally_summable_norm
      (schwartzLatticeShifts_locally_summable f)) x

/-- Translating the argument by an integer vector only reindexes the lattice periodization. -/
theorem schwartzLatticePeriodization_periodic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : 𝓢(ι → ℝ, ℂ)) (x : ι → ℝ) (z : ι → ℤ) :
    schwartzLatticePeriodization f (x + fun i => (z i : ℝ)) =
      schwartzLatticePeriodization f x := by
  rw [schwartzLatticePeriodization_apply, schwartzLatticePeriodization_apply]
  let g : (ι → ℤ) → ℂ := fun q => f (x + fun i => (q i : ℝ))
  have h := (Equiv.addLeft z).tsum_eq g
  calc
    (∑' q : ι → ℤ, f (x + (fun i => (z i : ℝ)) + fun i => (q i : ℝ))) =
        ∑' q : ι → ℤ, g (z + q) := by
          apply tsum_congr
          intro q
          unfold g
          congr 1
          funext i
          simp [Pi.add_apply, Int.cast_add, add_assoc]
    _ = ∑' q : ι → ℤ, g q := h
    _ = ∑' q : ι → ℤ, f (x + fun i => (q i : ℝ)) := by rfl

/-- The coordinatewise quotient map from Euclidean coordinate space to the finite product torus. -/
def latticeTorusQuotientMap {ι : Type*} (x : ι → ℝ) : UnitAddTorus ι :=
  fun i => (x i : UnitAddCircle)

theorem latticeTorusQuotientMap_isOpenQuotientMap {ι : Type*} :
    IsOpenQuotientMap (latticeTorusQuotientMap (ι := ι)) := by
  have h1 : IsOpenQuotientMap (fun x : ℝ => (x : UnitAddCircle)) := by
    change IsOpenQuotientMap
      (QuotientAddGroup.mk : ℝ → ℝ ⧸ AddSubgroup.zmultiples (1 : ℝ))
    exact QuotientAddGroup.isOpenQuotientMap_mk
  change IsOpenQuotientMap
    (Pi.map (fun _ : ι => (fun x : ℝ => (x : UnitAddCircle))))
  exact IsOpenQuotientMap.piMap (fun i : ι => h1)

/-- A periodized Schwartz function has the same value on any two representatives of a torus point. -/
theorem schwartzLatticePeriodization_eq_of_torus_eq {ι : Type*} [Fintype ι]
    [DecidableEq ι] (f : 𝓢(ι → ℝ, ℂ)) {x y : ι → ℝ}
    (h : latticeTorusQuotientMap x = latticeTorusQuotientMap y) :
    schwartzLatticePeriodization f x = schwartzLatticePeriodization f y := by
  classical
  have hcoord : ∀ i, ∃ n : ℤ, x i - y i = (n : ℝ) := by
    intro i
    have hc : (x i : UnitAddCircle) = (y i : UnitAddCircle) := congrFun h i
    have hzero : ((x i - y i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, hc]
      simp
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
    exact ⟨n, by simpa using hn.symm⟩
  choose n hn using hcoord
  have hxy : x = y + fun i => (n i : ℝ) := by
    funext i
    have hi := hn i
    change x i = y i + (n i : ℝ)
    linarith
  rw [hxy]
  exact schwartzLatticePeriodization_periodic f y n

/-- The continuous periodization of a Schwartz function on the finite product torus. -/
noncomputable def schwartzTorusPeriodization {ι : Type*} [Fintype ι]
    [DecidableEq ι] (f : 𝓢(ι → ℝ, ℂ)) : C(UnitAddTorus ι, ℂ) := by
  classical
  let hq := latticeTorusQuotientMap_isOpenQuotientMap (ι := ι)
  let P : UnitAddTorus ι → ℂ := fun t =>
    schwartzLatticePeriodization f (Classical.choose (hq.surjective t))
  have hcomp : P ∘ latticeTorusQuotientMap = schwartzLatticePeriodization f := by
    funext x
    dsimp [P]
    apply schwartzLatticePeriodization_eq_of_torus_eq f
    exact hq.surjective (latticeTorusQuotientMap x) |>.choose_spec
  have hcont : Continuous P := by
    apply hq.continuous_comp_iff.mp
    simpa [hcomp] using (schwartzLatticePeriodization f).continuous
  exact ⟨P, hcont⟩

theorem schwartzTorusPeriodization_coe {ι : Type*} [Fintype ι]
    [DecidableEq ι] (f : 𝓢(ι → ℝ, ℂ)) (x : ι → ℝ) :
    schwartzTorusPeriodization f (latticeTorusQuotientMap x) =
      schwartzLatticePeriodization f x := by
  classical
  unfold schwartzTorusPeriodization
  simp only [ContinuousMap.coe_mk]
  let hq := latticeTorusQuotientMap_isOpenQuotientMap (ι := ι)
  apply schwartzLatticePeriodization_eq_of_torus_eq f
  exact hq.surjective (latticeTorusQuotientMap x) |>.choose_spec

theorem schwartzTorusPeriodization_zero {ι : Type*} [Fintype ι]
    [DecidableEq ι] (f : 𝓢(ι → ℝ, ℂ)) :
    schwartzTorusPeriodization f 0 =
      ∑' q : ι → ℤ, f (fun i => (q i : ℝ)) := by
  have hz : latticeTorusQuotientMap (0 : ι → ℝ) = (0 : UnitAddTorus ι) := by
    ext i
    simp [latticeTorusQuotientMap]
  rw [← hz, schwartzTorusPeriodization_coe f (0 : ι → ℝ)]
  rw [schwartzLatticePeriodization_apply]
  simp

end FroehlichSpencer.BKT.Rotator

end
