/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Roughening.Theorem73
public import FroehlichSpencer.BKT.SOS.Roughening.Variance
public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerRoutineGraph
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Genuine probability and expectation carriers for the pinned SOS box. -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Source

open MeasureTheory ENNReal Filter Topology
open FroehlichSpencer.BKT.Generic.PinnedCharges
  (Site SquareZeroBond siteBoundaryDepth euclideanSiteDistance)
open FroehlichSpencer.BKT.SOS.Roughening

variable {L : ℕ}

private theorem sosHeightWeight_antitone_beta (L : ℕ) {β₁ β₂ : ℝ}
    (_hβ₁ : 0 ≤ β₁) (hβ₂ : β₁ ≤ β₂) (n : Site L → ℤ) :
    sosHeightWeight L β₂ n ≤ sosHeightWeight L β₁ n := by
  unfold sosHeightWeight
  rw [← Real.exp_sum, ← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  apply Finset.sum_le_sum
  intro e he
  have habs := abs_nonneg (pinnedGrad L (fun x => (n x : ℝ)) e)
  nlinarith

/-- The SOS partition sum converges for every positive inverse temperature. For `β ≤ 1` this is
the zero-tilt case of the Schwartz-comb summability theorem; for `β ≥ 1` compare termwise with
`β = 1`. -/
theorem sosHeightWeight_summable_all_beta (hL : 1 < L) {β : ℝ} (hβ : 0 < β) :
    Summable fun n : Site L → ℤ => sosHeightWeight L β n := by
  classical
  let x : Site L := (⟨0, by omega⟩, ⟨0, by omega⟩)
  by_cases hβ1 : β ≤ 1
  · have hs := summable_sosTilted hL hβ hβ1 x x (c := 0) (by
      rw [abs_zero]
      linarith)
    exact hs.congr fun n => by simp
  · have h1β : 1 ≤ β := le_of_not_ge hβ1
    have hsTilt := summable_sosTilted hL (by positivity : 0 < (1 : ℝ)) le_rfl x x
      (c := 0) (by rw [abs_zero]; norm_num)
    have hs : Summable fun n : Site L → ℤ => sosHeightWeight L 1 n := by
      simpa using hsTilt
    exact Summable.of_nonneg_of_le
      (fun n => (sosHeightWeight_pos L β n).le)
      (fun n => sosHeightWeight_antitone_beta L (by positivity) h1β n) hs

/-- The pinned SOS partition is a finite, strictly positive real number for every `β > 0`. -/
theorem sosPartition_finite_positive (hL : 1 < L) {β : ℝ} (hβ : 0 < β) :
    Summable (fun n : Site L → ℤ => sosHeightWeight L β n) ∧ 0 < sosPartition L β := by
  have hs := sosHeightWeight_summable_all_beta hL hβ
  constructor
  · exact hs
  · change 0 < ∑' n : Site L → ℤ, sosHeightWeight L β n
    exact hs.tsum_pos (fun n => (sosHeightWeight_pos L β n).le) 0
      (sosHeightWeight_pos L β 0)

/-- The pinned SOS law on heights, normalized by its finite positive partition function. -/
def sosLaw (_hL : 1 < L) (β : ℝ) (_hβ : 0 < β) : Measure (Site L → ℤ) :=
  Measure.sum fun n =>
    ENNReal.ofReal (sosHeightWeight L β n / sosPartition L β) • Measure.dirac n

/-- The extended moment-generating function of the height difference in the pinned SOS law. -/
def sosMomentExt (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (u v : Site L) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ n, ENNReal.ofReal (Real.exp (ε * ((n u : ℝ) - n v))) ∂sosLaw hL β hβ

/-- The Bochner expectation of the squared height difference in the pinned SOS law. -/
def sosVarianceIntegral (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (u v : Site L) : ℝ :=
  ∫ n, ((n u : ℝ) - n v) ^ 2 ∂sosLaw hL β hβ

theorem sosLaw_isProbabilityMeasure (hL : 1 < L) {β : ℝ} (hβ : 0 < β) :
    IsProbabilityMeasure (sosLaw hL β hβ) := by
  have hZ := (sosPartition_finite_positive hL hβ).2
  let c : (Site L → ℤ) → ℝ := fun n => sosHeightWeight L β n / sosPartition L β
  have hc : ∀ n, 0 ≤ c n := fun n => div_nonneg (sosHeightWeight_pos L β n).le hZ.le
  have hsumc : Summable c := by
    have hs := sosHeightWeight_summable_all_beta hL hβ
    have hs' := hs.mul_right (1 / sosPartition L β)
    simpa [c, div_eq_mul_inv] using hs'
  have htsumc : ∑' n, c n = 1 := by
    simp only [c, tsum_div_const, sosPartition]
    exact div_self hZ.ne'
  have hhas : HasSum c 1 := by
    rw [← htsumc]
    exact hsumc.hasSum
  change IsProbabilityMeasure (Measure.sum fun n =>
    ENNReal.ofReal (sosHeightWeight L β n / sosPartition L β) • Measure.dirac n)
  exact hhas.isProbabilityMeasure_sum_dirac hc

theorem sosLaw_apply_singleton (hL : 1 < L) {β : ℝ} (hβ : 0 < β)
    (n : Site L → ℤ) :
    sosLaw hL β hβ {n} = ENNReal.ofReal (sosHeightWeight L β n / sosPartition L β) := by
  rw [sosLaw, Measure.sum_smul_dirac_singleton]

theorem sosMomentExt_eq_tsum (hL : 1 < L) {β : ℝ} (hβ : 0 < β)
    (u v : Site L) (ε : ℝ) :
    sosMomentExt hL hβ u v ε =
      ∑' n : Site L → ℤ,
        ENNReal.ofReal (Real.exp (ε * ((n u : ℝ) - n v))) *
          ENNReal.ofReal (sosHeightWeight L β n / sosPartition L β) := by
  rw [sosMomentExt, sosLaw, MeasureTheory.lintegral_sum_measure]
  simp only [MeasureTheory.lintegral_smul_measure, MeasureTheory.lintegral_dirac,
    smul_eq_mul, mul_comm]

private theorem sosTiltedSummable_all_beta (hL : 1 < L) {β : ℝ} (hβ : 0 < β)
    (u v : Site L) {c : ℝ} (hc : |c| ≤ min β 1 / 2) :
    Summable fun n : Site L → ℤ =>
      Real.exp (c * ((n u : ℝ) - n v)) * sosHeightWeight L β n := by
  by_cases hβ1 : β ≤ 1
  · have hmin : min β 1 = β := min_eq_left hβ1
    have hc' : |c| ≤ β / 2 := by simpa [hmin] using hc
    exact summable_sosTilted hL hβ hβ1 u v hc'
  · have h1β : 1 ≤ β := le_of_not_ge hβ1
    have hmin : min β 1 = 1 := min_eq_right h1β
    have hc' : |c| ≤ (1 : ℝ) / 2 := by simpa [hmin] using hc
    have hs := summable_sosTilted hL (by positivity : 0 < (1 : ℝ)) le_rfl u v hc'
    exact Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Real.exp_pos _).le (sosHeightWeight_pos L β n).le)
      (fun n => mul_le_mul_of_nonneg_left
        (sosHeightWeight_antitone_beta L (by positivity) h1β n) (Real.exp_pos _).le) hs

theorem sosMomentExt_matches_sosMoment (hL : 1 < L) {β : ℝ} (hβ : 0 < β)
    (hβ1 : β ≤ 1) (u v : Site L) (ε : ℝ) (hε : |ε| ≤ β / 2) :
    sosMomentExt hL hβ u v ε = ENNReal.ofReal (sosMoment L β u v ε) := by
  have hZ := (sosPartition_finite_positive hL hβ).2
  let f : (Site L → ℤ) → ℝ := fun n =>
    Real.exp (ε * ((n u : ℝ) - n v)) * sosHeightWeight L β n / sosPartition L β
  have hf_nonneg : ∀ n, 0 ≤ f n := fun n => by
    dsimp [f]
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (sosHeightWeight_pos L β n).le) hZ.le
  have hf_sum : Summable f := by
    have hs := summable_sosTilted hL hβ hβ1 u v hε
    have hs' := hs.mul_right (1 / sosPartition L β)
    simpa [f, div_eq_mul_inv, mul_assoc] using hs'
  rw [sosMomentExt_eq_tsum]
  calc
    (∑' n : Site L → ℤ,
        ENNReal.ofReal (Real.exp (ε * ((n u : ℝ) - n v))) *
          ENNReal.ofReal (sosHeightWeight L β n / sosPartition L β))
        = ∑' n, ENNReal.ofReal (f n) := by
            apply tsum_congr
            intro n
            dsimp [f]
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
            congr 1
            field_simp
    _ = ENNReal.ofReal (∑' n, f n) :=
          (ENNReal.ofReal_tsum_of_nonneg hf_nonneg hf_sum).symm
    _ = ENNReal.ofReal (sosMoment L β u v ε) := by
          congr 1
          dsimp [f, sosMoment, sosTiltedSum]
          rw [tsum_div_const]

private theorem ennreal_ofReal_exp_rpow (x p : ℝ) (hp : 0 ≤ p) :
    ENNReal.ofReal (Real.exp x) ^ p = ENNReal.ofReal (Real.exp (p * x)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) hp]
  congr 1
  rw [← Real.exp_mul x p]
  ring_nf

theorem sosMomentExt_zero (hL : 1 < L) {β : ℝ} (hβ : 0 < β)
    (u v : Site L) : sosMomentExt hL hβ u v 0 = 1 := by
  have hμ := sosLaw_isProbabilityMeasure hL hβ
  simp [sosMomentExt, hμ.measure_univ]

theorem sosMomentExt_self (hL : 1 < L) {β : ℝ} (hβ : 0 < β)
    (u : Site L) (ε : ℝ) : sosMomentExt hL hβ u u ε = 1 := by
  have hμ := sosLaw_isProbabilityMeasure hL hβ
  simp [sosMomentExt, hμ.measure_univ]

theorem sosMomentExt_even (hL : 1 < L) {β : ℝ} (hβ : 0 < β)
    (u v : Site L) (ε : ℝ) :
    sosMomentExt hL hβ u v (-ε) = sosMomentExt hL hβ u v ε := by
  rw [sosMomentExt_eq_tsum, sosMomentExt_eq_tsum]
  calc
    (∑' n : Site L → ℤ,
        ENNReal.ofReal (Real.exp ((-ε) * ((n u : ℝ) - n v))) *
          ENNReal.ofReal (sosHeightWeight L β n / sosPartition L β)) =
      ∑' n : Site L → ℤ,
        ENNReal.ofReal (Real.exp ((-ε) * (((-n) u : ℝ) - (-n) v))) *
          ENNReal.ofReal (sosHeightWeight L β (-n) / sosPartition L β) := by
        symm
        exact (Equiv.neg (Site L → ℤ)).tsum_eq (fun n =>
          ENNReal.ofReal (Real.exp ((-ε) * ((n u : ℝ) - n v))) *
            ENNReal.ofReal (sosHeightWeight L β n / sosPartition L β))
    _ = ∑' n : Site L → ℤ,
        ENNReal.ofReal (Real.exp (ε * ((n u : ℝ) - n v))) *
          ENNReal.ofReal (sosHeightWeight L β n / sosPartition L β) := by
        apply tsum_congr
        intro n
        simp only [Pi.neg_apply, Int.cast_neg, sosHeightWeight_neg]
        congr 2
        ring_nf

theorem sosMomentExt_log_convex (hL : 1 < L) {β : ℝ} (hβ : 0 < β)
    (u v : Site L) (a b t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    sosMomentExt hL hβ u v ((1 - t) * a + t * b) ≤
      (sosMomentExt hL hβ u v a) ^ (1 - t) * (sosMomentExt hL hβ u v b) ^ t := by
  classical
  let μ := sosLaw hL β hβ
  let f : (Site L → ℤ) → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (Real.exp (a * ((n u : ℝ) - n v)))
  let g : (Site L → ℤ) → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (Real.exp (b * ((n u : ℝ) - n v)))
  have hf : AEMeasurable f μ := by fun_prop
  have hg : AEMeasurable g μ := by fun_prop
  have hpoint : ∀ n : Site L → ℤ,
      f n ^ (1 - t) * g n ^ t =
        ENNReal.ofReal (Real.exp (((1 - t) * a + t * b) * ((n u : ℝ) - n v))) := by
    intro n
    dsimp [f, g]
    rw [ennreal_ofReal_exp_rpow _ _ (sub_nonneg.mpr ht1),
      ennreal_ofReal_exp_rpow _ _ ht0]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 1
    ring_nf
  calc
    sosMomentExt hL hβ u v ((1 - t) * a + t * b) =
      ∫⁻ n, f n ^ (1 - t) * g n ^ t ∂μ := by
        rw [sosMomentExt]
        apply lintegral_congr
        intro n
        exact (hpoint n).symm
    _ ≤ (∫⁻ n, f n ∂μ) ^ (1 - t) * (∫⁻ n, g n ∂μ) ^ t :=
      lintegral_mul_norm_pow_le hf hg (sub_nonneg.mpr ht1) ht0 (by ring)
    _ = (sosMomentExt hL hβ u v a) ^ (1 - t) *
        (sosMomentExt hL hβ u v b) ^ t := by
          simp [f, g, sosMomentExt, μ]

private def sosRaisedHeight (u : Site L) (k : ℕ) : Site L → ℤ :=
  fun x => if x = u then (k : ℤ) else 0

private theorem pinnedGrad_sosRaisedHeight_abs (u : Site L) (k : ℕ)
    (e : SquareZeroBond L) :
    |pinnedGrad L (fun x => ((sosRaisedHeight u k x : ℤ) : ℝ)) e| =
      if (squareZero L).src e = some u ∨ (squareZero L).tgt e = some u
      then (k : ℝ) else 0 := by
  classical
  rw [pinnedGrad_apply]
  cases e with
  | inl e =>
      have hend : e.1.1 ≠ e.1.2 := by
        intro h
        have hlt : toLex e.1.1 < toLex e.1.1 := by simpa [h] using e.2.1
        exact (lt_irrefl _ hlt)
      have hsrc : (squareZero L).src (Sum.inl e) = some e.1.1 := rfl
      have htgt : (squareZero L).tgt (Sum.inl e) = some e.1.2 := rfl
      simp only [hsrc, htgt, Multigraph.grad, pinnedField]
      by_cases hs : e.1.1 = u
      · have ht : e.1.2 ≠ u := by
          intro h
          exact hend (hs.trans h.symm)
        simp [sosRaisedHeight, hs, ht]
      · by_cases ht : e.1.2 = u
        · simp [sosRaisedHeight, hs, ht]
        · simp [sosRaisedHeight, hs, ht]
  | inr b =>
      rcases b with ⟨j, q⟩
      have hsrc : (squareZero L).src (Sum.inr ⟨j, q⟩) = some j := rfl
      have htgt : (squareZero L).tgt (Sum.inr ⟨j, q⟩) = none := rfl
      simp only [hsrc, htgt, Multigraph.grad, pinnedField]
      by_cases hj : j = u
      · simp [sosRaisedHeight, hj]
      · simp [sosRaisedHeight, hj]

private theorem sosHeightWeight_raised_lower {β : ℝ} (hβ : 0 < β)
    (u : Site L) (k : ℕ) :
    Real.exp (-(4 * β * (k : ℝ))) ≤ sosHeightWeight L β (sosRaisedHeight u k) := by
  classical
  let S := Finset.univ.filter fun e : SquareZeroBond L =>
    (squareZero L).src e = some u ∨ (squareZero L).tgt e = some u
  have hcard : S.card ≤ 4 := by
    simpa [S] using
      (FroehlichSpencer.BKT.Generic.PinnedCharges.Layer.card_incident_le_four (L := L) u)
  have hprod : sosHeightWeight L β (sosRaisedHeight u k) =
      ∏ e ∈ S, Real.exp (-(β * (k : ℝ))) := by
    unfold sosHeightWeight
    rw [← Finset.prod_subset (Finset.subset_univ S) (fun e _ he => ?_)]
    · apply Finset.prod_congr rfl
      intro e he
      have hincident : (squareZero L).src e = some u ∨ (squareZero L).tgt e = some u :=
        (Finset.mem_filter.mp he).2
      rw [pinnedGrad_sosRaisedHeight_abs]
      simp [hincident]
    · have hnot : ¬((squareZero L).src e = some u ∨ (squareZero L).tgt e = some u) := by
        simpa [S] using he
      rw [pinnedGrad_sosRaisedHeight_abs]
      simp [hnot]
  rw [hprod]
  have hbase : Real.exp (-(β * (k : ℝ))) ^ 4 ≤
      Real.exp (-(β * (k : ℝ))) ^ S.card := by
    rw [← Real.exp_nat_mul (-(β * (k : ℝ))) S.card,
      ← Real.exp_nat_mul (-(β * (k : ℝ))) 4]
    apply Real.exp_le_exp.mpr
    push_cast
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hcardR : (S.card : ℝ) ≤ 4 := by exact_mod_cast hcard
    have hmul := mul_le_mul_of_nonneg_left hcardR (mul_nonneg hβ.le hk)
    nlinarith
  have hbase' : Real.exp (-(β * (k : ℝ))) ^ 4 =
      Real.exp (-(4 * β * (k : ℝ))) := by
    rw [← Real.exp_nat_mul (-(β * (k : ℝ))) 4]
    congr 1
    ring
  have hprodPow : (∏ e ∈ S, Real.exp (-(β * (k : ℝ)))) =
      Real.exp (-(β * (k : ℝ))) ^ S.card := by simp
  rw [hprodPow, ← hbase']
  exact hbase

private theorem sosMomentExt_eq_top_of_nonneg_four_beta (hL : 1 < L) {β : ℝ}
    (hβ : 0 < β) (u v : Site L) (huv : u ≠ v) (ε : ℝ)
    (hεlarge : 4 * β ≤ ε) : sosMomentExt hL hβ u v ε = ⊤ := by
  rw [sosMomentExt_eq_tsum]
  let nK : ℕ → Site L → ℤ := fun k => sosRaisedHeight u k
  let c : ℝ≥0∞ := ENNReal.ofReal (1 / sosPartition L β)
  let F : (Site L → ℤ) → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (Real.exp (ε * ((n u : ℝ) - n v))) *
      ENNReal.ofReal (sosHeightWeight L β n / sosPartition L β)
  have hZ : 0 < sosPartition L β := (sosPartition_finite_positive hL hβ).2
  have hnK_inj : Function.Injective nK := by
    intro k j h
    have hval := congrFun h u
    simp [nK, sosRaisedHeight] at hval
    exact_mod_cast hval
  have hnKu (k : ℕ) : nK k u = (k : ℤ) := by simp [nK, sosRaisedHeight]
  have hvu : v ≠ u := fun h => huv h.symm
  have hnKv (k : ℕ) : nK k v = 0 := by simp [nK, sosRaisedHeight, hvu]
  have hw (k : ℕ) : Real.exp (-(4 * β * (k : ℝ))) ≤ sosHeightWeight L β (nK k) := by
    simpa [nK] using sosHeightWeight_raised_lower hβ u k
  have hterm : ∀ k : ℕ, c ≤ F (nK k) := by
    intro k
    have hnum : 1 ≤
        Real.exp (ε * (k : ℝ)) * sosHeightWeight L β (nK k) := by
      have hlow : 1 ≤ Real.exp ((ε - 4 * β) * (k : ℝ)) :=
        Real.one_le_exp (mul_nonneg (sub_nonneg.mpr hεlarge) (Nat.cast_nonneg k))
      have hexp : Real.exp ((ε - 4 * β) * (k : ℝ)) =
          Real.exp (ε * (k : ℝ)) * Real.exp (-(4 * β * (k : ℝ))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        1 ≤ Real.exp ((ε - 4 * β) * (k : ℝ)) := hlow
        _ = Real.exp (ε * (k : ℝ)) * Real.exp (-(4 * β * (k : ℝ))) := hexp
        _ ≤ Real.exp (ε * (k : ℝ)) * sosHeightWeight L β (nK k) :=
          mul_le_mul_of_nonneg_left (hw k) (Real.exp_pos _).le
    have hquot : 1 / sosPartition L β ≤
        Real.exp (ε * (k : ℝ)) *
          (sosHeightWeight L β (nK k) / sosPartition L β) := by
      calc
        1 / sosPartition L β ≤
            (Real.exp (ε * (k : ℝ)) * sosHeightWeight L β (nK k)) /
              sosPartition L β := div_le_div_of_nonneg_right hnum hZ.le
        _ = _ := by ring
    dsimp [c, F]
    rw [hnKu k, hnKv k]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    simpa using hquot
  have hcpos : 0 < c := by
    dsimp [c]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hconst : ∑' k : ℕ, c = ⊤ := by
    rw [ENNReal.tsum_const]
    simp [hcpos.ne']
  have htop : ∑' n : Site L → ℤ, F n = ⊤ := by
    apply top_le_iff.mp
    calc
      ⊤ = ∑' k : ℕ, c := hconst.symm
      _ ≤ ∑' k : ℕ, F (nK k) := ENNReal.tsum_le_tsum hterm
      _ ≤ ∑' n : Site L → ℤ, F n :=
        ENNReal.tsum_comp_le_tsum_of_injective hnK_inj F
  simpa [F] using htop


theorem sosMomentExt_eq_top_of_abs_ge_four_beta (hL : 1 < L) {β : ℝ}
    (hβ : 0 < β) (u v : Site L) (huv : u ≠ v) {ε : ℝ}
    (hε : 4 * β ≤ |ε|) : sosMomentExt hL hβ u v ε = ⊤ := by
  by_cases hpos : 0 ≤ ε
  · exact sosMomentExt_eq_top_of_nonneg_four_beta hL hβ u v huv ε
      (by simpa [abs_of_nonneg hpos] using hε)
  · have hneg : 0 ≤ -ε := by linarith
    have hlarge : 4 * β ≤ -ε := by
      simpa [abs_of_neg (lt_of_not_ge hpos)] using hε
    have htop := sosMomentExt_eq_top_of_nonneg_four_beta hL hβ u v huv (-ε) hlarge
    calc
      sosMomentExt hL hβ u v ε = sosMomentExt hL hβ u v (-ε) :=
        (sosMomentExt_even hL hβ u v ε).symm
      _ = ⊤ := htop

private theorem sosTiltedSummable_plusminus (hL : 1 < L) {β : ℝ} (hβ : 0 < β)
    (u v : Site L) :
    ∃ δ : ℝ, 0 < δ ∧
      Summable (fun n : Site L → ℤ => Real.exp (δ * ((n u : ℝ) - n v)) * sosHeightWeight L β n) ∧
      Summable (fun n : Site L → ℤ => Real.exp (-δ * ((n u : ℝ) - n v)) * sosHeightWeight L β n) := by
  let δ := min β 1 / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_, ?_⟩
  · exact sosTiltedSummable_all_beta hL hβ u v (c := δ) (by
      rw [abs_of_pos hδ])
  · exact sosTiltedSummable_all_beta hL hβ u v (c := -δ) (by
      rw [abs_neg, abs_of_pos hδ])

theorem sosVarianceIntegral_integrable (hL : 1 < L) {β : ℝ} (hβ : 0 < β)
    (u v : Site L) :
    Integrable (fun n : Site L → ℤ => ((n u : ℝ) - n v) ^ 2) (sosLaw hL β hβ) := by
  obtain ⟨δ, hδ, hsplus, hsminus⟩ := sosTiltedSummable_plusminus hL hβ u v
  let η := δ / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have h2η : 2 * η = δ := by dsimp [η]; ring
  have hsExp : Summable fun n : Site L → ℤ =>
      (Real.exp (δ * ((n u : ℝ) - n v)) +
        Real.exp (-δ * ((n u : ℝ) - n v))) * sosHeightWeight L β n := by
    have h1 := hsplus.add hsminus
    exact h1.congr fun n => by ring
  let bound : (Site L → ℤ) → ℝ := fun n => 2 / η ^ 2 *
      ((Real.exp (δ * ((n u : ℝ) - n v)) +
        Real.exp (-δ * ((n u : ℝ) - n v))) * sosHeightWeight L β n)
  have hboundSum : Summable bound := by
    dsimp [bound]
    exact hsExp.mul_left _
  have hsqSum : Summable fun n : Site L → ℤ =>
      ((n u : ℝ) - n v) ^ 2 * sosHeightWeight L β n := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (sq_nonneg _) (sosHeightWeight_pos L β n).le)
      (fun n => ?_) hboundSum
    have hx := sq_mul_exp_abs_le hη ((n u : ℝ) - n v)
    rw [h2η] at hx
    have hexp : 1 ≤ Real.exp (η * |((n u : ℝ) - n v)|) :=
      Real.one_le_exp (mul_nonneg hη.le (abs_nonneg _))
    have hmul := mul_le_mul_of_nonneg_left hexp (sq_nonneg ((n u : ℝ) - n v))
    have hstep : ((n u : ℝ) - n v) ^ 2 ≤
        2 / η ^ 2 * (Real.exp (δ * ((n u : ℝ) - n v)) +
          Real.exp (-δ * ((n u : ℝ) - n v))) := by
      simpa using hmul.trans hx
    calc
      ((n u : ℝ) - n v) ^ 2 * sosHeightWeight L β n ≤
          (2 / η ^ 2 * (Real.exp (δ * ((n u : ℝ) - n v)) +
            Real.exp (-δ * ((n u : ℝ) - n v)))) * sosHeightWeight L β n :=
        mul_le_mul_of_nonneg_right hstep (sosHeightWeight_pos L β n).le
      _ = bound n := by dsimp [bound]; ring
  have hZ := (sosPartition_finite_positive hL hβ).2
  let coeff : (Site L → ℤ) → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (sosHeightWeight L β n / sosPartition L β)
  have hcoeffFinite : ∀ n, coeff n ≠ ∞ := by
    intro n
    simp [coeff]
  have hnormSum : Summable fun n : Site L → ℤ =>
      (sosHeightWeight L β n / sosPartition L β) *
        ‖((n u : ℝ) - n v) ^ 2‖ := by
    have hs := hsqSum.mul_right (1 / sosPartition L β)
    have hrewrite : (fun n : Site L → ℤ =>
        (sosHeightWeight L β n / sosPartition L β) *
          ‖((n u : ℝ) - n v) ^ 2‖) =
      fun n => (((n u : ℝ) - n v) ^ 2 * sosHeightWeight L β n) /
        sosPartition L β := by
      funext n
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      ring
    rw [hrewrite]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hs
  rw [sosLaw]
  apply (integrable_sum_dirac_iff hcoeffFinite).2
  have hconvert :
      (fun n : Site L → ℤ => (coeff n).toReal *
        ‖((n u : ℝ) - n v) ^ 2‖) =
        fun n => (sosHeightWeight L β n / sosPartition L β) *
          ‖((n u : ℝ) - n v) ^ 2‖ := by
    funext n
    simp [coeff, ENNReal.toReal_ofReal, div_nonneg (sosHeightWeight_pos L β n).le hZ.le]
  rw [hconvert]
  exact hnormSum

theorem sosVarianceIntegral_eq_sosVariance (hL : 1 < L) {β : ℝ} (hβ : 0 < β)
    (u v : Site L) :
    sosVarianceIntegral hL hβ u v = sosVariance L β u v := by
  have hint := sosVarianceIntegral_integrable hL hβ u v
  have hZ := (sosPartition_finite_positive hL hβ).2
  let coeff : (Site L → ℤ) → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (sosHeightWeight L β n / sosPartition L β)
  have hc : ∀ n, coeff n ≠ ∞ := by intro n; simp [coeff]
  rw [sosVarianceIntegral, sosLaw,
    integral_sum_dirac_eq_tsum hc ((integrable_sum_dirac_iff hc).1 hint)]
  unfold sosVariance
  calc
    (∑' n : Site L → ℤ,
        (coeff n).toReal • ((n u : ℝ) - n v) ^ 2) =
      ∑' n, (((n u : ℝ) - n v) ^ 2 * sosHeightWeight L β n) /
        sosPartition L β := by
          apply tsum_congr
          intro n
          change (ENNReal.ofReal (sosHeightWeight L β n / sosPartition L β)).toReal •
              ((n u : ℝ) - n v) ^ 2 =
            (((n u : ℝ) - n v) ^ 2 * sosHeightWeight L β n) / sosPartition L β
          rw [ENNReal.toReal_ofReal
            (div_nonneg (sosHeightWeight_pos L β n).le hZ.le)]
          simp only [smul_eq_mul]
          ring
    _ = (∑' n : Site L → ℤ,
        ((n u : ℝ) - n v) ^ 2 * sosHeightWeight L β n) / sosPartition L β := by
          rw [tsum_div_const]

end FroehlichSpencer.BKT.SOS.Source

end
