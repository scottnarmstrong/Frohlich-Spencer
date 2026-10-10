/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Roughening.Theorem73
public import FroehlichSpencer.BKT.SOS.Roughening.Variance

/-! # Integrability of the pinned SOS second moment

The contour estimate uses the normalized second moment `sosVariance`. This module first records
that its numerator is a genuine summable expectation for every positive inverse temperature.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Peierls

open FroehlichSpencer.BKT.Generic.PinnedCharges (Site)
open FroehlichSpencer.BKT.SOS.Roughening

variable {L : ℕ}

/-- The second-moment numerator is summable in every finite pinned box at positive β. -/
theorem summable_sosSecondMoment (hL : 1 < L) {β : ℝ} (hβ : 0 < β)
    (u v : Site L) :
    Summable fun n : Site L → ℤ =>
      (((n u : ℝ) - n v) ^ 2) * sosHeightWeight L β n := by
  let X : (Site L → ℤ) → ℝ := fun n => (n u : ℝ) - n v
  have hmoment (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
      Summable fun n : Site L → ℤ => (X n) ^ 2 * sosHeightWeight L b n := by
    let δ := b / 8
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hcoef : 0 ≤ 2 / δ ^ 2 := by positivity
    have hplus : |2 * δ| ≤ b / 2 := by
      rw [abs_of_nonneg (by positivity)]
      dsimp [δ]
      nlinarith
    have hminus : |- (2 * δ)| ≤ b / 2 := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
      dsimp [δ]
      nlinarith
    have hsplus := summable_sosTilted hL hb hb1 u v (c := 2 * δ) hplus
    have hsminus := summable_sosTilted hL hb hb1 u v (c := -(2 * δ)) hminus
    have hplus' : Summable fun n : Site L → ℤ => Real.exp (2 * δ * X n) *
        sosHeightWeight L b n := by
      simpa [X] using hsplus
    have hminus' : Summable fun n : Site L → ℤ => Real.exp (-(2 * δ) * X n) *
        sosHeightWeight L b n := by
      simpa [X] using hsminus
    have hbound (n : Site L → ℤ) :
        (X n) ^ 2 * sosHeightWeight L b n ≤
          (2 / δ ^ 2) *
            (Real.exp (2 * δ * X n) * sosHeightWeight L b n +
             Real.exp (-(2 * δ) * X n) * sosHeightWeight L b n) := by
      have h := sq_mul_exp_abs_le hδ (X n)
      have hexp : 1 ≤ Real.exp (δ * |X n|) := Real.one_le_exp (mul_nonneg hδ.le (abs_nonneg _))
      have hsq : (X n) ^ 2 ≤ (X n) ^ 2 * Real.exp (δ * |X n|) :=
        le_mul_of_one_le_right (sq_nonneg _) hexp
      have h' : (X n) ^ 2 ≤ 2 / δ ^ 2 *
          (Real.exp (2 * δ * X n) + Real.exp (-(2 * δ) * X n)) := hsq.trans h
      have hw := sosHeightWeight_pos L b n
      have h'' := mul_le_mul_of_nonneg_right h' hw.le
      nlinarith [h'']
    have hsum := Summable.mul_left (2 / δ ^ 2) (hplus'.add hminus')
    exact hsum.of_nonneg_of_le (fun n =>
      mul_nonneg (sq_nonneg (X n)) (sosHeightWeight_pos L b n).le) hbound
  by_cases hb1 : β ≤ 1
  · exact hmoment β hβ hb1
  · have hbase := hmoment 1 (by norm_num) (by norm_num)
    have hmono (n : Site L → ℤ) : sosHeightWeight L β n ≤ sosHeightWeight L 1 n := by
      unfold sosHeightWeight
      apply Finset.prod_le_prod₀
      · intro e he
        exact (Real.exp_pos _).le
      · intro e he
        apply Real.exp_le_exp.mpr
        have hβ' : 1 ≤ β := le_of_not_ge hb1
        have habs := abs_nonneg (pinnedGrad L (fun x => (n x : ℝ)) e)
        have hmul := mul_le_mul_of_nonneg_right hβ' habs
        nlinarith
    refine hbase.of_nonneg_of_le
      (fun n => mul_nonneg (sq_nonneg (X n)) (sosHeightWeight_pos L β n).le)
      (fun n => ?_)
    exact mul_le_mul_of_nonneg_left (hmono n) (sq_nonneg (X n))

/-- The partition sum is finite at every positive inverse temperature. -/
theorem summable_sosPartition (hL : 1 < L) {β : ℝ} (hβ : 0 < β) :
    Summable fun n : Site L → ℤ => sosHeightWeight L β n := by
  let u : Site L := (⟨0, by omega⟩, ⟨0, by omega⟩)
  by_cases hb1 : β ≤ 1
  · have h := summable_sosTilted hL hβ hb1 u u (c := 0) (by simp; positivity)
    exact h.congr fun n => by simp
  · have hbase0 := summable_sosTilted hL (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (1 : ℝ) ≤ 1) u u (c := 0) (by simp)
    have hbase : Summable fun n : Site L → ℤ => sosHeightWeight L 1 n :=
      hbase0.congr fun n => by simp
    have hmono (n : Site L → ℤ) : sosHeightWeight L β n ≤ sosHeightWeight L 1 n := by
      unfold sosHeightWeight
      apply Finset.prod_le_prod₀
      · intro e he
        exact (Real.exp_pos _).le
      · intro e he
        apply Real.exp_le_exp.mpr
        have hβ' : 1 ≤ β := le_of_not_ge hb1
        have habs := abs_nonneg (pinnedGrad L (fun x => (n x : ℝ)) e)
        have hmul := mul_le_mul_of_nonneg_right hβ' habs
        nlinarith
    refine hbase.of_nonneg_of_le (fun n => (sosHeightWeight_pos L β n).le) hmono

/-- Positivity of the partition sum, with its finiteness made explicit. -/
theorem sosPartition_pos_of_summable (L : ℕ) (β : ℝ)
    (hs : Summable fun n : Site L → ℤ => sosHeightWeight L β n) :
    0 < sosPartition L β := by
  unfold sosPartition
  exact hs.tsum_pos (fun n => (sosHeightWeight_pos L β n).le) 0
    (sosHeightWeight_pos L β 0)

/-- The variance series and its normalizing partition function are finite, and the normalizer is
strictly positive. Thus `sosVariance` is the expectation under the normalized pinned-box law. -/
theorem sosVariance_is_genuineExpectation (hL : 1 < L) {β : ℝ} (hβ : 0 < β)
    (u v : Site L) :
    Summable (fun n : Site L → ℤ => ((n u : ℝ) - n v) ^ 2 * sosHeightWeight L β n) ∧
      Summable (fun n : Site L → ℤ => sosHeightWeight L β n) ∧
      0 < sosPartition L β := by
  have hnum := summable_sosSecondMoment hL hβ u v
  have hden := summable_sosPartition hL hβ
  exact ⟨hnum, hden, sosPartition_pos_of_summable L β hden⟩


end FroehlichSpencer.BKT.SOS.Peierls

end
