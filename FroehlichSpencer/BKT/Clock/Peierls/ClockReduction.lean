/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Window.MasslessWindow
import Mathlib.Tactic

/-!
# Finite clock mismatch reduction for the Peierls theorem

The finite clock correlation is bounded below by one minus twice the Gibbs probability that the
two endpoint spins differ. This module also records the centered-box passage from a uniform finite
mismatch estimate to the exact all-harmonics long-range-order statement.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Peierls

open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Clock.Window
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Ginibre

/-- Unnormalized weight of clock configurations whose endpoint spins differ. -/
def clockMismatchWeight (n L : ℕ) (β : ℝ) (a b : RotatorSpinSite L) : ℝ :=
  ∑ k : RotatorSpinSite L → Fin n,
    (if k a ≠ k b then clockBoxWeight n L β k else 0)

/-- Partition sum of the free clock box. -/
def clockBoxPartitionSum (n L : ℕ) (β : ℝ) : ℝ :=
  ∑ k : RotatorSpinSite L → Fin n, clockBoxWeight n L β k

theorem clockBoxWeight_pos (n L : ℕ) (β : ℝ) (k : RotatorSpinSite L → Fin n) :
    0 < clockBoxWeight n L β k := by
  simp only [clockBoxWeight]
  exact Real.exp_pos _

theorem clockMismatchWeight_nonneg (n L : ℕ) (β : ℝ) (a b : RotatorSpinSite L) :
    0 ≤ clockMismatchWeight n L β a b := by
  unfold clockMismatchWeight
  exact Finset.sum_nonneg fun k _ => by
    split_ifs
    · exact (clockBoxWeight_pos n L β k).le
    · exact le_rfl

theorem clockBoxPartitionSum_pos (n L : ℕ) (hn : 0 < n) (β : ℝ) :
    0 < clockBoxPartitionSum n L β := by
  unfold clockBoxPartitionSum
  apply Finset.sum_pos
  · intro k hk
    exact clockBoxWeight_pos n L β k
  · exact ⟨fun _ => ⟨0, hn⟩, Finset.mem_univ _⟩

/-- The finite-volume character is at least `1 - 2` times the mismatch probability. -/
theorem clockModel_twoPoint_squareBox_ge_one_sub_two_mismatch (n L : ℕ) (hn : 0 < n)
    {β : ℝ} (hβ : 0 ≤ β) (ξ : ℤ) (a b : RotatorSpinSite L) :
    1 - 2 * (clockMismatchWeight n L β a b / clockBoxPartitionSum n L β) ≤
      (clockModel n hn β hβ).twoPoint (ξ : ℤ) (squareBoxZ L) (siteToZ a) (siteToZ b) := by
  have hZ : 0 < clockBoxPartitionSum n L β := clockBoxPartitionSum_pos n L hn β
  have hterm (k : RotatorSpinSite L → Fin n) :
      clockBoxWeight n L β k - 2 * (if k a ≠ k b then clockBoxWeight n L β k else 0) ≤
        Real.cos (ξ * (clockAngles n k a - clockAngles n k b)) * clockBoxWeight n L β k := by
    by_cases hab : k a = k b
    · simp [hab, clockAngles]
    · have hw := clockBoxWeight_pos n L β k
      have hc : -1 ≤ Real.cos (ξ * (clockAngles n k a - clockAngles n k b)) :=
        Real.neg_one_le_cos _
      rw [ite_eq_left hab]
      have hmul := mul_le_mul_of_nonneg_right hc hw.le
      nlinarith [hmul]
  have hsum :
      clockBoxPartitionSum n L β - 2 * clockMismatchWeight n L β a b ≤
        ∑ k : RotatorSpinSite L → Fin n,
          Real.cos (ξ * (clockAngles n k a - clockAngles n k b)) * clockBoxWeight n L β k := by
    calc
      _ = ∑ k : RotatorSpinSite L → Fin n,
          (clockBoxWeight n L β k -
            2 * (if k a ≠ k b then clockBoxWeight n L β k else 0)) := by
              dsimp [clockBoxPartitionSum, clockMismatchWeight]
              rw [Finset.mul_sum, Finset.sum_sub_distrib]
      _ ≤ _ := Finset.sum_le_sum fun k _ => hterm k
  have hratio :
      (clockBoxPartitionSum n L β - 2 * clockMismatchWeight n L β a b) /
          clockBoxPartitionSum n L β ≤
        (∑ k : RotatorSpinSite L → Fin n,
          Real.cos (ξ * (clockAngles n k a - clockAngles n k b)) * clockBoxWeight n L β k) /
          clockBoxPartitionSum n L β :=
    (div_le_div_iff_of_pos_right hZ).2 hsum
  rw [clockModel_twoPoint_squareBox n L hn hβ ξ a b]
  calc
    1 - 2 * (clockMismatchWeight n L β a b / clockBoxPartitionSum n L β) =
        (clockBoxPartitionSum n L β - 2 * clockMismatchWeight n L β a b) /
          clockBoxPartitionSum n L β := by field_simp [hZ.ne']
    _ ≤ _ := hratio

/-- A fixed positive mismatch estimate on large positive free squares implies the full clock
Peierls statement. The endpoints have separation `R+1`; the extra unit makes the construction
uniform at `R=0`. -/
theorem clockPeierlsStatement_of_positiveSquare_mismatch_bound
    (hbound : ∀ n : ℕ, ∀ _hn : 2 ≤ n, ∃ βbar : ℝ,
      ∀ (β : ℝ) (_hβ : 0 ≤ β), βbar < β →
        ∀ r : ℕ, 1 ≤ r →
          let L := 3 * r + 20
          let a : RotatorSpinSite L :=
            (squareBoxEquiv L).symm ⟨(0, 0), by
              simp [squareBoxZ, L]
              omega⟩
          let b : RotatorSpinSite L :=
            (squareBoxEquiv L).symm ⟨((r : ℤ), 0), by
              simp [squareBoxZ, L]
              omega⟩
          clockMismatchWeight n L β a b / clockBoxPartitionSum n L β ≤ (1 / 4 : ℝ)) :
    ClockPeierlsStatement := by
  intro n hn
  obtain ⟨βbar, hβbound⟩ := hbound n hn
  refine ⟨βbar, fun β hβ hβgt ξ => ?_⟩
  refine ⟨1 / 2, by norm_num, fun R => ?_⟩
  let r := R + 1
  have hr : 1 ≤ r := by simp [r]
  let L := 3 * r + 20
  let a : RotatorSpinSite L :=
    (squareBoxEquiv L).symm ⟨(0, 0), by
      simp [squareBoxZ, L]
      omega⟩
  let b : RotatorSpinSite L :=
    (squareBoxEquiv L).symm ⟨((r : ℤ), 0), by
      simp [squareBoxZ, L]
      omega⟩
  have hmis := hβbound β hβ hβgt r hr
  dsimp only [L, a, b] at hmis
  have hcorr := clockModel_twoPoint_squareBox_ge_one_sub_two_mismatch n (3 * r + 20)
    (by omega) hβ ξ a b
  have hratio : clockMismatchWeight n (3 * r + 20) β a b /
      clockBoxPartitionSum n (3 * r + 20) β ≤ (1 / 4 : ℝ) := by
    exact hmis
  have hfinite : (1 / 2 : ℝ) ≤
      (clockModel n (by omega) β hβ).twoPoint (ξ : ℤ)
        (squareBoxZ (3 * r + 20)) (siteToZ a) (siteToZ b) := by
    nlinarith [hcorr, hratio]
  have ha : siteToZ a = (0, 0) := by
    rw [← squareBoxEquiv_apply_coe]
    simp [a]
  have hb : siteToZ b = ((r : ℤ), 0) := by
    rw [← squareBoxEquiv_apply_coe]
    simp [b]
  have hfinite' : (1 / 2 : ℝ) ≤
      (clockModel n (by omega) β hβ).twoPoint (ξ : ℤ)
        (squareBoxZ (3 * r + 20)) (0, 0) ((r : ℤ), 0) := by
    simpa only [ha, hb] using hfinite
  have hinf := (clockModel n (by omega) β hβ).twoPoint_le_twoPointLimit (ξ : ℤ)
    (siteToZ_mem_squareBoxZ a) (siteToZ_mem_squareBoxZ b)
  rw [ha, hb] at hinf
  have hlim : (1 / 2 : ℝ) ≤
      (clockModel n (by omega) β hβ).twoPointLimit (ξ : ℤ)
        (0, 0) ((r : ℤ), 0) :=
    hfinite'.trans hinf
  refine ⟨(0, 0), ((r : ℤ), 0), ?_, hlim⟩
  rw [l1Dist_zero_right]
  omega

end FroehlichSpencer.BKT.Clock.Peierls

end
