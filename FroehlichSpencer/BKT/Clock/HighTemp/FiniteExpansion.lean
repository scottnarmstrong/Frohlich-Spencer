/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.HighTemp.BondSplit
public import FroehlichSpencer.BKT.Clock.HighTemp.FiniteBox
import Mathlib.Tactic

/-!
# Finite clock partition and marked expansions

The bond split expands both the partition sum and its marked numerator into
nonnegative bond-subset terms.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.HighTemp

open Classical
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Clock.Compact

def clockBondDefectAt (N L : ℕ) (β : ℝ)
    (k : RotatorSpinSite L → Fin N) (e : RotatorInternalBond L) : ℝ :=
  bondDefect β (clockAngles N k ((rotatorFreeGraph L).src e) -
    clockAngles N k ((rotatorFreeGraph L).tgt e))

/-- The finite marked clock numerator after expanding all split bonds. -/
theorem clockBoxNumerator_eq_subsetExpansion (N L : ℕ) (β : ℝ)
    (u v : RotatorSpinSite L) :
    (∑ k : RotatorSpinSite L → Fin N,
      Real.cos (clockAngles N k u - clockAngles N k v) * clockBoxWeight N L β k) =
      Real.exp (-β * (Fintype.card (RotatorInternalBond L) : ℝ)) *
        ∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
          ∑ k : RotatorSpinSite L → Fin N,
            Real.cos (clockAngles N k u - clockAngles N k v) *
              ∏ e ∈ A, clockBondDefectAt N L β k e := by
  classical
  let c := Real.exp (-β * (Fintype.card (RotatorInternalBond L) : ℝ))
  calc
    (∑ k : RotatorSpinSite L → Fin N,
      Real.cos (clockAngles N k u - clockAngles N k v) * clockBoxWeight N L β k) =
        ∑ k : RotatorSpinSite L → Fin N,
          c * (Real.cos (clockAngles N k u - clockAngles N k v) *
            ∏ e : RotatorInternalBond L, (1 + clockBondDefectAt N L β k e)) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [clockBoxWeight_eq_bondSplit]
              dsimp [c, clockBondDefectAt]
              ring
    _ = c * ∑ k : RotatorSpinSite L → Fin N,
          Real.cos (clockAngles N k u - clockAngles N k v) *
            ∏ e : RotatorInternalBond L, (1 + clockBondDefectAt N L β k e) := by
          rw [Finset.mul_sum]
    _ = c * ∑ k : RotatorSpinSite L → Fin N,
          ∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
            Real.cos (clockAngles N k u - clockAngles N k v) *
              ∏ e ∈ A, clockBondDefectAt N L β k e := by
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          have hprod := prod_one_add_bondDefect_eq_sum N L β k
          rw [show (∏ e : RotatorInternalBond L, (1 + clockBondDefectAt N L β k e)) =
                ∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
                  ∏ e ∈ A, clockBondDefectAt N L β k e by
                simpa [clockBondDefectAt] using hprod]
          rw [Finset.mul_sum]
    _ = c * ∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
          ∑ k : RotatorSpinSite L → Fin N,
            Real.cos (clockAngles N k u - clockAngles N k v) *
              ∏ e ∈ A, clockBondDefectAt N L β k e := by
          congr 1
          rw [Finset.sum_comm]
    _ = _ := by rfl

/-- The finite partition sum after expanding all split bonds. -/
theorem clockBoxPartition_eq_subsetExpansion (N L : ℕ) (β : ℝ) :
    (∑ k : RotatorSpinSite L → Fin N, clockBoxWeight N L β k) =
      Real.exp (-β * (Fintype.card (RotatorInternalBond L) : ℝ)) *
        ∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
          ∑ k : RotatorSpinSite L → Fin N,
            ∏ e ∈ A, clockBondDefectAt N L β k e := by
  classical
  let c := Real.exp (-β * (Fintype.card (RotatorInternalBond L) : ℝ))
  calc
    (∑ k : RotatorSpinSite L → Fin N, clockBoxWeight N L β k) =
        ∑ k : RotatorSpinSite L → Fin N,
          c * ∏ e : RotatorInternalBond L, (1 + clockBondDefectAt N L β k e) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [clockBoxWeight_eq_bondSplit]
            rfl
    _ = c * ∑ k : RotatorSpinSite L → Fin N,
          ∏ e : RotatorInternalBond L, (1 + clockBondDefectAt N L β k e) := by
          rw [Finset.mul_sum]
    _ = c * ∑ k : RotatorSpinSite L → Fin N,
          ∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
            ∏ e ∈ A, clockBondDefectAt N L β k e := by
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          have hprod := prod_one_add_bondDefect_eq_sum N L β k
          simpa [clockBondDefectAt] using hprod
    _ = c * ∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
          ∑ k : RotatorSpinSite L → Fin N,
            ∏ e ∈ A, clockBondDefectAt N L β k e := by
          congr 1
          rw [Finset.sum_comm]
    _ = _ := by rfl

/-- The split finite partition sum as a configuration sum of unrestricted
bond products. -/
theorem clockBoxPartition_eq_fullProductSum (N L : ℕ) (β : ℝ) :
    (∑ k : RotatorSpinSite L → Fin N, clockBoxWeight N L β k) =
      Real.exp (-β * (Fintype.card (RotatorInternalBond L) : ℝ)) *
        ∑ k : RotatorSpinSite L → Fin N,
          ∏ e : RotatorInternalBond L, (1 + clockBondDefectAt N L β k e) := by
  classical
  rw [clockBoxPartition_eq_subsetExpansion]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hprod := prod_one_add_bondDefect_eq_sum N L β k
  simpa [clockBondDefectAt] using hprod.symm

/-- Disconnected marked bond subsets cancel under a cluster rotation; the
remaining terms are bounded by their unmarked partition contributions. -/
theorem clockBoxMarkedSubsetSum_le_connected (N L : ℕ) (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 ≤ β) (u v : RotatorSpinSite L) :
    (∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
      ∑ k : RotatorSpinSite L → Fin N,
        Real.cos (clockAngles N k u - clockAngles N k v) *
          ∏ e ∈ A, clockBondDefectAt N L β k e) ≤
    ∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
      if (selectedBondGraph L A).Reachable u v then
        ∑ k : RotatorSpinSite L → Fin N, ∏ e ∈ A, clockBondDefectAt N L β k e
      else 0 := by
  classical
  apply Finset.sum_le_sum
  intro A hA
  by_cases hconn : (selectedBondGraph L A).Reachable u v
  · simp [hconn]
    apply Finset.sum_le_sum
    intro k hk
    have hnonneg : 0 ≤ ∏ e ∈ A, clockBondDefectAt N L β k e :=
      Finset.prod_nonneg fun e he => bondDefect_nonneg hβ
    calc
      Real.cos (clockAngles N k u - clockAngles N k v) *
          ∏ e ∈ A, clockBondDefectAt N L β k e ≤
        1 * ∏ e ∈ A, clockBondDefectAt N L β k e :=
          mul_le_mul_of_nonneg_right (Real.cos_le_one _) hnonneg
      _ = ∏ e ∈ A, clockBondDefectAt N L β k e := by ring
  · have hzero := clockSubsetTerm_eq_zero_of_not_reachable N L hN β A u v hconn
    have hzero' :
        (∑ k : RotatorSpinSite L → Fin N,
          Real.cos (clockAngles N k u - clockAngles N k v) *
            ∏ e ∈ A, clockBondDefectAt N L β k e) = 0 := by
      simpa [clockBondDefectAt] using hzero
    simp [hconn, hzero']

/-- The marked numerator is bounded by the connected unmarked subset sum,
with the common constant bond factor retained. -/
theorem clockBoxNumerator_le_exp_connected (N L : ℕ) (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 ≤ β) (u v : RotatorSpinSite L) :
    (∑ k : RotatorSpinSite L → Fin N,
      Real.cos (clockAngles N k u - clockAngles N k v) * clockBoxWeight N L β k) ≤
      Real.exp (-β * (Fintype.card (RotatorInternalBond L) : ℝ)) *
        ∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
          if (selectedBondGraph L A).Reachable u v then
            ∑ k : RotatorSpinSite L → Fin N,
              ∏ e ∈ A, clockBondDefectAt N L β k e
          else 0 := by
  rw [clockBoxNumerator_eq_subsetExpansion]
  exact mul_le_mul_of_nonneg_left
    (clockBoxMarkedSubsetSum_le_connected N L hN hβ u v) (Real.exp_pos _).le

end FroehlichSpencer.BKT.Clock.HighTemp

end
