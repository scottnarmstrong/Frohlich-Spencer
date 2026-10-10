/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Peierls.ClockReduction
public import FroehlichSpencer.BKT.Clock.Peierls.MismatchBound
import Mathlib.Tactic

/-! # The low-temperature ordered phase of the finite clock model -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Peierls

open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Clock.Window
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Ginibre

/-- The clock Peierls theorem: at sufficiently low temperature every integer harmonic has
long-range order. -/
theorem clockPeierlsStatement_holds : ClockPeierlsStatement := by
  apply clockPeierlsStatement_of_positiveSquare_mismatch_bound
  intro n hn
  let x : ℝ := 3600 * (n : ℝ)
  let βbar : ℝ := (Real.log x + 1) / clockEnergyGap n
  refine ⟨βbar, fun β hβ hβbar r hr => ?_⟩
  let L := 3 * r + 20
  let a : RotatorSpinSite L := clockBoxOrigin L
  let b : RotatorSpinSite L := (⟨r, by dsimp [L]; omega⟩, ⟨0, by dsimp [L]; omega⟩)
  have hgap : 0 < clockEnergyGap n := clockEnergyGap_pos hn
  have hx : 0 < x := by dsimp [x]; positivity
  have hthreshold : Real.log x + 1 < β * clockEnergyGap n := by
    apply (div_lt_iff₀ hgap).mp
    simpa [βbar] using hβbar
  have hexpTail : Real.exp (-(β * clockEnergyGap n)) ≤ x⁻¹ := by
    have hexpStrict : Real.exp (-(β * clockEnergyGap n)) <
        Real.exp (-(Real.log x + 1)) :=
      Real.exp_lt_exp.mpr (neg_lt_neg hthreshold)
    have hsmall : Real.exp (-(Real.log x + 1)) ≤ x⁻¹ := by
      have hexpSplit : Real.exp (-(Real.log x + 1)) =
          Real.exp (-(Real.log x)) * Real.exp (-1) := by
        rw [show -(Real.log x + 1) = -(Real.log x) + (-1) by ring,
          Real.exp_add]
      rw [hexpSplit, Real.exp_neg, Real.exp_log hx]
      have hone : Real.exp (-1 : ℝ) ≤ 1 :=
        (Real.exp_le_exp.mpr (show (-1 : ℝ) ≤ 0 by norm_num)).trans_eq Real.exp_zero
      have hinv : 0 ≤ x⁻¹ := by positivity
      simpa using mul_le_mul_of_nonneg_left hone hinv
    exact hexpStrict.le.trans hsmall
  have hq : 36 * (n : ℝ) * Real.exp (-(β * clockEnergyGap n)) ≤ 1 / 100 := by
    calc
      _ ≤ 36 * (n : ℝ) * x⁻¹ :=
        mul_le_mul_of_nonneg_left hexpTail (by positivity)
      _ = 1 / 100 := by
        dsimp [x]
        have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
        field_simp [hnreal]
        norm_num
  have hRL : r ≤ L := by dsimp [L]; omega
  have hratio := clockMismatchRatio_le_quarter_of_small_activity n L r hn hRL hr β hβ hq
  dsimp [L, a, b] at hratio ⊢
  simpa [clockBoxOrigin, squareBoxEquiv] using hratio

end FroehlichSpencer.BKT.Clock.Peierls

end
