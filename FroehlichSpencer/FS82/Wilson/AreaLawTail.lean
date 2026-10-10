/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Geometric tail for the small-activity Wilson estimate

This file isolates the numerical tail after the connected-plaquette count.
The input `r` is the animal-counted activity (at most `400` times the
nonzero one-plaquette activity in the small-activity expansion).
-/

public section

namespace FroehlichSpencer.FS82.Wilson

/-- The geometric tail beginning at area `A`, written with a natural shift so
that its value is a direct multiple of the ordinary geometric series. -/
@[expose] noncomputable def areaActivityTail (r : ℝ) (A : ℕ) : ℝ :=
  ∑' n : ℕ, r ^ (A + n)

theorem areaActivityTail_eq (r : ℝ) (A : ℕ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    areaActivityTail r A = r ^ A / (1 - r) := by
  unfold areaActivityTail
  have hsum : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_lt_one hr0 hr1
  calc
    (∑' n : ℕ, r ^ (A + n)) =
        ∑' n : ℕ, r ^ A * r ^ n := by
          apply tsum_congr
          intro n
          rw [pow_add]
    _ = r ^ A * ∑' n : ℕ, r ^ n := by rw [tsum_mul_left]
    _ = r ^ A / (1 - r) := by rw [tsum_geometric_of_lt_one hr0 hr1]; ring

/-- A factor linear in the area is absorbed by the geometric decay whenever
the animal-counted activity is at most `exp(-7)`. -/
theorem areaActivityTail_bound (A : ℕ) (hA : 1 ≤ A) (r : ℝ)
    (hr0 : 0 ≤ r) (hr : r ≤ Real.exp (-7)) :
    24 * (A : ℝ) * areaActivityTail r A ≤ Real.exp (-(A : ℝ) / 2) := by
  have hApos : 0 < (A : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hA)
  have hExp1 : (2 : ℝ) ≤ Real.exp 1 := by
    nlinarith only [Real.add_one_le_exp (1 : ℝ)]
  have hr1 : r < 1 := by
    have hsmall : Real.exp (-7) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    exact lt_of_le_of_lt hr hsmall
  have hden : 0 < 1 - r := by linarith
  have hExp5 : (32 : ℝ) ≤ Real.exp 5 := by
    have hpow : (2 : ℝ) ^ 5 ≤ (Real.exp 1) ^ 5 :=
      pow_le_pow_left₀ (by norm_num) hExp1 5
    rw [← Real.exp_nat_mul] at hpow
    norm_num at hpow ⊢
    exact hpow
  have hExp7 : (4 : ℝ) ≤ Real.exp 7 := by
    have hpow : (2 : ℝ) ^ 7 ≤ (Real.exp 1) ^ 7 :=
      pow_le_pow_left₀ (by norm_num) hExp1 7
    rw [← Real.exp_nat_mul] at hpow
    norm_num at hpow ⊢
    exact le_trans (by norm_num) hpow
  have hexpneg : Real.exp (-7) = 1 / Real.exp 7 := by
    simp [Real.exp_neg]
  have hrQuarter : r ≤ (1 : ℝ) / 4 := by
    calc
      r ≤ Real.exp (-7) := hr
      _ = 1 / Real.exp 7 := hexpneg
      _ ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hExp7
  have hdenInv : 1 / (1 - r) ≤ 4 / 3 := by
    have hdenLower : (3 : ℝ) / 4 ≤ 1 - r := by linarith
    calc
      1 / (1 - r) ≤ 1 / ((3 : ℝ) / 4) :=
        one_div_le_one_div_of_le (by norm_num) hdenLower
      _ = 4 / 3 := by norm_num
  have hpow : r ^ A ≤ (Real.exp (-7)) ^ A := by
    exact pow_le_pow_left₀ hr0 hr A
  have hexpPow : (Real.exp (-7)) ^ A = Real.exp (-7 * (A : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hpowExp : r ^ A ≤ Real.exp (-7 * (A : ℝ)) := by
    rw [hexpPow] at hpow
    exact hpow
  have hA_le_exp : (A : ℝ) ≤ Real.exp (A : ℝ) := by
    have h := Real.add_one_le_exp (A : ℝ)
    linarith
  have htail : areaActivityTail r A = r ^ A / (1 - r) :=
    areaActivityTail_eq r A hr0 hr1
  rw [htail]
  have hfactor : 24 * (A : ℝ) / (1 - r) ≤ Real.exp 5 * Real.exp (A : ℝ) := by
    calc
      24 * (A : ℝ) / (1 - r) ≤ 32 * (A : ℝ) := by
        rw [div_eq_mul_inv]
        calc
          24 * (A : ℝ) * (1 - r)⁻¹ ≤
              24 * (A : ℝ) * (4 / 3) := by
                exact mul_le_mul_of_nonneg_left
                  (by simpa only [one_div] using hdenInv) (by positivity)
          _ = 32 * (A : ℝ) := by ring
      _ ≤ 32 * Real.exp (A : ℝ) :=
        mul_le_mul_of_nonneg_left hA_le_exp (by norm_num)
      _ ≤ Real.exp 5 * Real.exp (A : ℝ) :=
        mul_le_mul_of_nonneg_right hExp5 (Real.exp_pos _).le
  calc
    24 * (A : ℝ) * (r ^ A / (1 - r)) =
        (24 * (A : ℝ) / (1 - r)) * r ^ A := by ring
    _ ≤ Real.exp 5 * Real.exp (A : ℝ) *
          Real.exp (-7 * (A : ℝ)) := by
        exact mul_le_mul hfactor hpowExp (by positivity) (by positivity)
    _ = Real.exp (5 + (A : ℝ) - 7 * (A : ℝ)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (-(A : ℝ) / 2) := by
        apply Real.exp_le_exp.mpr
        have hAone : (1 : ℝ) ≤ A := by exact_mod_cast hA
        nlinarith only [hAone]

end FroehlichSpencer.FS82.Wilson

end
