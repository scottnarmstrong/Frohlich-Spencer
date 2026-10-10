/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Compact.TwoPoint
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

/-! # The local energy gap for a nonconstant clock bond

Distinct clock states have a strictly smaller cosine interaction than an aligned bond. The
estimate is stated both for the residue values and for the `clockAngles` used by the finite clock
model.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Peierls

open FroehlichSpencer.BKT.Clock.Compact

/-- The loss in cosine energy of the smallest nontrivial `n`-clock rotation. -/
def clockEnergyGap (n : ℕ) : ℝ := 1 - Real.cos (2 * Real.pi / (n : ℝ))

/-- For at least two clock states, the smallest nontrivial rotation has positive energy gap. -/
theorem clockEnergyGap_pos {n : ℕ} (hn : 2 ≤ n) : 0 < clockEnergyGap n := by
  unfold clockEnergyGap
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx : 0 < 2 * Real.pi / (n : ℝ) := by positivity
  have hle : 2 * Real.pi / (n : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hnpos]
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    calc
      2 * Real.pi = Real.pi * 2 := by ring
      _ ≤ Real.pi * (n : ℝ) := mul_le_mul_of_nonneg_left h2 Real.pi_pos.le
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi
    (show 0 ≤ (0 : ℝ) by norm_num) hle hx
  simpa using hcos

/-- The cosine interaction of two distinct `n`-clock residues is bounded by that of the
nearest-neighbour residue difference. -/
theorem clockAngleDifference_cos_le {n : ℕ} (hn : 2 ≤ n) (a b : Fin n) (hab : a ≠ b) :
    Real.cos (2 * Real.pi * ((a : ℝ) - (b : ℝ)) / (n : ℝ)) ≤
      Real.cos (2 * Real.pi / (n : ℝ)) := by
  let d : ℕ := Nat.dist a.val b.val
  let q : ℕ := min d (n - d)
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.dist_pos_of_ne (by
      intro h
      exact hab (Fin.ext h))
  have hdlt : d < n := by
    rcases le_total a.val b.val with h | h
    · have hd : d = b.val - a.val := by
        dsimp [d]
        exact Nat.dist_eq_sub_of_le h
      rw [hd]
      omega
    · have hd : d = a.val - b.val := by
        dsimp [d]
        exact Nat.dist_eq_sub_of_le_right h
      rw [hd]
      omega
  have hqpos : 0 < q := by
    dsimp [q]
    omega
  have hqle : 2 * q ≤ n := by
    dsimp [q]
    omega
  have hcosd :
      Real.cos (2 * Real.pi * ((a : ℝ) - (b : ℝ)) / (n : ℝ)) =
      Real.cos (2 * Real.pi * (d : ℝ) / (n : ℝ)) := by
    rcases le_total a.val b.val with h | h
    · have hd : d = b.val - a.val := by
        dsimp [d]
        exact Nat.dist_eq_sub_of_le h
      rw [hd]
      have hcast : ((b.val - a.val : ℕ) : ℝ) = (b : ℝ) - (a : ℝ) := by
        rw [Nat.cast_sub h]
      have habs : (a : ℝ) - (b : ℝ) = -((b.val - a.val : ℕ) : ℝ) := by
        rw [hcast]
        ring
      rw [habs]
      have harg : 2 * Real.pi * (-((b.val - a.val : ℕ) : ℝ)) / (n : ℝ) =
          -(2 * Real.pi * ((b.val - a.val : ℕ) : ℝ) / (n : ℝ)) := by ring
      rw [harg, Real.cos_neg]
    · have hd : d = a.val - b.val := by
        dsimp [d]
        exact Nat.dist_eq_sub_of_le_right h
      rw [hd]
      have hcast : ((a.val - b.val : ℕ) : ℝ) = (a : ℝ) - (b : ℝ) := by
        rw [Nat.cast_sub h]
      have habs : (a : ℝ) - (b : ℝ) = ((a.val - b.val : ℕ) : ℝ) := by
        rw [hcast]
      rw [habs]
  have hcosq :
      Real.cos (2 * Real.pi * (d : ℝ) / (n : ℝ)) =
      Real.cos (2 * Real.pi * (q : ℝ) / (n : ℝ)) := by
    by_cases hhalf : d ≤ n - d
    · have hqeq : q = d := by
        dsimp [q]
        exact min_eq_left hhalf
      rw [hqeq]
    · have hdlarge : n - d < d := by omega
      have hqeq : q = n - d := by
        dsimp [q]
        exact min_eq_right (le_of_lt hdlarge)
      have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      have hcast : ((n - d : ℕ) : ℝ) = (n : ℝ) - (d : ℝ) := by
        rw [Nat.cast_sub (Nat.le_of_lt hdlt)]
      have heq : 2 * Real.pi * (d : ℝ) / (n : ℝ) =
          2 * Real.pi - 2 * Real.pi * ((n - d : ℕ) : ℝ) / (n : ℝ) := by
        rw [hcast]
        field_simp [hnreal]
        ring
      rw [heq, Real.cos_two_pi_sub, hqeq]
  have hnreal_pos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hangle_pos : 0 < 2 * Real.pi / (n : ℝ) := by positivity
  have hangle_le : 2 * Real.pi / (n : ℝ) ≤
      2 * Real.pi * (q : ℝ) / (n : ℝ) := by
    apply (div_le_div_iff_of_pos_right hnreal_pos).2
    have hqreal : 1 ≤ (q : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hqpos)
    calc
      2 * Real.pi = 2 * Real.pi * 1 := by ring
      _ ≤ 2 * Real.pi * (q : ℝ) :=
        mul_le_mul_of_nonneg_left hqreal (by positivity)
  have htop : 2 * Real.pi * (q : ℝ) / (n : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hnreal_pos]
    have hqleReal : 2 * (q : ℝ) ≤ (n : ℝ) := by exact_mod_cast hqle
    calc
      2 * Real.pi * (q : ℝ) = Real.pi * (2 * (q : ℝ)) := by ring
      _ ≤ Real.pi * (n : ℝ) := mul_le_mul_of_nonneg_left hqleReal Real.pi_pos.le
  calc
    Real.cos (2 * Real.pi * ((a : ℝ) - (b : ℝ)) / (n : ℝ)) =
        Real.cos (2 * Real.pi * (d : ℝ) / (n : ℝ)) := hcosd
    _ = Real.cos (2 * Real.pi * (q : ℝ) / (n : ℝ)) := hcosq
    _ ≤ Real.cos (2 * Real.pi / (n : ℝ)) :=
      Real.cos_le_cos_of_nonneg_of_le_pi hangle_pos.le htop hangle_le

/-- The positive-temperature exponential bond weight for distinct clock states is bounded by
the aligned weight times the local energy-gap factor. -/
theorem clockBondWeight_le {n : ℕ} (hn : 2 ≤ n) (a b : Fin n) (hab : a ≠ b)
    {β : ℝ} (hβ : 0 ≤ β) :
    Real.exp (β * Real.cos (2 * Real.pi * ((a : ℝ) - (b : ℝ)) / (n : ℝ))) ≤
      Real.exp (β * (1 - clockEnergyGap n)) := by
  apply Real.exp_le_exp.mpr
  have hc := clockAngleDifference_cos_le hn a b hab
  unfold clockEnergyGap
  nlinarith [mul_nonneg hβ (sub_nonneg.mpr hc)]

/-- The cosine and exponential gap estimates with the angle convention used by the finite clock
model. -/
theorem clockAngles_cos_bond_le {W : Type*} {n : ℕ} (hn : 2 ≤ n)
    (k : W → Fin n) (a b : W) (hab : k a ≠ k b) :
    Real.cos (clockAngles n k a - clockAngles n k b) ≤
      Real.cos (2 * Real.pi / (n : ℝ)) := by
  have hangle : clockAngles n k a - clockAngles n k b =
      2 * Real.pi * ((k a : ℝ) - (k b : ℝ)) / (n : ℝ) := by
    unfold clockAngles
    ring
  rw [hangle]
  exact clockAngleDifference_cos_le hn (k a) (k b) hab

/-- The finite clock-model bond weight at distinct states is at most its energy-gap bound. -/
theorem clockAngles_bondWeight_le {W : Type*} {n : ℕ} (hn : 2 ≤ n)
    (k : W → Fin n) (a b : W) (hab : k a ≠ k b) {β : ℝ} (hβ : 0 ≤ β) :
    Real.exp (β * Real.cos (clockAngles n k a - clockAngles n k b)) ≤
      Real.exp (β * (1 - clockEnergyGap n)) := by
  apply Real.exp_le_exp.mpr
  have hc := clockAngles_cos_bond_le hn k a b hab
  unfold clockEnergyGap
  nlinarith [mul_nonneg hβ (sub_nonneg.mpr hc)]

end FroehlichSpencer.BKT.Clock.Peierls

end
