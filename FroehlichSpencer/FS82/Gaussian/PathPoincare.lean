/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib

/-! A crude one-ended discrete Dirichlet Poincare estimate. -/

public section

open Finset

namespace FroehlichSpencer.FS82.Gaussian

theorem pathPoincare (n : ℕ) (f : ℕ → ℝ) (h0 : f 0 = 0) :
    (∑ j ∈ range n, f (j + 1) ^ 2) ≤
      (n + 1 : ℝ) ^ 2 *
        ∑ k ∈ range (n + 1), (f (k + 1) - f k) ^ 2 := by
  let E : ℝ := ∑ k ∈ range (n + 1), (f (k + 1) - f k) ^ 2
  have hE : 0 ≤ E := by
    dsimp [E]
    exact Finset.sum_nonneg fun k hk => sq_nonneg _
  have telescoping (j : ℕ) :
      (∑ k ∈ range (j + 1), (f (k + 1) - f k)) = f (j + 1) - f 0 := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      ring
  have pointwise (j : ℕ) (hj : j < n) : f (j + 1) ^ 2 ≤ ((j + 1 : ℕ) : ℝ) * E := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (range (j + 1))
      (fun k => f (k + 1) - f k) (fun _ => (1 : ℝ))
    have hconst : (∑ k ∈ range (j + 1), (1 : ℝ) ^ 2) = ((j + 1 : ℕ) : ℝ) := by
      simp
    have hsub : range (j + 1) ⊆ range (n + 1) :=
      Finset.range_mono (Nat.succ_le_succ (Nat.le_of_lt hj))
    have hprefix :
        (∑ k ∈ range (j + 1), (f (k + 1) - f k) ^ 2) ≤ E := by
      dsimp [E]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun k hk hnot => sq_nonneg _
    have htel := telescoping j
    rw [h0, sub_zero] at htel
    have hcs' : f (j + 1) ^ 2 ≤
        (∑ k ∈ range (j + 1), (f (k + 1) - f k) ^ 2) * ((j + 1 : ℕ) : ℝ) := by
      simpa only [mul_one, htel, h0, sub_zero, hconst] using hcs
    calc
      f (j + 1) ^ 2 ≤
          (∑ k ∈ range (j + 1), (f (k + 1) - f k) ^ 2) * ((j + 1 : ℕ) : ℝ) := hcs'
      _ ≤ E * ((j + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hprefix (Nat.cast_nonneg (j + 1))
      _ = ((j + 1 : ℕ) : ℝ) * E := by ring
  have hsum :
      (∑ j ∈ range n, f (j + 1) ^ 2) ≤
        ∑ j ∈ range n, ((n + 1 : ℝ) * E) := by
    apply Finset.sum_le_sum
    intro j hj
    have hp := pointwise j (Finset.mem_range.mp hj)
    have hj' : ((j + 1 : ℕ) : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt (Finset.mem_range.mp hj))
    exact le_trans hp (mul_le_mul_of_nonneg_right hj' hE)
  calc
    (∑ j ∈ range n, f (j + 1) ^ 2) ≤
        ∑ j ∈ range n, ((n + 1 : ℝ) * E) := hsum
    _ = (n : ℝ) * ((n + 1 : ℝ) * E) := by simp
    _ ≤ (n + 1 : ℝ) ^ 2 * E := by
      have hn : (n : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.le_succ n
      nlinarith [hE]

end FroehlichSpencer.FS82.Gaussian
