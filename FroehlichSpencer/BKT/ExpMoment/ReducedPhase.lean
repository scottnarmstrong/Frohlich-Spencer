/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Order.ToIntervalMod

/-! # The reduced phase `[t]_{2π}`

The reduced phase `[t]_{2π} := toIcoMod Real.two_pi_pos (-π) t ∈ [-π, π)` (KP p. 35) is a
nearest representative of `t` modulo `2π`; we record its minimality, subadditivity, behaviour under
integer multiples, negation and finite sums.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

private theorem reducedPhase_decomp (t : ℝ) :
    t = toIcoMod Real.two_pi_pos (-Real.pi) t +
      (toIcoDiv Real.two_pi_pos (-Real.pi) t : ℝ) * (2 * Real.pi) := by
  have h := self_sub_toIcoMod Real.two_pi_pos (-Real.pi) t
  rw [zsmul_eq_mul] at h
  linarith

private theorem reducedPhase_abs_le_pi (t : ℝ) :
    |toIcoMod Real.two_pi_pos (-Real.pi) t| ≤ Real.pi := by
  have h := toIcoMod_mem_Ico Real.two_pi_pos (-Real.pi) t
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- `[t]_{2π}` is a nearest representative: it is no longer than any `t - 2πn`. -/
theorem abs_toIcoMod_le_abs_sub_intMul (t : ℝ) (n : ℤ) :
    |toIcoMod Real.two_pi_pos (-Real.pi) t| ≤ |t - n * (2 * Real.pi)| := by
  set r := toIcoMod Real.two_pi_pos (-Real.pi) t with hr
  set m := toIcoDiv Real.two_pi_pos (-Real.pi) t with hm
  have hd : t - n * (2 * Real.pi) = r + ((m - n : ℤ) : ℝ) * (2 * Real.pi) := by
    have := reducedPhase_decomp t
    push_cast
    linarith
  rw [hd]
  by_cases hk : m - n = 0
  · rw [hk]; simp
  · have h1 : (1 : ℤ) ≤ |m - n| := Int.one_le_abs hk
    have h1' : (1 : ℝ) ≤ |((m - n : ℤ) : ℝ)| := by exact_mod_cast h1
    have hpi := Real.pi_pos
    have h2 : 2 * Real.pi ≤ |((m - n : ℤ) : ℝ) * (2 * Real.pi)| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith
    have h3 := abs_sub_abs_le_abs_sub (((m - n : ℤ) : ℝ) * (2 * Real.pi)) (-r)
    rw [abs_neg, sub_neg_eq_add, add_comm] at h3
    have := reducedPhase_abs_le_pi t
    linarith

theorem abs_toIcoMod_le_abs (t : ℝ) : |toIcoMod Real.two_pi_pos (-Real.pi) t| ≤ |t| := by
  simpa using abs_toIcoMod_le_abs_sub_intMul t 0

theorem abs_toIcoMod_add_le (s t : ℝ) :
    |toIcoMod Real.two_pi_pos (-Real.pi) (s + t)| ≤
      |toIcoMod Real.two_pi_pos (-Real.pi) s| + |toIcoMod Real.two_pi_pos (-Real.pi) t| := by
  have h := abs_toIcoMod_le_abs_sub_intMul (s + t)
    (toIcoDiv Real.two_pi_pos (-Real.pi) s + toIcoDiv Real.two_pi_pos (-Real.pi) t)
  have hs := reducedPhase_decomp s
  have ht := reducedPhase_decomp t
  have he : s + t - ((toIcoDiv Real.two_pi_pos (-Real.pi) s +
      toIcoDiv Real.two_pi_pos (-Real.pi) t : ℤ) : ℝ) * (2 * Real.pi) =
      toIcoMod Real.two_pi_pos (-Real.pi) s + toIcoMod Real.two_pi_pos (-Real.pi) t := by
    push_cast
    linarith
  rw [he] at h
  exact h.trans (abs_add_le _ _)

theorem abs_toIcoMod_intCast_mul_le (c : ℤ) (t : ℝ) :
    |toIcoMod Real.two_pi_pos (-Real.pi) ((c : ℝ) * t)| ≤
      |(c : ℝ)| * |toIcoMod Real.two_pi_pos (-Real.pi) t| := by
  have h := abs_toIcoMod_le_abs_sub_intMul ((c : ℝ) * t)
    (c * toIcoDiv Real.two_pi_pos (-Real.pi) t)
  have ht := reducedPhase_decomp t
  have he : (c : ℝ) * t - ((c * toIcoDiv Real.two_pi_pos (-Real.pi) t : ℤ) : ℝ) *
      (2 * Real.pi) = (c : ℝ) * toIcoMod Real.two_pi_pos (-Real.pi) t := by
    push_cast
    linear_combination (c : ℝ) * ht
  rw [he, abs_mul] at h
  exact h

private theorem abs_toIcoMod_neg_le (t : ℝ) :
    |toIcoMod Real.two_pi_pos (-Real.pi) (-t)| ≤ |toIcoMod Real.two_pi_pos (-Real.pi) t| := by
  simpa using abs_toIcoMod_intCast_mul_le (-1) t

theorem abs_toIcoMod_neg (t : ℝ) :
    |toIcoMod Real.two_pi_pos (-Real.pi) (-t)| = |toIcoMod Real.two_pi_pos (-Real.pi) t| := by
  refine le_antisymm (abs_toIcoMod_neg_le t) ?_
  simpa using abs_toIcoMod_neg_le (-t)

theorem toIcoMod_add_intCast_mul_two_pi (t : ℝ) (n : ℤ) :
    toIcoMod Real.two_pi_pos (-Real.pi) (t + n * (2 * Real.pi)) =
      toIcoMod Real.two_pi_pos (-Real.pi) t := by
  have := toIcoMod_add_zsmul Real.two_pi_pos (-Real.pi) t n
  rwa [zsmul_eq_mul] at this

theorem abs_toIcoMod_sum_le {ι : Type*} (s : Finset ι) (c : ι → ℤ) (t : ι → ℝ) :
    |toIcoMod Real.two_pi_pos (-Real.pi) (∑ i ∈ s, (c i : ℝ) * t i)| ≤
      ∑ i ∈ s, |(c i : ℝ)| * |toIcoMod Real.two_pi_pos (-Real.pi) (t i)| := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := Real.pi_pos
    simp [toIcoMod_eq_self]
    constructor <;> linarith
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (abs_toIcoMod_add_le _ _).trans
      (add_le_add (abs_toIcoMod_intCast_mul_le _ _) ih)

theorem sq_toIcoMod_neg (t : ℝ) :
    toIcoMod Real.two_pi_pos (-Real.pi) (-t) ^ 2 = toIcoMod Real.two_pi_pos (-Real.pi) t ^ 2 := by
  rw [← sq_abs, abs_toIcoMod_neg, sq_abs]

end FroehlichSpencer.BKT

end
