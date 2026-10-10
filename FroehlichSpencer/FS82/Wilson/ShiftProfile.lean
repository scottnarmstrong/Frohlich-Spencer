/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# The transverse profile of the explicit loop shift

* `uni d` is the uniform weight `1/(d+1)` on `{0,…,d}` and `ramp d` is
  `j/((d+1)(d+2))` on `{1,…,d+1}`; `ramp d (j+1) - ramp d j = uni d j - uni (d+1) j`.
* `levelTwo d`, `levelThree d` are the two components of the level field `b_d` in the
  transverse `2–3` plane, with `curl b_d = u_d ⊗ u_d - u_{d+1} ⊗ u_{d+1}`.
* `shiftTwo d`, `shiftThree d` are the components of `a_d = Σ_{j<d} b_j`, with
  `curl a_d = u_0 ⊗ u_0 - u_d ⊗ u_d`: the unit flux of one plaquette is spread
  uniformly over the square `{0,…,d}²`.
* The squared norms are bounded over every finite index set, and the tent sums used for
  the perimeter bookkeeping are bounded.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open Finset

/-- `u_d`: the uniform weight `1/(d+1)` on `{0,…,d}`. -/
@[expose] noncomputable def uni (d : ℕ) (j : ℤ) : ℝ :=
  if 0 ≤ j ∧ j ≤ (d : ℤ) then 1 / ((d : ℝ) + 1) else 0

/-- `X_d`: the ramp `j/((d+1)(d+2))` on `{1,…,d+1}`. -/
@[expose] noncomputable def ramp (d : ℕ) (j : ℤ) : ℝ :=
  if 1 ≤ j ∧ j ≤ (d : ℤ) + 1 then (j : ℝ) / (((d : ℝ) + 1) * ((d : ℝ) + 2)) else 0


theorem uni_zero (j : ℤ) : uni 0 j = if j = 0 then 1 else 0 := by
  unfold uni
  by_cases h : j = 0
  · subst h
    simp
  · rw [ite_eq_right (by omega), ite_eq_right h]

theorem uni_ne_zero {d : ℕ} {j : ℤ} (h : uni d j ≠ 0) : 0 ≤ j ∧ j ≤ (d : ℤ) := by
  by_contra hc
  exact h (by unfold uni; rw [ite_eq_right hc])

theorem ramp_ne_zero {d : ℕ} {j : ℤ} (h : ramp d j ≠ 0) : 1 ≤ j ∧ j ≤ (d : ℤ) + 1 := by
  by_contra hc
  exact h (by unfold ramp; rw [ite_eq_right hc])

set_option linter.unusedTactic false in
/-- The forward difference of the ramp is the difference of consecutive uniform weights. -/
theorem ramp_succ_sub (d : ℕ) (j : ℤ) :
    ramp d (j + 1) - ramp d j = uni d j - uni (d + 1) j := by
  have h1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  unfold ramp uni
  split_ifs with c1 c2 c3 c4 c3 c4 c3 c4 c2 c3 c4 c3 c4 c3 c4 <;>
    first
      | (exfalso; omega)
      | (push_cast; field_simp; (try ring); done)
      | (obtain rfl : j = 0 := by omega
         push_cast; field_simp; (try ring); done)
      | (obtain rfl : j = (d : ℤ) + 1 := by omega
         push_cast; field_simp; (try ring); done)

theorem uni_natCast (d j : ℕ) (hj : j ≤ d) : uni d (j : ℤ) = 1 / ((d : ℝ) + 1) := by
  have h : (0 : ℤ) ≤ (j : ℤ) ∧ (j : ℤ) ≤ (d : ℤ) := ⟨by positivity, by exact_mod_cast hj⟩
  simp only [uni, h, and_self, ite_true]

theorem ramp_natCast (d j : ℕ) (hj : j ≤ d + 1) :
    ramp d (j : ℤ) = (j : ℝ) / (((d : ℝ) + 1) * ((d : ℝ) + 2)) := by
  unfold ramp
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · simp
  · have h : (1 : ℤ) ≤ (j : ℤ) ∧ (j : ℤ) ≤ (d : ℤ) + 1 :=
      ⟨by exact_mod_cast hpos, by exact_mod_cast hj⟩
    simp only [h, and_self, ite_true, Int.cast_natCast]

/-! ### Sums over arbitrary finite index sets -/

/-- A nonnegative function on `ℤ` whose support is parametrized by `e` on `range n` has every
finite partial sum bounded by the parametrized sum. -/
theorem sum_le_sum_range_of_param (f : ℤ → ℝ) (hf : ∀ j, 0 ≤ f j) (n : ℕ) (e : ℕ → ℤ)
    (hsupp : ∀ j, f j ≠ 0 → ∃ k, k < n ∧ e k = j) (s : Finset ℤ) :
    ∑ j ∈ s, f j ≤ ∑ k ∈ range n, f (e k) := by
  classical
  calc ∑ j ∈ s, f j = ∑ j ∈ s with f j ≠ 0, f j := (sum_filter_ne_zero s).symm
    _ ≤ ∑ j ∈ (range n).image e, f j := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj
          obtain ⟨k, hk, rfl⟩ := hsupp j (mem_filter.mp hj).2
          exact mem_image.mpr ⟨k, mem_range.mpr hk, rfl⟩
        · intro j _ _
          exact hf j
    _ ≤ ∑ k ∈ range n, f (e k) := sum_image_le_of_nonneg fun _ _ => hf _

theorem sum_range_natCast_sq (n : ℕ) :
    ∑ j ∈ range (n + 1), (j : ℝ) ^ 2 = (n : ℝ) * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- `‖u_d‖² ≤ 1/(d+1)` over every finite index set. -/
theorem sum_uni_sq_le (d : ℕ) (s : Finset ℤ) :
    ∑ j ∈ s, uni d j ^ 2 ≤ 1 / ((d : ℝ) + 1) := by
  have h1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hle := sum_le_sum_range_of_param (fun j => uni d j ^ 2) (fun j => sq_nonneg _)
    (d + 1) (fun k => (k : ℤ))
    (by
      intro j hj
      have hj' := uni_ne_zero (d := d) (j := j) (by
        intro h0
        exact hj (by simp [h0]))
      refine ⟨j.toNat, by omega, by omega⟩) s
  refine hle.trans (le_of_eq ?_)
  rw [sum_congr rfl (fun j hj => by
    rw [uni_natCast d j (Nat.lt_succ_iff.mp (mem_range.mp hj))])]
  rw [sum_const, card_range, nsmul_eq_mul]
  push_cast
  field_simp

/-- The squared norm of the ramp, `(2d+3)/(6(d+1)(d+2))`. -/
@[expose] noncomputable def rampNormSq (d : ℕ) : ℝ :=
  (2 * (d : ℝ) + 3) / (6 * ((d : ℝ) + 1) * ((d : ℝ) + 2))

theorem rampNormSq_nonneg (d : ℕ) : 0 ≤ rampNormSq d := by
  unfold rampNormSq
  positivity

/-- `‖X_d‖² ≤ (2d+3)/(6(d+1)(d+2))` over every finite index set. -/
theorem sum_ramp_sq_le (d : ℕ) (s : Finset ℤ) :
    ∑ j ∈ s, ramp d j ^ 2 ≤ rampNormSq d := by
  have h1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hle := sum_le_sum_range_of_param (fun j => ramp d j ^ 2) (fun j => sq_nonneg _)
    (d + 2) (fun k => (k : ℤ))
    (by
      intro j hj
      have hj' := ramp_ne_zero (d := d) (j := j) (by
        intro h0
        exact hj (by simp [h0]))
      refine ⟨j.toNat, by omega, by omega⟩) s
  refine hle.trans (le_of_eq ?_)
  rw [sum_congr rfl (fun j hj => by
    rw [ramp_natCast d j (Nat.lt_succ_iff.mp (mem_range.mp hj)), div_pow])]
  rw [← sum_div, sum_range_natCast_sq (d + 1), rampNormSq]
  push_cast
  field_simp
  ring

/-! ### The level field and the shift in the transverse plane -/

/-- Component along axis 2 of the level field `b_d`. -/
@[expose] noncomputable def levelTwo (d : ℕ) (y z : ℤ) : ℝ := -(uni (d + 1) y * ramp d z)

/-- Component along axis 3 of the level field `b_d`. -/
@[expose] noncomputable def levelThree (d : ℕ) (y z : ℤ) : ℝ := ramp d y * uni d z

/-- Component along axis 2 of `a_d = Σ_{j<d} b_j`. -/
@[expose] noncomputable def shiftTwo (d : ℕ) (y z : ℤ) : ℝ := ∑ j ∈ range d, levelTwo j y z

/-- Component along axis 3 of `a_d = Σ_{j<d} b_j`. -/
@[expose] noncomputable def shiftThree (d : ℕ) (y z : ℤ) : ℝ := ∑ j ∈ range d, levelThree j y z

@[simp] theorem shiftTwo_zero (y z : ℤ) : shiftTwo 0 y z = 0 := by simp [shiftTwo]

@[simp] theorem shiftThree_zero (y z : ℤ) : shiftThree 0 y z = 0 := by simp [shiftThree]

theorem shiftTwo_succ (d : ℕ) (y z : ℤ) :
    shiftTwo (d + 1) y z = shiftTwo d y z + levelTwo d y z := by
  simp [shiftTwo, sum_range_succ]

theorem shiftThree_succ (d : ℕ) (y z : ℤ) :
    shiftThree (d + 1) y z = shiftThree d y z + levelThree d y z := by
  simp [shiftThree, sum_range_succ]

/-- `curl b_d = u_d ⊗ u_d - u_{d+1} ⊗ u_{d+1}`. -/
theorem curl_level (d : ℕ) (y z : ℤ) :
    (levelThree d (y + 1) z - levelThree d y z) - (levelTwo d y (z + 1) - levelTwo d y z) =
      uni d y * uni d z - uni (d + 1) y * uni (d + 1) z := by
  have hy := ramp_succ_sub d y
  have hz := ramp_succ_sub d z
  unfold levelTwo levelThree
  linear_combination (uni d z) * hy + (uni (d + 1) y) * hz

/-- `curl a_d = u_0 ⊗ u_0 - u_d ⊗ u_d`. -/
theorem curl_shift (d : ℕ) (y z : ℤ) :
    (shiftThree d (y + 1) z - shiftThree d y z) - (shiftTwo d y (z + 1) - shiftTwo d y z) =
      uni 0 y * uni 0 z - uni d y * uni d z := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hb := curl_level d y z
    simp only [shiftTwo_succ, shiftThree_succ]
    linear_combination ih + hb

theorem levelTwo_ne_zero {d : ℕ} {y z : ℤ} (h : levelTwo d y z ≠ 0) :
    (0 ≤ y ∧ y ≤ (d : ℤ) + 1) ∧ (1 ≤ z ∧ z ≤ (d : ℤ) + 1) := by
  unfold levelTwo at h
  have hu : uni (d + 1) y ≠ 0 := fun h0 => h (by rw [h0]; ring)
  have hr : ramp d z ≠ 0 := fun h0 => h (by rw [h0]; ring)
  have h1 := uni_ne_zero hu
  have h2 := ramp_ne_zero hr
  refine ⟨⟨h1.1, ?_⟩, h2⟩
  have := h1.2
  push_cast at this
  exact this

theorem levelThree_ne_zero {d : ℕ} {y z : ℤ} (h : levelThree d y z ≠ 0) :
    (1 ≤ y ∧ y ≤ (d : ℤ) + 1) ∧ (0 ≤ z ∧ z ≤ (d : ℤ)) := by
  unfold levelThree at h
  have hr : ramp d y ≠ 0 := fun h0 => h (by rw [h0]; ring)
  have hu : uni d z ≠ 0 := fun h0 => h (by rw [h0]; ring)
  exact ⟨ramp_ne_zero hr, uni_ne_zero hu⟩

/-- The shift `a_d` is supported in the square `{0,…,d}²`. -/
theorem shiftTwo_ne_zero {d : ℕ} {y z : ℤ} (h : shiftTwo d y z ≠ 0) :
    (0 ≤ y ∧ y ≤ (d : ℤ)) ∧ (1 ≤ z ∧ z ≤ (d : ℤ)) := by
  unfold shiftTwo at h
  obtain ⟨j, hj, hne⟩ := exists_ne_zero_of_sum_ne_zero h
  have hjd : j < d := mem_range.mp hj
  have hs := levelTwo_ne_zero hne
  omega

theorem shiftThree_ne_zero {d : ℕ} {y z : ℤ} (h : shiftThree d y z ≠ 0) :
    (1 ≤ y ∧ y ≤ (d : ℤ)) ∧ (0 ≤ z ∧ z ≤ (d : ℤ)) := by
  unfold shiftThree at h
  obtain ⟨j, hj, hne⟩ := exists_ne_zero_of_sum_ne_zero h
  have hjd : j < d := mem_range.mp hj
  have hs := levelThree_ne_zero hne
  omega

/-! ### Squared norms in the transverse plane -/

/-- The spread flux `u_d ⊗ u_d` has squared norm at most `1/(d+1)²`. -/
theorem sum_spread_sq_le (d : ℕ) (s t : Finset ℤ) :
    ∑ y ∈ s, ∑ z ∈ t, (uni d y * uni d z) ^ 2 ≤ 1 / ((d : ℝ) + 1) ^ 2 := by
  have h1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hs := sum_uni_sq_le d s
  have ht := sum_uni_sq_le d t
  have hs0 : 0 ≤ ∑ y ∈ s, uni d y ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have ht0 : 0 ≤ ∑ z ∈ t, uni d z ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  calc ∑ y ∈ s, ∑ z ∈ t, (uni d y * uni d z) ^ 2
      = (∑ y ∈ s, uni d y ^ 2) * ∑ z ∈ t, uni d z ^ 2 := by
        rw [sum_mul_sum]
        exact sum_congr rfl fun y _ => sum_congr rfl fun z _ => mul_pow _ _ _
    _ ≤ (1 / ((d : ℝ) + 1)) * (1 / ((d : ℝ) + 1)) := mul_le_mul hs ht ht0 (by positivity)
    _ = 1 / ((d : ℝ) + 1) ^ 2 := by
        field_simp

/-- The bound `(1/3) (1/(d+1)² + 1/(d+2)²)` for the squared norm of the level field `b_d`. -/
@[expose] noncomputable def levelBound (d : ℕ) : ℝ :=
  (1 / 3) * (1 / ((d : ℝ) + 1) ^ 2 + 1 / ((d : ℝ) + 2) ^ 2)

theorem levelBound_nonneg (d : ℕ) : 0 ≤ levelBound d := by
  unfold levelBound
  positivity

theorem rampNormSq_mul_le (d : ℕ) :
    rampNormSq d * (1 / ((d : ℝ) + 1) + 1 / ((d : ℝ) + 2)) ≤ levelBound d := by
  have h1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have key : rampNormSq d * (1 / ((d : ℝ) + 1) + 1 / ((d : ℝ) + 2)) =
      (1 / 6) * (1 / ((d : ℝ) + 1) + 1 / ((d : ℝ) + 2)) ^ 2 := by
    unfold rampNormSq
    field_simp
    ring
  rw [key, levelBound]
  have hsq : (1 / ((d : ℝ) + 1) + 1 / ((d : ℝ) + 2)) ^ 2 ≤
      2 * (1 / ((d : ℝ) + 1) ^ 2 + 1 / ((d : ℝ) + 2) ^ 2) := by
    have h := sq_nonneg (1 / ((d : ℝ) + 1) - 1 / ((d : ℝ) + 2))
    have e1 : (1 / ((d : ℝ) + 1)) ^ 2 = 1 / ((d : ℝ) + 1) ^ 2 := by rw [div_pow, one_pow]
    have e2 : (1 / ((d : ℝ) + 2)) ^ 2 = 1 / ((d : ℝ) + 2) ^ 2 := by rw [div_pow, one_pow]
    nlinarith
  linarith

/-- The level field `b_d` has squared norm at most `levelBound d`. -/
theorem sum_level_sq_le (d : ℕ) (s t : Finset ℤ) :
    ∑ y ∈ s, ∑ z ∈ t, (levelTwo d y z ^ 2 + levelThree d y z ^ 2) ≤ levelBound d := by
  have h1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hu1 := sum_uni_sq_le (d + 1) s
  have hu0 := sum_uni_sq_le d t
  have hrs := sum_ramp_sq_le d s
  have hrt := sum_ramp_sq_le d t
  have hu1' : ∑ y ∈ s, uni (d + 1) y ^ 2 ≤ 1 / ((d : ℝ) + 2) := by
    refine hu1.trans (le_of_eq ?_)
    push_cast
    ring
  have n1 : 0 ≤ ∑ y ∈ s, uni (d + 1) y ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have n2 : 0 ≤ ∑ z ∈ t, ramp d z ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have n3 : 0 ≤ ∑ y ∈ s, ramp d y ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have n4 : 0 ≤ ∑ z ∈ t, uni d z ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hR := rampNormSq_nonneg d
  have e2 : ∑ y ∈ s, ∑ z ∈ t, levelTwo d y z ^ 2 =
      (∑ y ∈ s, uni (d + 1) y ^ 2) * ∑ z ∈ t, ramp d z ^ 2 := by
    rw [sum_mul_sum]
    refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
    unfold levelTwo
    ring
  have e3 : ∑ y ∈ s, ∑ z ∈ t, levelThree d y z ^ 2 =
      (∑ y ∈ s, ramp d y ^ 2) * ∑ z ∈ t, uni d z ^ 2 := by
    rw [sum_mul_sum]
    refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
    unfold levelThree
    ring
  have b2 : (∑ y ∈ s, uni (d + 1) y ^ 2) * ∑ z ∈ t, ramp d z ^ 2 ≤
      (1 / ((d : ℝ) + 2)) * rampNormSq d := mul_le_mul hu1' hrt n2 (by positivity)
  have b3 : (∑ y ∈ s, ramp d y ^ 2) * ∑ z ∈ t, uni d z ^ 2 ≤
      rampNormSq d * (1 / ((d : ℝ) + 1)) := mul_le_mul hrs hu0 n4 hR
  calc ∑ y ∈ s, ∑ z ∈ t, (levelTwo d y z ^ 2 + levelThree d y z ^ 2)
      = ∑ y ∈ s, ∑ z ∈ t, levelTwo d y z ^ 2 + ∑ y ∈ s, ∑ z ∈ t, levelThree d y z ^ 2 := by
        simp only [sum_add_distrib]
    _ ≤ (1 / ((d : ℝ) + 2)) * rampNormSq d + rampNormSq d * (1 / ((d : ℝ) + 1)) := by
        rw [e2, e3]
        exact add_le_add b2 b3
    _ = rampNormSq d * (1 / ((d : ℝ) + 1) + 1 / ((d : ℝ) + 2)) := by ring
    _ ≤ levelBound d := rampNormSq_mul_le d

/-! ### Series and tent sums -/

/-- `Σ_{r ≤ m} 1/(r+1)² ≤ 2 - 1/(m+1)`. -/
theorem sum_inv_sq_le (m : ℕ) :
    ∑ r ∈ range (m + 1), 1 / ((r : ℝ) + 1) ^ 2 ≤ 2 - 1 / ((m : ℝ) + 1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [sum_range_succ]
    have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have step : 1 / (((m + 1 : ℕ) : ℝ) + 1) ^ 2 ≤
        1 / ((m : ℝ) + 1) - 1 / (((m + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      rw [div_sub_div _ _ h1.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- `Σ_{r ≤ m} 1/(r+2)² ≤ 1 - 1/(m+2)`. -/
theorem sum_inv_sq_shift_le (m : ℕ) :
    ∑ r ∈ range (m + 1), 1 / ((r : ℝ) + 2) ^ 2 ≤ 1 - 1 / ((m : ℝ) + 2) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [sum_range_succ]
    have h2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have h3 : (0 : ℝ) < (m : ℝ) + 3 := by positivity
    have step : 1 / (((m + 1 : ℕ) : ℝ) + 2) ^ 2 ≤
        1 / ((m : ℝ) + 2) - 1 / (((m + 1 : ℕ) : ℝ) + 2) := by
      push_cast
      rw [div_sub_div _ _ h2.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

theorem inv_sq_min_le (a b : ℕ) (c : ℝ) (hc : 0 < c) :
    1 / (((min a b : ℕ) : ℝ) + c) ^ 2 ≤ 1 / ((a : ℝ) + c) ^ 2 + 1 / ((b : ℝ) + c) ^ 2 := by
  have ha : (0 : ℝ) ≤ 1 / ((a : ℝ) + c) ^ 2 := by positivity
  have hb : (0 : ℝ) ≤ 1 / ((b : ℝ) + c) ^ 2 := by positivity
  rcases le_total a b with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

theorem sum_range_reflect_inv_sq (m : ℕ) (c : ℝ) :
    ∑ y ∈ range (m + 1), 1 / (((m - y : ℕ) : ℝ) + c) ^ 2 =
      ∑ y ∈ range (m + 1), 1 / ((y : ℝ) + c) ^ 2 := by
  have h := sum_range_reflect (fun y : ℕ => 1 / ((y : ℝ) + c) ^ 2) (m + 1)
  simpa using h

/-- A row of the sheet: `Σ_{y ≤ m} 1/(min(y, m-y)+1)² ≤ 4`. -/
theorem tent_sum_le (m : ℕ) :
    ∑ y ∈ range (m + 1), 1 / (((min y (m - y) : ℕ) : ℝ) + 1) ^ 2 ≤ 4 := by
  have hS := sum_inv_sq_le m
  have hm : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
  calc ∑ y ∈ range (m + 1), 1 / (((min y (m - y) : ℕ) : ℝ) + 1) ^ 2
      ≤ ∑ y ∈ range (m + 1),
          (1 / ((y : ℝ) + 1) ^ 2 + 1 / (((m - y : ℕ) : ℝ) + 1) ^ 2) :=
        sum_le_sum fun y _ => inv_sq_min_le y (m - y) 1 one_pos
    _ = ∑ y ∈ range (m + 1), 1 / ((y : ℝ) + 1) ^ 2 +
          ∑ y ∈ range (m + 1), 1 / ((y : ℝ) + 1) ^ 2 := by
        rw [sum_add_distrib, sum_range_reflect_inv_sq]
    _ ≤ 4 := by linarith

/-- `Σ_{y ≤ m} 1/(min(y, m-y)+2)² ≤ 2`. -/
theorem tent_sum_shift_le (m : ℕ) :
    ∑ y ∈ range (m + 1), 1 / (((min y (m - y) : ℕ) : ℝ) + 2) ^ 2 ≤ 2 := by
  have hS := sum_inv_sq_shift_le m
  have hm : (0 : ℝ) ≤ 1 / ((m : ℝ) + 2) := by positivity
  calc ∑ y ∈ range (m + 1), 1 / (((min y (m - y) : ℕ) : ℝ) + 2) ^ 2
      ≤ ∑ y ∈ range (m + 1),
          (1 / ((y : ℝ) + 2) ^ 2 + 1 / (((m - y : ℕ) : ℝ) + 2) ^ 2) :=
        sum_le_sum fun y _ => inv_sq_min_le y (m - y) 2 two_pos
    _ = ∑ y ∈ range (m + 1), 1 / ((y : ℝ) + 2) ^ 2 +
          ∑ y ∈ range (m + 1), 1 / ((y : ℝ) + 2) ^ 2 := by
        rw [sum_add_distrib, sum_range_reflect_inv_sq]
    _ ≤ 2 := by linarith

/-- One row of walls: `Σ_{y ≤ m} levelBound (min(y, m-y)) ≤ 2`. -/
theorem tent_levelBound_sum_le (m : ℕ) :
    ∑ y ∈ range (m + 1), levelBound (min y (m - y)) ≤ 2 := by
  have h1 := tent_sum_le m
  have h2 := tent_sum_shift_le m
  have e : ∑ y ∈ range (m + 1), levelBound (min y (m - y)) =
      (1 / 3) * (∑ y ∈ range (m + 1), 1 / (((min y (m - y) : ℕ) : ℝ) + 1) ^ 2 +
        ∑ y ∈ range (m + 1), 1 / (((min y (m - y) : ℕ) : ℝ) + 2) ^ 2) := by
    rw [← sum_add_distrib, mul_sum]
    rfl
  rw [e]
  linarith

/-- The sheet part of the energy for an `(L+1) × (T+1)` rectangle:
`Σ 1/(depth+1)² ≤ 4 ((L+1) + (T+1))`, `depth` the minimum of the two tents. -/
theorem sheet_sum_le (L T : ℕ) :
    ∑ y₀ ∈ range (L + 1), ∑ y₁ ∈ range (T + 1),
        1 / (((min (min y₀ (L - y₀)) (min y₁ (T - y₁)) : ℕ) : ℝ) + 1) ^ 2 ≤
      4 * (((L : ℝ) + 1) + ((T : ℝ) + 1)) := by
  calc ∑ y₀ ∈ range (L + 1), ∑ y₁ ∈ range (T + 1),
        1 / (((min (min y₀ (L - y₀)) (min y₁ (T - y₁)) : ℕ) : ℝ) + 1) ^ 2
      ≤ ∑ y₀ ∈ range (L + 1), ∑ y₁ ∈ range (T + 1),
          (1 / (((min y₀ (L - y₀) : ℕ) : ℝ) + 1) ^ 2 +
            1 / (((min y₁ (T - y₁) : ℕ) : ℝ) + 1) ^ 2) :=
        sum_le_sum fun y₀ _ => sum_le_sum fun y₁ _ => inv_sq_min_le _ _ 1 one_pos
    _ = ((T : ℝ) + 1) * ∑ y₀ ∈ range (L + 1), 1 / (((min y₀ (L - y₀) : ℕ) : ℝ) + 1) ^ 2 +
          ((L : ℝ) + 1) * ∑ y₁ ∈ range (T + 1), 1 / (((min y₁ (T - y₁) : ℕ) : ℝ) + 1) ^ 2 := by
        simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_sum]
        push_cast
        ring
    _ ≤ ((T : ℝ) + 1) * 4 + ((L : ℝ) + 1) * 4 := by
        gcongr
        · exact tent_sum_le L
        · exact tent_sum_le T
    _ = 4 * (((L : ℝ) + 1) + ((T : ℝ) + 1)) := by ring

end FroehlichSpencer.FS82.Wilson

end
