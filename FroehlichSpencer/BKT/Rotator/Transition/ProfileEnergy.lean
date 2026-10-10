/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Transition.L1Distance
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# The logarithmic McBryan–Spencer profile and its Dirichlet energy

The profile around `u` is `x ↦ Σ_{s = r+1}^{R} 1/s` with `r = ‖x - u‖₁`: it equals the harmonic
number `H_R ≥ log(R+1)` at `u`, vanishes at `ℓ¹` distance `≥ R`, changes by at most `1/max(r,1)`
across a bond, and its Dirichlet energy over the nearest-neighbour bonds of any finite domain is at
most `8 H_R + 10`, because the `ℓ¹` sphere of radius `r ≥ 1` has at most `4r + 2` points.
-/

@[expose] public section

open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Transition

open FroehlichSpencer.BKT.Rotator.Ginibre

/-- `Σ_{s = r+1}^{R} 1/s`, zero when `r ≥ R`. -/
def tailHarmonic (R r : ℕ) : ℝ :=
  ∑ s ∈ Finset.Ioc r R, (1 : ℝ) / s

theorem tailHarmonic_nonneg (R r : ℕ) : 0 ≤ tailHarmonic R r :=
  Finset.sum_nonneg fun s _ => by positivity

theorem tailHarmonic_eq_zero {R r : ℕ} (h : R ≤ r) : tailHarmonic R r = 0 := by
  unfold tailHarmonic
  rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]

theorem log_add_one_le_tailHarmonic_zero (R : ℕ) : Real.log (R + 1) ≤ tailHarmonic R 0 := by
  have h1 := log_add_one_le_harmonic R
  have h2 : ((harmonic R : ℚ) : ℝ) = tailHarmonic R 0 := by
    rw [harmonic_eq_sum_Icc]
    unfold tailHarmonic
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    rfl
  rw [h2] at h1
  simpa using h1

/-- The McBryan–Spencer profile around `u`. -/
def msProfile (R : ℕ) (u x : ℤ × ℤ) : ℝ :=
  tailHarmonic R (l1Norm (x - u))

theorem msProfile_self (R : ℕ) (u : ℤ × ℤ) : msProfile R u u = tailHarmonic R 0 := by
  simp [msProfile, l1Norm]

theorem msProfile_eq_zero {R : ℕ} {u x : ℤ × ℤ} (h : R ≤ l1Norm (x - u)) : msProfile R u x = 0 :=
  tailHarmonic_eq_zero h

private lemma tailHarmonic_sub_succ (R a : ℕ) :
    tailHarmonic R a - tailHarmonic R (a + 1) = if a < R then 1 / ((a : ℝ) + 1) else 0 := by
  by_cases h : a < R
  · have e : Finset.Ioc a R = insert (a + 1) (Finset.Ioc (a + 1) R) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
    unfold tailHarmonic
    rw [e, Finset.sum_insert (by simp)]
    simp [h]
  · rw [tailHarmonic_eq_zero (by omega), tailHarmonic_eq_zero (by omega)]
    simp [h]

/-- The squared-increment bound across a bond, as a function of the nearer-to-`u` radius. -/
private def profileBound (R a : ℕ) : ℝ :=
  if a ≤ R then (1 / ((max a 1 : ℕ) : ℝ)) ^ 2 else 0

private lemma profileBound_nonneg (R a : ℕ) : 0 ≤ profileBound R a := by
  unfold profileBound
  split_ifs <;> positivity

private lemma profileBound_le_one (R a : ℕ) : profileBound R a ≤ 1 := by
  unfold profileBound
  split_ifs
  · have h1 : (1 : ℝ) ≤ ((max a 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right a 1
    have h2 : 1 / ((max a 1 : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; exact h1
    have h3 : 0 ≤ 1 / ((max a 1 : ℕ) : ℝ) := by positivity
    nlinarith
  · norm_num

private lemma sq_step (R a b : ℕ) (h : b = a + 1 ∨ a = b + 1) :
    (tailHarmonic R a - tailHarmonic R b) ^ 2 ≤ profileBound R a := by
  rcases h with rfl | rfl
  · rw [tailHarmonic_sub_succ]
    unfold profileBound
    by_cases h1 : a < R
    · have h2 : a ≤ R := h1.le
      rw [ite_eq_left_of_eq_true _ _ (by simp [h1]), ite_eq_left_of_eq_true _ _ (by simp [h2])]
      have hp : (0 : ℝ) < ((max a 1 : ℕ) : ℝ) := by
        exact_mod_cast lt_of_lt_of_le one_pos (le_max_right a 1)
      have hle : ((max a 1 : ℕ) : ℝ) ≤ (a : ℝ) + 1 := by
        have : max a 1 ≤ a + 1 := by omega
        exact_mod_cast this
      exact pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le hp hle) 2
    · rw [ite_eq_right_of_eq_false _ _ (by simp [h1])]
      split_ifs <;> simp
  · have e : (tailHarmonic R (b + 1) - tailHarmonic R b) ^ 2 =
        (tailHarmonic R b - tailHarmonic R (b + 1)) ^ 2 := by ring
    rw [e, tailHarmonic_sub_succ]
    unfold profileBound
    have hm : max (b + 1) 1 = b + 1 := by omega
    by_cases h1 : b < R
    · rw [ite_eq_left_of_eq_true _ _ (by simp [h1]), ite_eq_left_of_eq_true _ _ (by simp; omega), hm]
      push_cast
      exact le_rfl
    · rw [ite_eq_right_of_eq_false _ _ (by simp [h1]), ite_eq_right_of_eq_false _ _ (by simp; omega)]
      simp

private lemma l1_step {x y : ℤ × ℤ} (u : ℤ × ℤ) (h : LatticeStep x y) :
    l1Norm (y - u) = l1Norm (x - u) + 1 ∨ l1Norm (x - u) = l1Norm (y - u) + 1 := by
  rcases h with rfl | rfl <;> simp only [l1Norm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add,
    Prod.snd_add] <;> omega

private lemma sq_step_ms (R : ℕ) (u : ℤ × ℤ) {x y : ℤ × ℤ} (h : LatticeStep x y) :
    (msProfile R u x - msProfile R u y) ^ 2 ≤ profileBound R (l1Norm (x - u)) := by
  unfold msProfile
  have := l1_step u h
  refine sq_step R _ _ ?_
  omega

theorem abs_msProfile_sub_le_one (R : ℕ) (u : ℤ × ℤ) {x y : ℤ × ℤ} (h : LatticeStep x y) :
    |msProfile R u x - msProfile R u y| ≤ 1 := by
  rw [← sq_le_one_iff_abs_le_one]
  exact (sq_step_ms R u h).trans (profileBound_le_one _ _)

private lemma sum_inv_sq_le_two (R : ℕ) :
    ∑ j ∈ Finset.Ioc 0 R, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · simp
  · have e : Finset.Ioc 0 R = insert 1 (Finset.Ioc 1 R) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
    rw [e, Finset.sum_insert (by simp)]
    have h := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := R) one_ne_zero hR
    have h2 : (0 : ℝ) ≤ (R : ℝ)⁻¹ := by positivity
    simp only [one_div] at h ⊢
    norm_num at h ⊢
    linarith

private lemma fiber_card_le (R : ℕ) (u : ℤ × ℤ) (j : ℕ) (hj : 1 ≤ j) :
    ((Finset.Icc (u.1 - R) (u.1 + R) ×ˢ Finset.Icc (u.2 - R) (u.2 + R)).filter
      fun x => l1Norm (x - u) = j).card ≤ 4 * j + 2 := by
  have h := Finset.card_le_card_of_injOn
    (s := (Finset.Icc (u.1 - R) (u.1 + R) ×ˢ Finset.Icc (u.2 - R) (u.2 + R)).filter
      fun x => l1Norm (x - u) = j)
    (t := Finset.Icc (u.1 - j) (u.1 + j) ×ˢ (Finset.univ : Finset Bool))
    (fun x => (x.1, decide (0 ≤ x.2 - u.2))) ?_ ?_
  · calc _ ≤ _ := h
      _ = 4 * j + 2 := by
        simp only [Finset.card_product, Int.card_Icc, Finset.card_univ, Fintype.card_bool]
        omega
  · intro x hx
    obtain ⟨hxD, hxn⟩ := Finset.mem_filter.mp hx
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hxD
    simp only [l1Norm, Prod.fst_sub, Prod.snd_sub] at hxn
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true]
    omega
  · intro x hx y hy hxy
    obtain ⟨hxD, hxn⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyD, hyn⟩ := Finset.mem_filter.mp hy
    simp only [l1Norm, Prod.fst_sub, Prod.snd_sub] at hxn hyn
    simp only [Prod.mk.injEq, decide_eq_decide] at hxy
    obtain ⟨x1, x2⟩ := x
    obtain ⟨y1, y2⟩ := y
    simp only at hxy hxn hyn ⊢
    ext
    · exact hxy.1
    · simp only
      omega

/-- The Dirichlet energy of the profile over the positive nearest-neighbour bonds of any finite
domain. -/
theorem msProfile_energy_le (R : ℕ) (u : ℤ × ℤ) (Λ : Finset (ℤ × ℤ)) :
    ∑ b : Λ × Λ, (if LatticeStep (b.1 : ℤ × ℤ) (b.2 : ℤ × ℤ) then
        (msProfile R u b.1 - msProfile R u b.2) ^ 2 else 0) ≤ 8 * tailHarmonic R 0 + 10 := by
  set D : Finset (ℤ × ℤ) :=
    (Finset.Icc (u.1 - R) (u.1 + R) ×ˢ Finset.Icc (u.2 - R) (u.2 + R)).filter
      (fun x => l1Norm (x - u) ≤ R) with hD
  have key : ∀ x y : ℤ × ℤ, (if LatticeStep x y then
      (msProfile R u x - msProfile R u y) ^ 2 else 0) ≤
      (if y = x + (1, 0) then profileBound R (l1Norm (x - u)) else 0) +
      (if y = x + (0, 1) then profileBound R (l1Norm (x - u)) else 0) := by
    intro x y
    have hb := profileBound_nonneg R (l1Norm (x - u))
    by_cases h1 : y = x + (1, 0)
    · by_cases h2 : y = x + (0, 1)
      · exfalso
        rw [h1] at h2
        have := congrArg Prod.fst h2
        simp at this
      · have hs : LatticeStep x y := Or.inl h1
        simp only [eq_true hs, eq_true h1, eq_false h2, ↓reduceIte]
        linarith [sq_step_ms R u hs]
    · by_cases h2 : y = x + (0, 1)
      · have hs : LatticeStep x y := Or.inr h2
        simp only [eq_true hs, eq_false h1, eq_true h2, ↓reduceIte]
        linarith [sq_step_ms R u hs]
      · have hs : ¬ LatticeStep x y := by
          rintro (h | h)
          · exact h1 h
          · exact h2 h
        simp only [eq_false hs, eq_false h1, eq_false h2, ↓reduceIte]
        linarith
  have step1 : ∑ b : Λ × Λ, (if LatticeStep (b.1 : ℤ × ℤ) (b.2 : ℤ × ℤ) then
        (msProfile R u b.1 - msProfile R u b.2) ^ 2 else 0) ≤
      ∑ x ∈ Λ, 2 * profileBound R (l1Norm (x - u)) := by
    calc _ ≤ ∑ b : Λ × Λ, ((if (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) then
              profileBound R (l1Norm ((b.1 : ℤ × ℤ) - u)) else 0) +
            (if (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1) then
              profileBound R (l1Norm ((b.1 : ℤ × ℤ) - u)) else 0)) :=
          Finset.sum_le_sum fun b _ => key _ _
      _ = ∑ x : Λ, ∑ y : Λ, ((if (y : ℤ × ℤ) = (x : ℤ × ℤ) + (1, 0) then
              profileBound R (l1Norm ((x : ℤ × ℤ) - u)) else 0) +
            (if (y : ℤ × ℤ) = (x : ℤ × ℤ) + (0, 1) then
              profileBound R (l1Norm ((x : ℤ × ℤ) - u)) else 0)) :=
          Fintype.sum_prod_type _
      _ = ∑ x : Λ, ∑ y ∈ Λ, ((if y = (x : ℤ × ℤ) + (1, 0) then
              profileBound R (l1Norm ((x : ℤ × ℤ) - u)) else 0) +
            (if y = (x : ℤ × ℤ) + (0, 1) then
              profileBound R (l1Norm ((x : ℤ × ℤ) - u)) else 0)) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_coe_sort Λ
            (fun y => (if y = (x : ℤ × ℤ) + (1, 0) then
              profileBound R (l1Norm ((x : ℤ × ℤ) - u)) else 0) +
            (if y = (x : ℤ × ℤ) + (0, 1) then
              profileBound R (l1Norm ((x : ℤ × ℤ) - u)) else 0))
      _ = ∑ x ∈ Λ, ∑ y ∈ Λ, ((if y = x + (1, 0) then
              profileBound R (l1Norm (x - u)) else 0) +
            (if y = x + (0, 1) then profileBound R (l1Norm (x - u)) else 0)) :=
          Finset.sum_coe_sort Λ (fun x => ∑ y ∈ Λ, ((if y = x + (1, 0) then
              profileBound R (l1Norm (x - u)) else 0) +
            (if y = x + (0, 1) then profileBound R (l1Norm (x - u)) else 0)))
      _ ≤ ∑ x ∈ Λ, 2 * profileBound R (l1Norm (x - u)) := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
          have hb := profileBound_nonneg R (l1Norm (x - u))
          split_ifs <;> linarith
  refine step1.trans ?_
  have step2 : ∑ x ∈ Λ, 2 * profileBound R (l1Norm (x - u)) ≤
      ∑ x ∈ D, 2 * profileBound R (l1Norm (x - u)) := by
    rw [← Finset.sum_filter_of_ne (p := fun x => x ∈ D)]
    · refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (Finset.mem_filter.mp hx).2) ?_
      intro x _ _
      have := profileBound_nonneg R (l1Norm (x - u))
      linarith
    · intro x _ hx
      by_contra hxD
      apply hx
      have : profileBound R (l1Norm (x - u)) = 0 := by
        unfold profileBound
        split_ifs with hle
        · exfalso
          apply hxD
          rw [hD, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
          simp only [l1Norm, Prod.fst_sub, Prod.snd_sub] at hle ⊢
          omega
        · rfl
      rw [this]; ring
  refine step2.trans ?_
  have hmaps : ∀ x ∈ D, l1Norm (x - u) ∈ insert 0 (Finset.Ioc 0 R) := by
    intro x hx
    have hx2 : l1Norm (x - u) ≤ R := (Finset.mem_filter.mp hx).2
    rw [Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps (fun j => 2 * profileBound R j)]
  have hzero : (D.filter fun x => l1Norm (x - u) = 0).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨-, ha⟩ := Finset.mem_filter.mp ha
    obtain ⟨-, hb⟩ := Finset.mem_filter.mp hb
    simp only [l1Norm, Prod.fst_sub, Prod.snd_sub] at ha hb
    ext <;> omega
  have hterm : ∀ j ∈ Finset.Ioc 0 R,
      ∑ i ∈ D with l1Norm (i - u) = j, 2 * profileBound R j ≤
        8 * (1 / (j : ℝ)) + 4 * (1 / (j : ℝ) ^ 2) := by
    intro j hj
    rw [Finset.mem_Ioc] at hj
    rw [Finset.sum_const, nsmul_eq_mul]
    have hsub : (D.filter fun x => l1Norm (x - u) = j) ⊆
        ((Finset.Icc (u.1 - R) (u.1 + R) ×ˢ Finset.Icc (u.2 - R) (u.2 + R)).filter
          fun x => l1Norm (x - u) = j) := by
      intro x hx
      simp only [hD, Finset.mem_filter] at hx ⊢
      tauto
    have hc := (Finset.card_le_card hsub).trans (fiber_card_le R u j hj.1)
    have hc' : (((D.filter fun x => l1Norm (x - u) = j).card : ℕ) : ℝ) ≤ 4 * j + 2 := by
      exact_mod_cast hc
    have hpb : profileBound R j = (1 / (j : ℝ)) ^ 2 := by
      unfold profileBound
      simp only [eq_true hj.2, ↓reduceIte, max_eq_left (show 1 ≤ j from hj.1)]
    rw [hpb]
    have hjpos : (0 : ℝ) < j := by exact_mod_cast hj.1
    have e : 8 * (1 / (j : ℝ)) + 4 * (1 / (j : ℝ) ^ 2) = (4 * j + 2) * (2 * (1 / (j : ℝ)) ^ 2) := by
      field_simp
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hc' (by positivity)
  rw [Finset.sum_insert (by simp)]
  have h0 : ∑ i ∈ D with l1Norm (i - u) = 0, 2 * profileBound R 0 ≤ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hpb : profileBound R 0 = 1 := by
      unfold profileBound
      simp
    rw [hpb]
    have : (((D.filter fun x => l1Norm (x - u) = 0).card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hzero
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hH : ∑ j ∈ Finset.Ioc 0 R, (1 : ℝ) / (j : ℝ) = tailHarmonic R 0 := rfl
  rw [hH] at hsum
  have h2 := sum_inv_sq_le_two R
  linarith

theorem cosh_sub_one_le_sq {t : ℝ} (ht : |t| ≤ 1) : Real.cosh t - 1 ≤ t ^ 2 := by
  have h1 := Real.cosh_le_exp_half_sq t
  have h2 : t ^ 2 ≤ 1 := by
    have := sq_abs t
    nlinarith [abs_nonneg t]
  have h3 : |t ^ 2 / 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have h4 := Real.abs_exp_sub_one_sub_id_le h3
  have h5 := (abs_le.mp h4).2
  nlinarith [sq_nonneg t]

end FroehlichSpencer.BKT.Rotator.Transition

end
