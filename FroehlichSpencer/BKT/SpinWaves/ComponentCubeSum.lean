/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.Covers

/-!
# Dyadic packing bound for the cubed diameters of separated components
-/

@[expose] public section

namespace FroehlichSpencer.BKT.SpinWaves

/-- The constant `2 ^ (7/4)` is at least `10/3`. -/
lemma cubeSum_ten_thirds_le_two_rpow : (10 / 3 : ℝ) ≤ (2 : ℝ) ^ (7 / 4 : ℝ) := by
  have h4 : ((2 : ℝ) ^ (7 / 4 : ℝ)) ^ 4 = 2 ^ 7 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (7 / 4 : ℝ)) 4, ← Real.rpow_mul (by norm_num)]
    norm_num
  by_contra h
  push Not at h
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ (7 / 4 : ℝ) := by positivity
  have := pow_lt_pow_left₀ h h0 (by norm_num : (4 : ℕ) ≠ 0)
  rw [h4] at this
  norm_num at this

/-- Root separation gives `d ^ α ≤ n / 200`. -/
lemma cubeSum_rpow_le_of_root {D n : ℝ} (hD : 1 ≤ D)
    (h : (2 ^ 16 / 128 : ℝ) * D ^ (7 / 4 : ℝ) ≤ 5 / 2 * n + D) : D ^ (7 / 4 : ℝ) ≤ n / 200 := by
  have h1 : D ≤ D ^ (7 / 4 : ℝ) := Real.self_le_rpow_of_one_le hD (by norm_num)
  linarith only [hD, h, h1]

/-- The real arithmetic of one dyadic class. -/
lemma cubeSum_class_arith {n y m c P Q : ℝ} (hc0 : 0 ≤ c) (hy : 1 ≤ y)
    (hyn : y ≤ n / 200) (hm1 : 1023 * y ≤ m) (hm2 : m ≤ 1024 * y)
    (hcm : c * m ^ 2 ≤ (6 * n + m) ^ 2) (hPQ : P ≤ Q * y ^ 2) (hQ : 0 ≤ Q) :
    c * 8 * P ≤ n ^ 2 / 300 * Q := by
  have h1 : 6 * n + m ≤ 11.12 * n := by linarith only [hyn, hm2]
  have hm0 : 0 ≤ 6 * n + m := by linarith only [hy, hyn, hm1]
  have h2 : (6 * n + m) ^ 2 ≤ 124 * n ^ 2 := by
    have := pow_le_pow_left₀ hm0 h1 2
    nlinarith only [this, sq_nonneg n]
  have h3 : c * (1023 * y) ^ 2 ≤ c * m ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hm1 2) hc0
  have h4 : c * y ^ 2 ≤ n ^ 2 / 8000 := by nlinarith only [hcm, h2, h3]
  calc c * 8 * P ≤ c * 8 * (Q * y ^ 2) := by gcongr
    _ = 8 * Q * (c * y ^ 2) := by ring
    _ ≤ 8 * Q * (n ^ 2 / 8000) := by gcongr
    _ ≤ n ^ 2 / 300 * Q := by
      have := mul_nonneg hQ (sq_nonneg n)
      nlinarith only [this]

/-- Geometric sum bound. -/
lemma cubeSum_geom_sum_le (K : ℕ) : ∑ ℓ ∈ Finset.range K, (18 / 25 : ℝ) ^ ℓ ≤ 25 / 7 := by
  have h : ∀ K : ℕ, ∑ ℓ ∈ Finset.range K, (18 / 25 : ℝ) ^ ℓ = 25 / 7 * (1 - (18 / 25) ^ K) := by
    intro K
    induction K with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [h]
  have : (0 : ℝ) ≤ (18 / 25) ^ K := by positivity
  linarith only [this]

/-- The bound for a single dyadic class. -/
lemma cubeSum_class_sum_le {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (d : ι → ℕ) (dist : ι → ι → ℕ) (n : ℝ) (hn : 1 ≤ n) (R : ℕ) (hR : (R : ℝ) ≤ 3 * n)
    (hd : ∀ i ∈ I, 1 ≤ d i)
    (hroot : ∀ i ∈ I, (2 ^ 16 / 128 : ℝ) * (d i : ℝ) ^ (7 / 4 : ℝ) ≤ 5 / 2 * n + d i)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      (2 ^ 16 / 25 : ℝ) * ((min (d i) (d j) : ℕ) : ℝ) ^ (7 / 4 : ℝ) ≤
        ((dist i j + d i + d j : ℕ) : ℝ))
    (hpack : ∀ J ⊆ I, ∀ m : ℕ, 1 ≤ m →
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j → 2 * m ≤ dist i j) → J.card ≤ (2 * R / m + 1) ^ 2)
    (ℓ : ℕ) :
    ∑ i ∈ I.filter (fun i => Nat.log 2 (d i) = ℓ), (d i : ℝ) ^ 3 ≤
      n ^ 2 / 300 * (18 / 25 : ℝ) ^ ℓ := by
  set J := I.filter (fun i => Nat.log 2 (d i) = ℓ) with hJdef
  have hn0 : (0 : ℝ) ≤ n := by linarith only [hR]
  by_cases hJ : J = ∅
  · rw [hJ]; simp only [Finset.sum_empty]; positivity
  obtain ⟨i0, hi0⟩ := Finset.nonempty_iff_ne_empty.2 hJ
  have hbd : ∀ i ∈ J, 2 ^ ℓ ≤ d i ∧ d i < 2 ^ (ℓ + 1) := by
    intro i hi
    rw [hJdef, Finset.mem_filter] at hi
    have hd1 : d i ≠ 0 := by have := hd i hi.1; omega
    refine ⟨?_, ?_⟩
    · rw [← hi.2]; exact Nat.pow_log_le_self 2 hd1
    · rw [← hi.2]; exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hJI : J ⊆ I := Finset.filter_subset _ _
  set x : ℝ := (2 : ℝ) ^ (7 / 4 : ℝ) with hx
  have hx1 : (10 / 3 : ℝ) ≤ x := cubeSum_ten_thirds_le_two_rpow
  set y : ℝ := x ^ ℓ with hy
  have hy1 : 1 ≤ y := one_le_pow₀ (by linarith only [hx1])
  have hy2 : ((2 : ℝ) ^ ℓ) ≤ y := pow_le_pow_left₀ (by norm_num) (by linarith only [hx1]) ℓ
  have hcomm : ((2 : ℝ) ^ ℓ) ^ (7 / 4 : ℝ) = y :=
    (Real.rpow_pow_comm (by norm_num) _ _).symm
  have hyle : ∀ i ∈ J, y ≤ (d i : ℝ) ^ (7 / 4 : ℝ) := by
    intro i hi
    rw [← hcomm]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    exact_mod_cast (hbd i hi).1
  have hyn : y ≤ n / 200 :=
    (hyle i0 hi0).trans (cubeSum_rpow_le_of_root (by exact_mod_cast hd i0 (hJI hi0))
      (hroot i0 (hJI hi0)))
  set m : ℕ := ⌊1024 * y⌋₊ with hm
  have hm2 : (m : ℝ) ≤ 1024 * y := Nat.floor_le (by positivity)
  have hm3 : 1024 * y < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hm1 : 1023 * y ≤ (m : ℝ) := by linarith only [hy1, hm3]
  have hm0 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := by linarith only [hy1, hm1]
    exact_mod_cast this
  have hdlt : ∀ i ∈ J, (d i : ℝ) < 2 * 2 ^ ℓ := by
    intro i hi
    have := (hbd i hi).2
    have h' : (d i : ℝ) < ((2 ^ (ℓ + 1) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h'
    linarith only [h', pow_succ (2 : ℝ) ℓ]
  have hsepJ : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → 2 * m ≤ dist i j := by
    intro i hi j hj hij
    have h1 := hsep i (hJI hi) j (hJI hj) hij
    have hmin : (2 : ℝ) ^ ℓ ≤ ((min (d i) (d j) : ℕ) : ℝ) := by
      have : 2 ^ ℓ ≤ min (d i) (d j) := le_min (hbd i hi).1 (hbd j hj).1
      exact_mod_cast this
    have h2 : y ≤ ((min (d i) (d j) : ℕ) : ℝ) ^ (7 / 4 : ℝ) := by
      rw [← hcomm]
      exact Real.rpow_le_rpow (by positivity) hmin (by norm_num)
    rw [Nat.cast_add, Nat.cast_add] at h1
    have h3 := hdlt i hi
    have h4 := hdlt j hj
    have : ((2 * m : ℕ) : ℝ) ≤ (dist i j : ℝ) := by
      push_cast
      nlinarith only [hy2, hm2, h1, h2, h3, h4]
    exact_mod_cast this
  have hcard := hpack J hJI m hm0 hsepJ
  set q : ℕ := 2 * R / m with hq
  have hq1 : (q : ℝ) * m ≤ 2 * R := by
    have : q * m ≤ 2 * R := Nat.div_mul_le_self _ _
    exact_mod_cast this
  have hcR : ((J.card : ℕ) : ℝ) ≤ ((q : ℝ) + 1) ^ 2 := by exact_mod_cast hcard
  have hcm : (J.card : ℝ) * (m : ℝ) ^ 2 ≤ (6 * n + m) ^ 2 := by
    have h1 : ((q : ℝ) + 1) * m ≤ 6 * n + m := by nlinarith only [hR, hq1]
    have h2 : (0 : ℝ) ≤ ((q : ℝ) + 1) * m := by positivity
    calc (J.card : ℝ) * (m : ℝ) ^ 2 ≤ ((q : ℝ) + 1) ^ 2 * (m : ℝ) ^ 2 := by gcongr
      _ = (((q : ℝ) + 1) * m) ^ 2 := by ring
      _ ≤ (6 * n + m) ^ 2 := pow_le_pow_left₀ h2 h1 2
  have hP : (8 : ℝ) ^ ℓ ≤ (18 / 25 : ℝ) ^ ℓ * y ^ 2 := by
    have h8 : (8 : ℝ) ≤ 18 / 25 * x ^ 2 := by nlinarith only [hx1]
    have := pow_le_pow_left₀ (by norm_num) h8 ℓ
    rw [mul_pow, ← pow_mul, mul_comm 2 ℓ, pow_mul] at this
    rw [hy]
    simpa [← pow_mul, mul_comm ℓ 2, pow_mul] using this
  have hcube : ∀ i ∈ J, (d i : ℝ) ^ 3 ≤ 8 * 8 ^ ℓ := by
    intro i hi
    have h0 : (0 : ℝ) ≤ d i := by positivity
    have := pow_le_pow_left₀ h0 (hdlt i hi).le 3
    have h8 : ((2 : ℝ) ^ ℓ) ^ 3 = 8 ^ ℓ := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    calc (d i : ℝ) ^ 3 ≤ (2 * 2 ^ ℓ) ^ 3 := this
      _ = 8 * 8 ^ ℓ := by rw [mul_pow, h8]; norm_num
  calc ∑ i ∈ J, (d i : ℝ) ^ 3 ≤ ∑ _i ∈ J, (8 * 8 ^ ℓ : ℝ) := Finset.sum_le_sum hcube
    _ = J.card * 8 * 8 ^ ℓ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ n ^ 2 / 300 * (18 / 25 : ℝ) ^ ℓ :=
      cubeSum_class_arith (by positivity) hy1 hyn hm1 hm2 hcm hP (by positivity)


theorem sum_cube_le_of_scale_separation {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (d : ι → ℕ) (dist : ι → ι → ℕ) (n : ℝ) (hn : 1 ≤ n) (R : ℕ) (hR : (R : ℝ) ≤ 3 * n)
    (hd : ∀ i ∈ I, 1 ≤ d i)
    (hroot : ∀ i ∈ I, (2 ^ 16 / 128 : ℝ) * (d i : ℝ) ^ (7 / 4 : ℝ) ≤ 5 / 2 * n + d i)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      (2 ^ 16 / 25 : ℝ) * ((min (d i) (d j) : ℕ) : ℝ) ^ (7 / 4 : ℝ) ≤
        ((dist i j + d i + d j : ℕ) : ℝ))
    (hpack : ∀ J ⊆ I, ∀ m : ℕ, 1 ≤ m →
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j → 2 * m ≤ dist i j) → J.card ≤ (2 * R / m + 1) ^ 2) :
    ∑ i ∈ I, (d i : ℝ) ^ 3 ≤ n ^ 2 / 50 := by
  set K : ℕ := I.sup (fun i => Nat.log 2 (d i)) + 1 with hK
  have hmaps : ∀ i ∈ I, Nat.log 2 (d i) ∈ Finset.range K := by
    intro i hi
    rw [Finset.mem_range, hK]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun i => Nat.log 2 (d i)) hi)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ ℓ ∈ Finset.range K, ∑ i ∈ I with Nat.log 2 (d i) = ℓ, (d i : ℝ) ^ 3
      ≤ ∑ ℓ ∈ Finset.range K, n ^ 2 / 300 * (18 / 25 : ℝ) ^ ℓ :=
        Finset.sum_le_sum fun ℓ _ =>
          cubeSum_class_sum_le I d dist n hn R hR hd hroot hsep hpack ℓ
    _ = n ^ 2 / 300 * ∑ ℓ ∈ Finset.range K, (18 / 25 : ℝ) ^ ℓ := by rw [Finset.mul_sum]
    _ ≤ n ^ 2 / 300 * (25 / 7) := by
        gcongr
        exact cubeSum_geom_sum_le K
    _ ≤ n ^ 2 / 50 := by nlinarith only [sq_nonneg n]

end FroehlichSpencer.BKT.SpinWaves

end
