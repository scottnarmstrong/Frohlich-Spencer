/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileA3Components
public import Mathlib.Algebra.Order.Floor.Semiring

/-! # Dyadic path charging for collapsed terminal profiles

The module proves the quantitative dyadic summation and the final `9/8` path comparison.  The
path-packing premise records the one-dimensional count obtained by charging separated components
in their order along a shortest quotient path.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT

variable {ι : Type*}

private theorem sum_three_fourth_pow_le_four (n : ℕ) :
    ∑ k ∈ Finset.range n, ((3 : ℝ) / 4) ^ k ≤ 4 := by
  have hstrong : ∀ n : ℕ,
      ∑ k ∈ Finset.range n, ((3 : ℝ) / 4) ^ k ≤ 4 * (1 - ((3 : ℝ) / 4) ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        have hp : 0 ≤ ((3 : ℝ) / 4) ^ n := pow_nonneg (by norm_num) _
        rw [pow_succ]
        nlinarith [ih]
  have h := hstrong n
  have hp : 0 ≤ ((3 : ℝ) / 4) ^ n := pow_nonneg (by norm_num) _
  nlinarith

private theorem sum_two_pow_succ (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (n + 2) - 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num [pow_succ]
      ring

/-- At exponent `7/4`, the dyadic growth dominates the geometric ratio used in the path charge. -/
theorem profileA3_dyadic_power_lower (k : ℕ) :
    (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k ≤
      (2 : ℝ) ^ ((7 / 4 : ℝ) * k) := by
  have hbase : (8 / 3 : ℝ) ≤ (2 : ℝ) ^ (7 / 4 : ℝ) := by
    let A : ℝ := 8 / 3
    let B : ℝ := (2 : ℝ) ^ (7 / 4 : ℝ)
    have hB : 0 ≤ B := Real.rpow_nonneg (by norm_num) _
    have hpowMul : B ^ 4 = 128 := by
      calc
        B ^ 4 = B ^ (4 : ℝ) := (Real.rpow_natCast B 4).symm
        _ = (2 : ℝ) ^ ((7 / 4 : ℝ) * 4) := (Real.rpow_mul (by norm_num) _ _).symm
        _ = 128 := by norm_num [B]
    have hA4 : A ^ 4 ≤ B ^ 4 := by rw [hpowMul]; norm_num [A]
    have hAB := le_of_pow_le_pow_left₀ (by norm_num : 4 ≠ 0) hB hA4
    simpa [A, B] using hAB
  have hpow : ((8 : ℝ) / 3) ^ k ≤ ((2 : ℝ) ^ (7 / 4 : ℝ)) ^ k :=
    pow_le_pow_left₀ (by norm_num) hbase k
  calc
    (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k = ((8 : ℝ) / 3) ^ k := by
      rw [← mul_pow]
      ring
    _ ≤ ((2 : ℝ) ^ (7 / 4 : ℝ)) ^ k := hpow
    _ = (2 : ℝ) ^ ((7 / 4 : ℝ) * k) := by
      calc
        ((2 : ℝ) ^ (7 / 4 : ℝ)) ^ k = ((2 : ℝ) ^ (7 / 4 : ℝ)) ^ (k : ℝ) :=
          (Real.rpow_natCast _ _).symm
        _ = (2 : ℝ) ^ ((7 / 4 : ℝ) * k) := (Real.rpow_mul (by norm_num) _ _).symm

/-- Pairwise Appendix-D separation, after the `40D` component losses, gives enough spacing for
two components in the same dyadic size bin. -/
theorem profileA3_sameBin_component_positions_separated
    {L : ℕ} (D D' : ℝ) (k : ℕ) (C C' : Finset (Site L)) (p p' : ℝ)
    (hDlo : (2 : ℝ) ^ k ≤ D) (hDhi : D < (2 : ℝ) ^ (k + 1))
    (hD'lo : (2 : ℝ) ^ k ≤ D') (hD'hi : D' < (2 : ℝ) ^ (k + 1))
    (hsep : (65536 : ℝ) * min D D' ^ (7 / 4 : ℝ) - 40 * (D + D') ≤
      euclideanSetDistance C C')
    (hpos : euclideanSetDistance C C' ≤ |p - p'|) :
    (32768 : ℝ) * (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k ≤ |p - p'| := by
  have hmin : (2 : ℝ) ^ k ≤ min D D' := le_min hDlo hD'lo
  have hminpow : ((2 : ℝ) ^ k) ^ (7 / 4 : ℝ) ≤ min D D' ^ (7 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hmin (by norm_num)
  have hpowId : ((2 : ℝ) ^ k) ^ (7 / 4 : ℝ) =
      (2 : ℝ) ^ ((7 / 4 : ℝ) * k) := by
    calc
      ((2 : ℝ) ^ k) ^ (7 / 4 : ℝ) =
          ((2 : ℝ) ^ (k : ℝ)) ^ (7 / 4 : ℝ) := by rw [← Real.rpow_natCast]
      _ = (2 : ℝ) ^ ((k : ℝ) * (7 / 4 : ℝ)) :=
        (Real.rpow_mul (by norm_num) _ _).symm
      _ = (2 : ℝ) ^ ((7 / 4 : ℝ) * k) := by congr 1; ring
  have hscale : (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k ≤ min D D' ^ (7 / 4 : ℝ) := by
    calc
      (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k ≤
          (2 : ℝ) ^ ((7 / 4 : ℝ) * k) := profileA3_dyadic_power_lower k
      _ = ((2 : ℝ) ^ k) ^ (7 / 4 : ℝ) := hpowId.symm
      _ ≤ min D D' ^ (7 / 4 : ℝ) := hminpow
  have hDsum : 40 * (D + D') ≤ 160 * (2 : ℝ) ^ k := by
    have hpow : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by rw [pow_succ]; ring
    rw [hpow] at hDhi hD'hi
    nlinarith
  have hBleA : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k := by
    have hq : 1 ≤ ((4 : ℝ) / 3) ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have hmain : (65536 : ℝ) * ((2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k) -
      160 * (2 : ℝ) ^ k ≤ |p - p'| := by
    have h := hsep.trans hpos
    nlinarith [hscale, hDsum]
  have hconst : (32768 : ℝ) * (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k ≤
      (65536 : ℝ) * ((2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k) -
        160 * (2 : ℝ) ^ k := by
    nlinarith [hBleA]
  exact hconst.trans hmain

/-- A finite set of points in a path interval with mutual spacing at least `s` has at most
`1 + P/s` points. The proof injects the points into the unit intervals of their rescaled
coordinates. -/
theorem profileA3_linear_packing_count
    {ι : Type*} [DecidableEq ι] (F : Finset ι) (position : ι → ℝ)
    (s P : ℝ) (hs : 0 < s) (hP : 0 ≤ P)
    (hrange : ∀ i ∈ F, 0 ≤ position i ∧ position i ≤ P)
    (hsep : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → s ≤ |position i - position j|) :
    (F.card : ℝ) ≤ 1 + P / s := by
  classical
  let f : ι → ℕ := fun i => Nat.floor (position i / s)
  let T : Finset ℕ := Finset.range (Nat.floor (P / s) + 1)
  have hmaps : Set.MapsTo f (F : Set ι) (T : Set ℕ) := by
    intro i hi
    have hiF : i ∈ F := hi
    have hiRange := hrange i hiF
    have hdiv : position i / s ≤ P / s := div_le_div_of_nonneg_right hiRange.2 (le_of_lt hs)
    have hfloor : f i ≤ Nat.floor (P / s) := by
      exact Nat.floor_mono hdiv
    change f i ∈ Finset.range (Nat.floor (P / s) + 1)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hfloor)
  have hinj : Set.InjOn f (F : Set ι) := by
    intro i hi j hj hij
    by_contra hneq
    have hspacing := hsep i hi j hj hneq
    have hiRange := hrange i hi
    have hjRange := hrange j hj
    have hfi : (f i : ℝ) ≤ position i / s := Nat.floor_le (div_nonneg hiRange.1 (le_of_lt hs))
    have hfj : (f j : ℝ) ≤ position j / s := Nat.floor_le (div_nonneg hjRange.1 (le_of_lt hs))
    have hitop : position i / s < (f i : ℝ) + 1 := Nat.lt_floor_add_one _
    have hjtop : position j / s < (f j : ℝ) + 1 := Nat.lt_floor_add_one _
    have hupper : position i < s * ((f i : ℝ) + 1) := by
      simpa [mul_comm] using (div_lt_iff₀ hs).mp hitop
    have hlower : s * (f j : ℝ) ≤ position j := by
      simpa [mul_comm] using (le_div_iff₀ hs).mp hfj
    have hupper' : position j < s * ((f j : ℝ) + 1) := by
      simpa [mul_comm] using (div_lt_iff₀ hs).mp hjtop
    have hlower' : s * (f i : ℝ) ≤ position i := by
      simpa [mul_comm] using (le_div_iff₀ hs).mp hfi
    have hupperSame : position i < s * ((f j : ℝ) + 1) := by rw [← hij]; exact hupper
    have hupperSame' : position j < s * ((f i : ℝ) + 1) := by rw [hij]; exact hupper'
    have hgap1 : position i - position j < s := by nlinarith [hupperSame, hlower]
    have hgap2 : position j - position i < s := by nlinarith [hupperSame', hlower']
    have habs : |position i - position j| < s := by
      rw [abs_lt]
      constructor <;> linarith
    exact (not_le_of_gt habs) hspacing
  have hcard : F.card ≤ T.card := Finset.card_le_card_of_injOn f hmaps hinj
  have hfloor : (Nat.floor (P / s) : ℝ) ≤ P / s := Nat.floor_le (div_nonneg hP (le_of_lt hs))
  have hcard' : (F.card : ℝ) ≤ T.card := by exact_mod_cast hcard
  have hT : (T.card : ℝ) = Nat.floor (P / s) + 1 := by simp [T]
  rw [hT] at hcard'
  nlinarith

/-- The bin-count hypothesis generated by pairwise component separation along an ordered path.
Sizes in bin `k` are between `2^k` and `2^(k+1)`.  The denominator `2^k(4/3)^k` is a
conservative lower bound for the `2^(7k/4)` separation at Appendix-D exponent `7/4`. -/
structure ProfileA3DyadicPathPacking [DecidableEq ι] (C : Finset ι) (size : ι → ℝ)
    (bin : ι → ℕ) (N : ℕ) (P Dmax : ℝ) where
  budget_nonneg : 0 ≤ P
  max_lower : (2 : ℝ) ^ N ≤ Dmax
  max_upper : ∀ i ∈ C, size i ≤ Dmax
  bin_bound : ∀ i ∈ C, bin i ≤ N
  bin_lower : ∀ i ∈ C, (2 : ℝ) ^ bin i ≤ size i
  bin_upper : ∀ i ∈ C, size i < (2 : ℝ) ^ (bin i + 1)
  position : ι → ℝ
  position_bounds : ∀ i ∈ C, 0 ≤ position i ∧ position i ≤ P
  same_bin_separation : ∀ i ∈ C, ∀ j ∈ C, bin i = bin j → i ≠ j →
    (32768 : ℝ) * (2 : ℝ) ^ bin i * ((4 : ℝ) / 3) ^ bin i ≤
      |position i - position j|

/-- The position-spacing clause of a path certificate implies the required count in each dyadic
bin by the one-dimensional packing lemma. -/
theorem ProfileA3DyadicPathPacking.packing_count
    [DecidableEq ι] {C : Finset ι} {size : ι → ℝ} {bin : ι → ℕ} {N : ℕ} {P Dmax : ℝ}
    (hpack : ProfileA3DyadicPathPacking C size bin N P Dmax) (k : ℕ) (_hk : k ≤ N) :
    ((C.filter fun i => bin i = k).card : ℝ) ≤
      1 + (2 * P) / ((65536 : ℝ) * (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k) := by
  let B := C.filter fun i => bin i = k
  have hcount := profileA3_linear_packing_count B hpack.position
    ((32768 : ℝ) * (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k) P (by positivity)
    hpack.budget_nonneg
    (by
      intro i hi
      have hiC : i ∈ C := (Finset.mem_filter.mp hi).1
      exact hpack.position_bounds i hiC)
    (by
      intro i hi j hj hij
      have hiC : i ∈ C := (Finset.mem_filter.mp hi).1
      have hjC : j ∈ C := (Finset.mem_filter.mp hj).1
      have hbi : bin i = k := (Finset.mem_filter.mp hi).2
      have hbj : bin j = k := (Finset.mem_filter.mp hj).2
      have h := hpack.same_bin_separation i hiC j hjC (hbi.trans hbj.symm) hij
      simpa [hbi] using h)
  have hden : ((32768 : ℝ) * (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k) * 2 =
      (65536 : ℝ) * (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k := by ring
  have hratio : P / ((32768 : ℝ) * (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k) =
      (2 * P) / ((65536 : ℝ) * (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k) := by
    rw [show (65536 : ℝ) * (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k =
      2 * ((32768 : ℝ) * (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k) by ring]
    field_simp
  simpa [B, hratio] using hcount

/-- Dyadic bins give `Σ d_i ≤ 4 Dmax + 16 P / M`; the geometric sum is bounded by the
explicit ratio `3/4`. -/
theorem profileA3_dyadic_size_sum_bound
    [DecidableEq ι] (C : Finset ι) (size : ι → ℝ) (bin : ι → ℕ) (N : ℕ) (P Dmax : ℝ)
    (hpack : ProfileA3DyadicPathPacking C size bin N P Dmax) :
    (∑ i ∈ C, size i) ≤ 4 * Dmax + (16 / 65536 : ℝ) * P := by
  classical
  have hmaps : ∀ i ∈ C, bin i ∈ Finset.range (N + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hpack.bin_bound i hi))
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps size
  have hgroup (k : ℕ) :
      (∑ i ∈ C with bin i = k, size i) ≤
        ((C.filter fun i => bin i = k).card : ℝ) * (2 : ℝ) ^ (k + 1) := by
    calc
      (∑ i ∈ C with bin i = k, size i) ≤
          ∑ i ∈ C with bin i = k, (2 : ℝ) ^ (k + 1) := by
            apply Finset.sum_le_sum
            intro i hi
            have hiC : i ∈ C.filter (fun i => bin i = k) := by
              simpa [Finset.mem_filter] using hi
            have hiC' : i ∈ C := (Finset.mem_filter.mp hiC).1
            have hbin : bin i = k := (Finset.mem_filter.mp hiC).2
            simpa [hbin] using (le_of_lt (hpack.bin_upper i hiC'))
      _ = ((C.filter fun i => bin i = k).card : ℝ) * (2 : ℝ) ^ (k + 1) := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hsumGroup :
      (∑ k ∈ Finset.range (N + 1), ∑ i ∈ C with bin i = k, size i) ≤
        ∑ k ∈ Finset.range (N + 1),
          ((C.filter fun i => bin i = k).card : ℝ) * (2 : ℝ) ^ (k + 1) := by
    apply Finset.sum_le_sum
    intro k hk
    exact hgroup k
  have hcountSum :
      (∑ k ∈ Finset.range (N + 1),
          ((C.filter fun i => bin i = k).card : ℝ) * (2 : ℝ) ^ (k + 1)) ≤
        ∑ k ∈ Finset.range (N + 1),
          (1 + (2 * P) / ((65536 : ℝ) * (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k)) *
            (2 : ℝ) ^ (k + 1) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkN : k ≤ N := by simp only [Finset.mem_range] at hk; omega
    have hc := hpack.packing_count k hkN
    have hp : 0 ≤ (2 : ℝ) ^ (k + 1) := by positivity
    exact mul_le_mul_of_nonneg_right hc hp
  have hterm (k : ℕ) :
      (1 + (2 * P) / ((65536 : ℝ) * (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k)) *
          (2 : ℝ) ^ (k + 1) =
        (2 : ℝ) ^ (k + 1) + (4 / 65536 : ℝ) * P * ((3 : ℝ) / 4) ^ k := by
    have hpow : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
      rw [pow_succ]
      ring
    have hpos : 0 < (2 : ℝ) ^ k := by positivity
    have hq : 0 < ((4 : ℝ) / 3) ^ k := by positivity
    have hcancel :
        (2 * P / ((65536 : ℝ) * (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k)) *
          (2 * (2 : ℝ) ^ k) =
        (4 / 65536 : ℝ) * P * ((3 : ℝ) / 4) ^ k := by
      rw [div_eq_mul_inv]
      field_simp
      have hpowprod : ((4 : ℝ) / 3) ^ k * ((3 : ℝ) / 4) ^ k = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        2 ^ 2 * P = 4 * P := by norm_num
        _ = 4 * P * (((4 : ℝ) / 3) ^ k * ((3 : ℝ) / 4) ^ k) := by
          rw [hpowprod]
          ring
        _ = P * 4 * ((4 : ℝ) / 3) ^ k * ((3 : ℝ) / 4) ^ k := by ring
    calc
      (1 + (2 * P) / ((65536 : ℝ) * (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k)) *
          (2 : ℝ) ^ (k + 1) =
        (2 : ℝ) ^ (k + 1) +
          (2 * P / ((65536 : ℝ) * (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k)) *
            (2 : ℝ) ^ (k + 1) := by ring
      _ = (2 : ℝ) ^ (k + 1) + (4 / 65536 : ℝ) * P * ((3 : ℝ) / 4) ^ k := by
        rw [hpow]
        rw [hcancel]
  have htotal :
      ∑ k ∈ Finset.range (N + 1),
          (1 + (2 * P) / ((65536 : ℝ) * (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k)) *
            (2 : ℝ) ^ (k + 1) =
        (∑ k ∈ Finset.range (N + 1), (2 : ℝ) ^ (k + 1)) +
          (4 / 65536 : ℝ) * P *
            (∑ k ∈ Finset.range (N + 1), ((3 : ℝ) / 4) ^ k) := by
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  calc
    (∑ i ∈ C, size i) = ∑ k ∈ Finset.range (N + 1),
        ∑ i ∈ C with bin i = k, size i := hfiber.symm
    _ ≤ ∑ k ∈ Finset.range (N + 1),
        ((C.filter fun i => bin i = k).card : ℝ) * (2 : ℝ) ^ (k + 1) := hsumGroup
    _ ≤ ∑ k ∈ Finset.range (N + 1),
        (1 + (2 * P) / ((65536 : ℝ) * (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k)) *
          (2 : ℝ) ^ (k + 1) := hcountSum
    _ = (∑ k ∈ Finset.range (N + 1), (2 : ℝ) ^ (k + 1)) +
        (4 / 65536 : ℝ) * P *
          (∑ k ∈ Finset.range (N + 1), ((3 : ℝ) / 4) ^ k) := htotal
    _ ≤ 4 * Dmax + (16 / 65536 : ℝ) * P := by
      rw [sum_two_pow_succ]
      have hgeo := sum_three_fourth_pow_le_four (N + 1)
      have hmax := hpack.max_lower
      have hP := hpack.budget_nonneg
      have hbase : (2 : ℝ) ^ (N + 2) - 2 ≤ 4 * Dmax := by
        have hpow : (2 : ℝ) ^ (N + 2) = 4 * (2 : ℝ) ^ N := by
          rw [pow_add]
          norm_num
          ring
        rw [hpow]
        nlinarith
      have hcor : (4 / 65536 : ℝ) * P *
          (∑ k ∈ Finset.range (N + 1), ((3 : ℝ) / 4) ^ k) ≤
          (16 / 65536 : ℝ) * P := by
        have hmul := mul_le_mul_of_nonneg_left hgeo
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 65536) hP)
        nlinarith
      exact add_le_add hbase hcor

/-- The component diameters on a path cost at most `1/80` of the total physical budget, once
the parent estimate and dyadic packing count are available. -/
theorem profileA3_path_component_cost_small
    [DecidableEq ι] (C : Finset ι) (size diameter : ι → ℝ) (bin : ι → ℕ) (N : ℕ)
    (P Dmax : ℝ)
    (hpack : ProfileA3DyadicPathPacking C size bin N P Dmax)
    (hdiam : ∀ i ∈ C, diameter i ≤ 40 * size i)
    (hparent : (65536 - 40 : ℝ) * Dmax ≤ P) :
    (∑ i ∈ C, diameter i) ≤ (1 / 80 : ℝ) * P := by
  have hsize := profileA3_dyadic_size_sum_bound C size bin N P Dmax hpack
  have hsum : (∑ i ∈ C, diameter i) ≤ 40 * ∑ i ∈ C, size i := by
    calc
      (∑ i ∈ C, diameter i) ≤ ∑ i ∈ C, 40 * size i :=
        Finset.sum_le_sum fun i hi => hdiam i hi
      _ = 40 * ∑ i ∈ C, size i := by rw [Finset.mul_sum]
  have hDmax_nonneg : 0 ≤ Dmax := by
    exact (show 0 ≤ (2 : ℝ) ^ N by positivity).trans hpack.max_lower
  have hparent' : Dmax ≤ P / (65536 - 40 : ℝ) := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 65536 - 40)]
    nlinarith
  have hcoeff : (160 / (65536 - 40 : ℝ) + 640 / 65536 : ℝ) < 1 / 80 := by
    norm_num
  have hP : 0 ≤ P := hpack.budget_nonneg
  calc
    (∑ i ∈ C, diameter i) ≤ 40 * ∑ i ∈ C, size i := hsum
    _ ≤ 40 * (4 * Dmax + (16 / 65536 : ℝ) * P) := by nlinarith
    _ ≤ (160 / (65536 - 40 : ℝ) + 640 / 65536 : ℝ) * P := by
      have := mul_le_mul_of_nonneg_left hparent' (by norm_num : (0 : ℝ) ≤ 160)
      nlinarith
    _ ≤ (1 / 80 : ℝ) * P := by
      exact mul_le_mul_of_nonneg_right hcoeff.le hP

/-- Absorbing the component diameters into the path budget gives the final `9/8` allowance. -/
theorem profileA3_path_budget_le_nine_eighths
    (m P S : ℝ) (hm : 0 ≤ m) (hP : P = m + S)
    (hS : S ≤ (1 / 80 : ℝ) * P) : P ≤ (9 / 8 : ℝ) * m := by
  rw [hP] at hS ⊢
  nlinarith

/- The explicit pointwise form is the adapter used after the quotient-path construction supplies
its finite component list and bin-count certificate. -/
theorem profileA3_collapsed_support_point_of_dyadic_path
    [DecidableEq ι] {L : ℕ} (K : Finset (Site L)) (d : Site L → ℝ) (x : Site L)
    (C : Finset ι) (size diameter : ι → ℝ) (bin : ι → ℕ) (N : ℕ)
    (P Dmax : ℝ)
    (hpack : ProfileA3DyadicPathPacking C size bin N P Dmax)
    (hdiam : ∀ i ∈ C, diameter i ≤ 40 * size i)
    (hparent : (65536 - 40 : ℝ) * Dmax ≤ P)
    (hbudget : P = d x + ∑ i ∈ C, diameter i)
    (hend : euclideanSetDistance K {x} ≤ P)
    (hm : 0 ≤ d x) :
    euclideanSetDistance K {x} ≤ (9 / 8 : ℝ) * d x := by
  have hcost := profileA3_path_component_cost_small C size diameter bin N P Dmax
    hpack hdiam hparent
  have hP := profileA3_path_budget_le_nine_eighths (d x) P
    (∑ i ∈ C, diameter i) hm hbudget hcost
  exact hend.trans hP

/-- Data left by a shortest quotient path after listing its visited zero-cost components. The
position-spacing clause in `packing` is obtained from component separation, and the parent fields
record the first-component separation from the selected cluster. -/
structure ProfileA3PathWitness {L : ℕ} (K : Finset (Site L))
    (d : Site L → ℝ) (x : Site L) where
  Index : Type
  indexDecidableEq : DecidableEq Index
  components : Finset Index
  size : Index → ℝ
  diameter : Index → ℝ
  bin : Index → ℕ
  maxBin : ℕ
  budget : ℝ
  maxSize : ℝ
  parentSize : ℝ
  parentDistance : ℝ
  collapsed_nonneg : 0 ≤ d x
  packing : @ProfileA3DyadicPathPacking Index indexDecidableEq
    components size bin maxBin budget maxSize
  max_size_lower : (2 : ℝ) ^ maxBin ≤ maxSize
  component_diameter : ∀ i ∈ components, diameter i ≤ 40 * size i
  parent_scale_order : maxSize ≤ parentSize
  parent_component_separation :
    (65536 : ℝ) * min parentSize maxSize ^ (7 / 4 : ℝ) - 40 * maxSize ≤ parentDistance
  parent_path_length : parentDistance ≤ budget
  budget_eq : budget = d x + ∑ i ∈ components, diameter i
  endpoint_bound : euclideanSetDistance K {x} ≤ budget

/-- A quotient-path witness for every point proves the exact support-control predicate consumed by
the terminal ramp. -/
theorem profileA3CollapsedSupportControl_of_path_witness
    {L : ℕ} (j : ℕ) (K : Finset (Site L)) (d : Site L → ℝ)
    (hpath : ∀ x, Nonempty (ProfileA3PathWitness K d x)) :
    ProfileA3CollapsedSupportControl j K d := by
  intro x _hx
  obtain ⟨W⟩ := hpath x
  have hmax : 1 ≤ W.maxSize := by
    calc
      1 ≤ (2 : ℝ) ^ W.maxBin := one_le_pow₀ (by norm_num)
      _ ≤ W.maxSize := W.max_size_lower
  have hparent := profileA3_parent_budget_from_separation W.maxSize W.parentSize
    W.parentDistance W.budget hmax W.parent_scale_order
    W.parent_component_separation W.parent_path_length
  exact @profileA3_collapsed_support_point_of_dyadic_path W.Index W.indexDecidableEq
    L K d x W.components W.size
    W.diameter W.bin W.maxBin W.budget W.maxSize W.packing W.component_diameter
    hparent W.budget_eq W.endpoint_bound W.collapsed_nonneg

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
