/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Numerical contour-series estimate for the clock Peierls argument

The finite partial sums of the contour union bound are uniformly small.  For a contour of size
`k + 1`, at most `2 * (k + 5)` path positions can support an active contour.  The resulting
size-counted sum is bounded by a geometric series with ratio `2 * q`.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Clock.Peierls

open Finset

/-- The minimum contour size forced by the explicit frame detour at path position `j`. -/
def clockPeierlsMinContourSize (R M j : ℕ) : ℕ :=
  max 1 (min j (min (R - j) M) - 3)

/-- For a contour of size `k + 1`, only positions within `k + 4` of an endpoint can be active. -/
theorem clockPeierlsActivePositions_card_le (R M k : ℕ) (hM : R ≤ M) :
    ((Icc 1 R).filter fun j => clockPeierlsMinContourSize R M j ≤ k + 1).card ≤
      2 * (k + 5) := by
  classical
  let active := (Icc 1 R).filter fun j => clockPeierlsMinContourSize R M j ≤ k + 1
  let left := Icc 1 (k + 4)
  let right := Icc (R - (k + 4)) R
  have hsubset : active ⊆ left ∪ right := by
    intro j hj
    change j ∈ (Icc 1 R).filter
      (fun j => clockPeierlsMinContourSize R M j ≤ k + 1) at hj
    rcases mem_filter.mp hj with ⟨hjmem, hjk⟩
    have hjbounds : 1 ≤ j ∧ j ≤ R := by simpa only [mem_Icc] using hjmem
    rcases hjbounds with ⟨hj₁, hjR⟩
    have hrem : R - j ≤ M := (Nat.sub_le R j).trans hM
    change max 1 (min j (min (R - j) M) - 3) ≤ k + 1 at hjk
    rw [Nat.min_eq_left hrem] at hjk
    have hdiff : min j (R - j) - 3 ≤ k + 1 := (max_le_iff.mp hjk).2
    have hnear : min j (R - j) ≤ k + 4 := by omega
    rcases min_le_iff.mp hnear with hjLeft | hjRight
    · exact mem_union_left _ (mem_Icc.mpr ⟨hj₁, hjLeft⟩)
    · exact mem_union_right _ (mem_Icc.mpr ⟨by omega, hjR⟩)
  have hleft : left.card ≤ k + 4 := by
    simp [left]
  have hright : right.card ≤ k + 5 := by
    simp [right]
    omega
  calc
    active.card ≤ (left ∪ right).card := card_le_card hsubset
    _ ≤ left.card + right.card := card_union_le _ _
    _ ≤ (k + 4) + (k + 5) := Nat.add_le_add hleft hright
    _ ≤ 2 * (k + 5) := by omega

private theorem nat_add_five_le_six_mul_two_pow (k : ℕ) : k + 5 ≤ 6 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hp : 1 ≤ (2 : ℕ) ^ k := Nat.one_le_pow k 2 (by norm_num)
      calc
        k + 1 + 5 ≤ 6 * 2 ^ k + 1 := by omega
        _ ≤ 12 * 2 ^ k := by omega
        _ = 6 * 2 ^ (k + 1) := by rw [pow_succ]; ring

/--
Uniform bound for all finite partial sums of the contour-size union bound.  The inner index `k`
is shifted by one so `k + 1` is the contour size and `range K` sums sizes `1` through `K`.

The condition `clockPeierlsMinContourSize R M j ≤ k + 1` records that an active contour at path
position `j` must be at least the indicated detour size.  In particular, every finite partial
sum of the corresponding infinite contour series is at most `1 / 4`.
-/
theorem clockPeierlsContourSeries_partial_le_quarter (R M K : ℕ) (hM : R ≤ M) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 100) :
    (∑ j ∈ Icc 1 R, ∑ k ∈ range K,
      if clockPeierlsMinContourSize R M j ≤ k + 1 then q ^ (k + 1) else 0) ≤ 1 / 4 := by
  classical
  have hratio : 2 * q < 1 := by nlinarith
  have hgeom : Summable fun k : ℕ => (2 * q) ^ k :=
    summable_geometric_of_lt_one (by positivity) hratio
  have hgeom_le : (∑ k ∈ range K, (2 * q) ^ k) ≤ (1 - 2 * q)⁻¹ := by
    calc
      (∑ k ∈ range K, (2 * q) ^ k) ≤ ∑' k : ℕ, (2 * q) ^ k :=
        hgeom.sum_le_tsum (range K) (fun _ _ => by positivity)
      _ = (1 - 2 * q)⁻¹ := tsum_geometric_of_lt_one (by positivity) hratio
  have hden : 0 < 1 - 2 * q := by linarith
  have hinv : (1 - 2 * q)⁻¹ ≤ 2 := by
    have hdiv : 1 / (1 - 2 * q) ≤ 2 := by
      apply (div_le_iff₀ hden).2
      nlinarith
    simpa only [one_div] using hdiv
  have hqfinal : 24 * q ≤ 1 / 4 := by nlinarith
  rw [Finset.sum_comm]
  calc
    (∑ k ∈ range K, ∑ j ∈ Icc 1 R,
      if clockPeierlsMinContourSize R M j ≤ k + 1 then q ^ (k + 1) else 0)
        ≤ ∑ k ∈ range K, 12 * q * (2 * q) ^ k := by
          apply sum_le_sum
          intro k hk
          have hcard := clockPeierlsActivePositions_card_le R M k hM
          have hsum :
              (∑ j ∈ Icc 1 R,
                if clockPeierlsMinContourSize R M j ≤ k + 1 then q ^ (k + 1) else 0) =
                ((Icc 1 R).filter
                  fun j => clockPeierlsMinContourSize R M j ≤ k + 1).card * q ^ (k + 1) := by
            rw [Finset.sum_ite]
            simp
          rw [hsum]
          have hcardReal :
              (((Icc 1 R).filter
                fun j => clockPeierlsMinContourSize R M j ≤ k + 1).card : ℝ) ≤
                (2 : ℝ) * ((k : ℝ) + 5) := by
            calc
              _ ≤ ((2 * (k + 5) : ℕ) : ℝ) := by exact_mod_cast hcard
              _ = (2 : ℝ) * ((k : ℝ) + 5) := by push_cast; ring
          have hcoeffNat : 2 * (k + 5) ≤ 12 * 2 ^ k := by
            calc
              2 * (k + 5) ≤ 2 * (6 * 2 ^ k) := Nat.mul_le_mul_left 2
                (nat_add_five_le_six_mul_two_pow k)
              _ = 12 * 2 ^ k := by ring
          have hcoeff : (2 * (k + 5) : ℝ) ≤ 12 * (2 : ℝ) ^ k := by
            exact_mod_cast hcoeffNat
          calc
            (((Icc 1 R).filter
              fun j => clockPeierlsMinContourSize R M j ≤ k + 1).card : ℝ) * q ^ (k + 1)
                ≤ (2 * (k + 5) : ℝ) * q ^ (k + 1) :=
                  mul_le_mul_of_nonneg_right hcardReal (pow_nonneg hq0 _)
            _ ≤ (12 * (2 : ℝ) ^ k) * q ^ (k + 1) :=
                  mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hq0 _)
            _ = 12 * q * (2 * q) ^ k := by
                  rw [pow_succ]
                  calc
                    12 * (2 : ℝ) ^ k * (q ^ k * q) =
                        12 * q * ((2 : ℝ) ^ k * q ^ k) := by ring
                    _ = 12 * q * (2 * q) ^ k := by rw [← mul_pow]
    _ = 12 * q * ∑ k ∈ range K, (2 * q) ^ k := by rw [mul_sum]
    _ ≤ 12 * q * (1 - 2 * q)⁻¹ :=
      mul_le_mul_of_nonneg_left hgeom_le (by positivity)
    _ ≤ 24 * q := by
      calc
        12 * q * (1 - 2 * q)⁻¹ ≤ (12 * q) * 2 :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = 24 * q := by ring
    _ ≤ 1 / 4 := hqfinal

end FroehlichSpencer.BKT.Clock.Peierls
