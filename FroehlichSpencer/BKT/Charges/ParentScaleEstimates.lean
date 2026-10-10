/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.SeparatedPatch
public import FroehlichSpencer.BKT.Charges.SquareDiameterBounds

/-! # Numerical scale bounds for

These estimates isolate the numerical comparison in the parent selector from
the graph metric diameter bound for dyadic squares. -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- With `M=2^16` and `α=7/4`, the scale-`k` separation threshold is larger
than `32·2^k`, the upper diameter scale for any of the first four ancestors. -/
theorem squareSeparationThreshold_gt_32_side (k : PositiveSquareScale) :
    (32 : ℝ) * (squareSide k.val : ℝ) < squareSeparationThreshold k := by
  have hexponent : ((k.val + 1 : ℕ) : ℝ) ≤
      chargeCoverExponent * (k.val + 1 : ℕ) := by
    rw [show chargeCoverExponent = (7 / 4 : ℝ) by norm_num [chargeCoverExponent]]
    have hnonneg : 0 ≤ ((k.val + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hpow : (2 : ℝ) ^ ((k.val + 1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (chargeCoverExponent * (k.val + 1 : ℕ)) := by
    exact Real.rpow_le_rpow_of_exponent_le
      (x := (2 : ℝ)) (by norm_num) hexponent
  have hpowSide : (2 : ℝ) * (squareSide k.val : ℝ) ≤
      (2 : ℝ) ^ (chargeCoverExponent * (k.val + 1 : ℕ)) := by
    have hbase : (2 : ℝ) ^ (k.val : ℝ) = (squareSide k.val : ℝ) := by
      rw [Real.rpow_natCast]
      simp [squareSide]
    have hcast : ((k.val + 1 : ℕ) : ℝ) = (k.val : ℝ) + 1 := by norm_cast
    calc
      (2 : ℝ) * (squareSide k.val : ℝ) =
          (2 : ℝ) ^ (k.val : ℝ) * 2 := by rw [hbase]; ring
      _ = (2 : ℝ) ^ ((k.val + 1 : ℕ) : ℝ) := by
        rw [hcast, Real.rpow_add_one (by norm_num) (k.val : ℝ)]
      _ ≤ (2 : ℝ) ^ (chargeCoverExponent * (k.val + 1 : ℕ)) := hpow
  have hpositive : 0 < (squareSide k.val : ℝ) := by
    simp [squareSide]
  change (32 : ℝ) * (squareSide k.val : ℝ) <
    (2 * (chargeCoverScale : ℝ)) *
      (2 : ℝ) ^ (chargeCoverExponent * (k.val + 1 : ℕ))
  have hscale : (2 : ℝ) * (chargeCoverScale : ℝ) = 2 ^ 17 := by
    norm_num [chargeCoverScale]
  rw [hscale]
  have hcoeff : (32 : ℝ) < 2 ^ 17 * 2 := by norm_num
  calc
    32 * (squareSide k.val : ℝ) <
        (2 ^ 17 * 2) * (squareSide k.val : ℝ) := by
          exact mul_lt_mul_of_pos_right hcoeff hpositive
    _ = 2 ^ 17 * ((2 : ℝ) * (squareSide k.val : ℝ)) := by ring
    _ ≤ 2 ^ 17 * (2 : ℝ) ^ (chargeCoverExponent * (k.val + 1 : ℕ)) :=
      mul_le_mul_of_nonneg_left hpowSide (by positivity)

/-- For every `j≤4`, the numerical scale bound used in  is strict. -/
theorem squareSeparationThreshold_gt_ancestorDiameterScale
    (k : PositiveSquareScale) (j : ParentOffset) :
    (2 * (squareSide (ancestorScale k j) : ℝ)) < squareSeparationThreshold k := by
  have hside : squareSide (ancestorScale k j) ≤ 16 * squareSide k.val := by
    change 2 ^ (k.val + j.val) ≤ 16 * 2 ^ k.val
    rw [Nat.pow_add]
    have hj : 2 ^ j.val ≤ 2 ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have hj' : 2 ^ j.val ≤ 16 := by simpa using hj
    calc
      2 ^ k.val * 2 ^ j.val = 2 ^ j.val * 2 ^ k.val := Nat.mul_comm _ _
      _ ≤ 16 * 2 ^ k.val := Nat.mul_le_mul_right _ hj'
  have hscale := squareSeparationThreshold_gt_32_side k
  have hstrict : 2 * (squareSide (ancestorScale k j) : ℝ) ≤
      32 * (squareSide k.val : ℝ) := by
    have hsideR : (squareSide (ancestorScale k j) : ℝ) ≤
        16 * (squareSide k.val : ℝ) := by exact_mod_cast hside
    calc
      2 * (squareSide (ancestorScale k j) : ℝ) ≤
          2 * (16 * (squareSide k.val : ℝ)) :=
        mul_le_mul_of_nonneg_left hsideR (by norm_num)
      _ = 32 * (squareSide k.val : ℝ) := by ring
  exact lt_of_le_of_lt hstrict hscale

/-- Every allowed square at an ancestor scale has diameter below the source
separation threshold. The square may already have overflowed to the whole
domain. -/
theorem ancestorScaleSquare_diameter_lt_threshold
    (boundary : SquareBoundary) (L : ℕ) (hL : 1 < L)
    (k : PositiveSquareScale) (j : ParentOffset)
    (s : Finset (Fin L × Fin L))
    (hs : s ∈ kpSquares boundary L (ancestorScale k j)) :
    (squareDiameter boundary L s : ℝ) < squareSeparationThreshold k := by
  have hdiam : squareDiameter boundary L s ≤
      2 * (squareSide (ancestorScale k j) - 1) := by
    cases boundary with
    | free => exact free_squareDiameter_le_all L (ancestorScale k j) s hs
    | periodic => exact periodic_squareDiameter_le L (ancestorScale k j) hL s hs
  have hdiamR : (squareDiameter boundary L s : ℝ) ≤
      (2 * (squareSide (ancestorScale k j) - 1) : ℕ) := by
    exact_mod_cast hdiam
  have hsideNat : 2 * (squareSide (ancestorScale k j) - 1) ≤
      2 * squareSide (ancestorScale k j) := by omega
  have hsideR : (2 * (squareSide (ancestorScale k j) - 1) : ℕ) ≤
      2 * (squareSide (ancestorScale k j) : ℝ) := by
    calc
      ((2 * (squareSide (ancestorScale k j) - 1) : ℕ) : ℝ) ≤
          ((2 * squareSide (ancestorScale k j) : ℕ) : ℝ) :=
        Nat.cast_le.mpr hsideNat
      _ = 2 * (squareSide (ancestorScale k j) : ℝ) := by norm_num
  exact (le_trans hdiamR hsideR).trans_lt
    (squareSeparationThreshold_gt_ancestorDiameterScale k j)

/-- A square at a no-larger scale is small relative to the separation
threshold of any positive comparison scale. -/
theorem square_diameter_lt_threshold_of_scale_le
    (boundary : SquareBoundary) (L : ℕ) (hL : 1 < L)
    (k q : PositiveSquareScale) (hqk : q.val ≤ k.val)
    (s : Finset (Fin L × Fin L))
    (hs : s ∈ kpSquares boundary L q.val) :
    (squareDiameter boundary L s : ℝ) < squareSeparationThreshold k := by
  have hdiam : squareDiameter boundary L s ≤ 2 * (squareSide q.val - 1) := by
    cases boundary with
    | free => exact free_squareDiameter_le_all L q.val s hs
    | periodic => exact periodic_squareDiameter_le L q.val hL s hs
  have hdiamR : (squareDiameter boundary L s : ℝ) ≤
      (2 * (squareSide q.val - 1) : ℕ) := by exact_mod_cast hdiam
  have hqside : squareSide q.val ≤ squareSide k.val := by
    exact Nat.pow_le_pow_right (by omega) hqk
  have hstrict : (2 * (squareSide q.val : ℝ)) <
      (32 : ℝ) * (squareSide k.val : ℝ) := by
    have hqposNat : 0 < squareSide q.val := Nat.pow_pos (by decide)
    have hqpos : 0 < (squareSide q.val : ℝ) := by exact_mod_cast hqposNat
    have hqkR : (squareSide q.val : ℝ) ≤ (squareSide k.val : ℝ) := by exact_mod_cast hqside
    nlinarith
  have hdiamSide : (2 * (squareSide q.val - 1) : ℕ) ≤
      2 * (squareSide q.val : ℝ) := by
    have hNat : 2 * (squareSide q.val - 1) ≤ 2 * squareSide q.val := by omega
    calc
      ((2 * (squareSide q.val - 1) : ℕ) : ℝ) ≤
          ((2 * squareSide q.val : ℕ) : ℝ) := Nat.cast_le.mpr hNat
      _ = 2 * (squareSide q.val : ℝ) := by norm_num
  exact (le_trans hdiamR hdiamSide).trans_lt
    (lt_trans hstrict (squareSeparationThreshold_gt_32_side k))

/-- A square no more than three scales above `k` still has diameter below
the scale-`k` separation threshold. -/
theorem square_diameter_lt_threshold_of_gap_le_three
    (boundary : SquareBoundary) (L : ℕ) (hL : 1 < L)
    (k q : PositiveSquareScale) (hqk : q.val - k.val ≤ 3)
    (s : Finset (Fin L × Fin L))
    (hs : s ∈ kpSquares boundary L q.val) :
    (squareDiameter boundary L s : ℝ) < squareSeparationThreshold k := by
  have hdiam : squareDiameter boundary L s ≤ 2 * (squareSide q.val - 1) := by
    cases boundary with
    | free => exact free_squareDiameter_le_all L q.val s hs
    | periodic => exact periodic_squareDiameter_le L q.val hL s hs
  have hdiamR : (squareDiameter boundary L s : ℝ) ≤
      (2 * (squareSide q.val - 1) : ℕ) := by exact_mod_cast hdiam
  have hqside : squareSide q.val ≤ 8 * squareSide k.val := by
    change 2 ^ q.val ≤ 8 * 2 ^ k.val
    by_cases hqk' : q.val ≤ k.val
    · have hp := Nat.pow_le_pow_right (by omega : 0 < 2) hqk'
      omega
    · have hdiff : q.val = k.val + (q.val - k.val) := by omega
      rw [hdiff, Nat.pow_add]
      have hexp : 2 ^ (q.val - k.val) ≤ 2 ^ 3 :=
        Nat.pow_le_pow_right (by omega) hqk
      have hexp' : 2 ^ (q.val - k.val) ≤ 8 := by simpa using hexp
      calc
        2 ^ k.val * 2 ^ (q.val - k.val) =
            2 ^ (q.val - k.val) * 2 ^ k.val := Nat.mul_comm _ _
        _ ≤ 8 * 2 ^ k.val := Nat.mul_le_mul_right _ hexp'
  have hstrict : (2 * (squareSide q.val : ℝ)) <
      (32 : ℝ) * (squareSide k.val : ℝ) := by
    have hqposNat : 0 < squareSide q.val := Nat.pow_pos (by decide)
    have hqpos : 0 < (squareSide q.val : ℝ) := by exact_mod_cast hqposNat
    have hqkR : (squareSide q.val : ℝ) ≤ 8 * (squareSide k.val : ℝ) := by
      exact_mod_cast hqside
    nlinarith
  have hdiamSide : (2 * (squareSide q.val - 1) : ℕ) ≤
      2 * (squareSide q.val : ℝ) := by
    have hNat : 2 * (squareSide q.val - 1) ≤ 2 * squareSide q.val := by omega
    calc
      ((2 * (squareSide q.val - 1) : ℕ) : ℝ) ≤
          ((2 * squareSide q.val : ℕ) : ℝ) := Nat.cast_le.mpr hNat
      _ = 2 * (squareSide q.val : ℝ) := by norm_num
  exact (le_trans hdiamR hdiamSide).trans_lt
    (lt_trans hstrict (squareSeparationThreshold_gt_32_side k))

end FroehlichSpencer.BKT

end
