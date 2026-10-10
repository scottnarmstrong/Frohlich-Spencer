/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.RecurrenceArithmetic
public import FroehlichSpencer.BKT.Charges.Covers

/-! # A scale map for the pinned boundary recurrence

The shifted KP recurrence map supplies the lower scale needed by the pinned
matching groups. The shift is chosen so its affine upper bound leaves room for
the isolation-inflated radius.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT

/-- Shift the standard `4/7` floor map to absorb the larger pinned isolation
radius. -/
def boundaryEntropyGamma (k : ℕ) : ℕ :=
  (recurrenceGamma ((k : ℤ) + 8) - 8).toNat

/-- The shifted lower scale is nonnegative and leaves a four-unit dyadic gap. -/
theorem boundaryEntropyGamma_spec (k : ℕ) (hk : 29 ≤ k) :
    ((boundaryEntropyGamma k : ℕ) : ℝ) =
        (recurrenceGamma ((k : ℤ) + 8) : ℝ) - 8 ∧
      boundaryEntropyGamma k + 4 ≤ k := by
  have hkR : (29 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hbounds := recurrenceGamma_bounds ((k : ℤ) + 8)
  have hγlo : 8 ≤ (recurrenceGamma ((k : ℤ) + 8) : ℝ) := by
    have hlow : (4 / 7 : ℝ) * ((k : ℝ) + 8) - 83 / 7 - 1 ≤
        (recurrenceGamma ((k : ℤ) + 8) : ℝ) := by
      simpa using hbounds.1
    norm_num at hlow ⊢
    nlinarith only [hlow, hkR]
  have hγloInt : 8 ≤ recurrenceGamma ((k : ℤ) + 8) := by exact_mod_cast hγlo
  have hcast :
      ((Int.toNat (recurrenceGamma ((k : ℤ) + 8) - 8) : ℕ) : ℤ) =
        recurrenceGamma ((k : ℤ) + 8) - 8 :=
    Int.toNat_of_nonneg (by omega)
  have hγhi : (recurrenceGamma ((k : ℤ) + 8) : ℝ) ≤
      (4 / 7 : ℝ) * ((k : ℝ) + 8) - 83 / 7 := by
    simpa using hbounds.2
  have hshiftHi : (recurrenceGamma ((k : ℤ) + 8) : ℝ) - 8 ≤
      (4 / 7 : ℝ) * (k : ℝ) - 107 / 7 := by
    nlinarith only [hγhi]
  have hgapR : (recurrenceGamma ((k : ℤ) + 8) : ℝ) - 8 + 4 ≤ (k : ℝ) := by
    nlinarith only [hshiftHi, hkR]
  constructor
  · exact_mod_cast hcast
  · change Int.toNat (recurrenceGamma ((k : ℤ) + 8) - 8) + 4 ≤ k
    have hgapR' :
        ((Int.toNat (recurrenceGamma ((k : ℤ) + 8) - 8) + 4 : ℕ) : ℝ) ≤
          (k : ℝ) := by
      rw [Nat.cast_add]
      have hcastR :
          (Int.toNat (recurrenceGamma ((k : ℤ) + 8) - 8) : ℝ) =
            (recurrenceGamma ((k : ℤ) + 8) : ℝ) - 8 := by exact_mod_cast hcast
      rw [hcastR]
      exact hgapR
    exact_mod_cast hgapR'

private theorem boundaryEntropy_factor_rpow_le :
    (4 + Real.sqrt 2 : ℝ) ^ (7 / 4 : ℝ) ≤ (2 : ℝ) ^ (21 / 4 : ℝ) := by
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hbase : 4 + Real.sqrt 2 ≤ 6 := by linarith
  calc
    (4 + Real.sqrt 2 : ℝ) ^ (7 / 4 : ℝ) ≤
        (6 : ℝ) ^ (7 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hbase (by norm_num)
    _ ≤ (8 : ℝ) ^ (7 / 4 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    _ = (2 : ℝ) ^ (21 / 4 : ℝ) := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num,
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      norm_num

private theorem boundaryEntropy_dyadic_rpow (j : ℕ) :
    ((2 : ℝ) ^ j) ^ (7 / 4 : ℝ) = (2 : ℝ) ^ ((7 / 4 : ℝ) * j) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

/-- The fixed numerical scale inequality for the matching-group cover bound:
`6·2^j + 3R_j < 2^k`, where `R_j` is the Appendix-D isolation radius. -/
theorem boundaryEntropyGamma_matchingScale (k : ℕ) (hk : 29 ≤ k) :
    6 * (2 : ℝ) ^ boundaryEntropyGamma k +
      3 * (2 * (chargeCoverScale : ℝ) *
        ((4 + Real.sqrt 2) * (2 : ℝ) ^ boundaryEntropyGamma k) ^
          chargeCoverExponent) < (2 : ℝ) ^ k := by
  obtain ⟨hγcast, hgap⟩ := boundaryEntropyGamma_spec k hk
  have hkR : (29 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hjBound : (boundaryEntropyGamma k : ℝ) ≤
      (4 / 7 : ℝ) * (k : ℝ) - 107 / 7 := by
    rw [hγcast]
    have hγhi := (recurrenceGamma_bounds ((k : ℤ) + 8)).2
    have hγhiR : (recurrenceGamma ((k : ℤ) + 8) : ℝ) ≤
        (4 / 7 : ℝ) * ((k : ℝ) + 8) - 83 / 7 := by simpa using hγhi
    nlinarith only [hγhiR]
  have hside : (2 : ℝ) ^ (boundaryEntropyGamma k : ℕ) * 16 ≤ (2 : ℝ) ^ k := by
    have hpow :
        2 ^ (boundaryEntropyGamma k + 4) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by omega) hgap
    have hcast :
        ((2 ^ (boundaryEntropyGamma k + 4) : ℕ) : ℝ) ≤
          ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast hpow
    rw [Nat.pow_add] at hcast
    norm_num at hcast ⊢
    nlinarith only [hcast]
  have hfirst : 6 * (2 : ℝ) ^ boundaryEntropyGamma k ≤
      (3 / 8 : ℝ) * (2 : ℝ) ^ k := by
    have hp : 0 ≤ (2 : ℝ) ^ boundaryEntropyGamma k := by positivity
    nlinarith only [hside, hp]
  have hfactor := boundaryEntropy_factor_rpow_le
  have hradpow := boundaryEntropy_dyadic_rpow (boundaryEntropyGamma k)
  have hexp : (19 : ℝ) + 21 / 4 +
      (7 / 4 : ℝ) * (boundaryEntropyGamma k : ℝ) ≤ (k : ℝ) - 2 := by
    nlinarith only [hjBound]
  have hcoeff : 6 * (chargeCoverScale : ℝ) ≤ (2 : ℝ) ^ (19 : ℝ) := by
    norm_num [chargeCoverScale]
  have hfactorMul :
      6 * (chargeCoverScale : ℝ) *
          (4 + Real.sqrt 2) ^ (7 / 4 : ℝ) ≤
        (2 : ℝ) ^ (19 : ℝ) * (2 : ℝ) ^ (21 / 4 : ℝ) :=
    mul_le_mul hcoeff hfactor (by positivity) (by positivity)
  have hconst :
      (2 : ℝ) ^ (19 : ℝ) * (2 : ℝ) ^ (21 / 4 : ℝ) =
        (2 : ℝ) ^ ((19 : ℝ) + 21 / 4 : ℝ) := by
    rw [← Real.rpow_add (by norm_num)]
  have hrad :
      3 * (2 * (chargeCoverScale : ℝ) *
          ((4 + Real.sqrt 2) * (2 : ℝ) ^ boundaryEntropyGamma k) ^
            chargeCoverExponent) ≤ (2 : ℝ) ^ ((k : ℝ) - 2) := by
    have htotal :
        6 * (chargeCoverScale : ℝ) *
          ((4 + Real.sqrt 2) ^ (7 / 4 : ℝ) *
            (2 : ℝ) ^ ((7 / 4 : ℝ) * boundaryEntropyGamma k)) ≤
          (2 : ℝ) ^ ((19 : ℝ) + 21 / 4) *
            (2 : ℝ) ^ ((7 / 4 : ℝ) * boundaryEntropyGamma k) := by
      have hcoeff' : 6 * (chargeCoverScale : ℝ) *
          (4 + Real.sqrt 2) ^ (7 / 4 : ℝ) ≤
          (2 : ℝ) ^ ((19 : ℝ) + 21 / 4) := by
        rw [← hconst]
        exact hfactorMul
      have hpowpos : 0 ≤
          (2 : ℝ) ^ ((7 / 4 : ℝ) * boundaryEntropyGamma k) :=
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
      calc
        6 * (chargeCoverScale : ℝ) *
            ((4 + Real.sqrt 2) ^ (7 / 4 : ℝ) *
              (2 : ℝ) ^ ((7 / 4 : ℝ) * boundaryEntropyGamma k)) =
          (6 * (chargeCoverScale : ℝ) *
            (4 + Real.sqrt 2) ^ (7 / 4 : ℝ)) *
              (2 : ℝ) ^ ((7 / 4 : ℝ) * boundaryEntropyGamma k) := by ring
        _ ≤ (2 : ℝ) ^ ((19 : ℝ) + 21 / 4) *
            (2 : ℝ) ^ ((7 / 4 : ℝ) * boundaryEntropyGamma k) :=
          mul_le_mul_of_nonneg_right hcoeff' hpowpos
    calc
      3 * (2 * (chargeCoverScale : ℝ) *
          ((4 + Real.sqrt 2) * (2 : ℝ) ^ boundaryEntropyGamma k) ^
            chargeCoverExponent) =
        6 * (chargeCoverScale : ℝ) *
          ((4 + Real.sqrt 2) ^ (7 / 4 : ℝ) *
            (2 : ℝ) ^ ((7 / 4 : ℝ) * boundaryEntropyGamma k)) := by
              rw [chargeCoverExponent, Real.mul_rpow (by positivity) (by positivity),
                hradpow]
              ring
      _ ≤ (2 : ℝ) ^ ((19 : ℝ) + 21 / 4) *
          (2 : ℝ) ^ ((7 / 4 : ℝ) * boundaryEntropyGamma k) := htotal
      _ = (2 : ℝ) ^ ((19 : ℝ) + 21 / 4 +
          (7 / 4 : ℝ) * boundaryEntropyGamma k) := by
            rw [← Real.rpow_add (by norm_num)]
      _ ≤ (2 : ℝ) ^ ((k : ℝ) - 2) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hk2 : 2 ≤ k := by omega
  have hquarter : (2 : ℝ) ^ ((k : ℝ) - 2) =
      (1 / 4 : ℝ) * (2 : ℝ) ^ k := by
    have hcast : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
      rw [Nat.cast_sub hk2]
      norm_num
    rw [← hcast, Real.rpow_natCast]
    have hpow : (2 : ℕ) ^ k = (2 : ℕ) ^ (k - 2) * 2 ^ 2 := by
      rw [← Nat.pow_add, Nat.sub_add_cancel hk2]
    have hpowR : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 2) * 4 := by
      rw [← Nat.sub_add_cancel hk2, pow_add]
      norm_num
    rw [hpowR]
    ring
  rw [hquarter] at hrad
  have hsum :
      6 * (2 : ℝ) ^ boundaryEntropyGamma k +
          3 * (2 * (chargeCoverScale : ℝ) *
            ((4 + Real.sqrt 2) * (2 : ℝ) ^ boundaryEntropyGamma k) ^
              chargeCoverExponent) ≤
        (5 / 8 : ℝ) * (2 : ℝ) ^ k := by
    nlinarith only [hfirst, hrad]
  have hsidePos : 0 < (2 : ℝ) ^ k := by positivity
  nlinarith only [hsum, hsidePos]

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
