/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Compact.Theorem71
public import FroehlichSpencer.BKT.Generic.Marked.Gap
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
The internal clock estimates use the ℓ¹ distance `Clock.Compact.l1Dist 0 x`; the clock
statements use the Euclidean `|x|`.

Here `|x| ≤ |x|₁ ≤ 2 |x|` (`euclid_le_l1Dist`,
`l1Dist_le_two_euclid`), the two power-law conversions (`l1Profile_le_euclidProfile`,
`euclidProfile_le_l1Profile`), and the restricted harmonics `1 ≤ ξ ≤ n - 1` of the statements
as the natural harmonics of the internal ones (`harmonic_toNat`, `dipoleGap_eq`).

They serve FS81
Theorem 7.1 (2) and result 4 .

They concern the
internal `Clock.Compact.l1Dist`; source's `Bridge.PlaneRotatorEuclidean` concerns the rotator's
`Rotator.Transition.l1Norm`.

This module imports no  file.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.ClockProfile

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.Marked (dipoleGap)

/-- The Euclidean norm `|x|`. -/
abbrev euclid (x : ℤ × ℤ) : ℝ := Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2)

theorem l1Dist_zero (x : ℤ × ℤ) :
    (Clock.Compact.l1Dist 0 x : ℝ) = |(x.1 : ℝ)| + |(x.2 : ℝ)| := by
  simp [Clock.Compact.l1Dist, Nat.cast_natAbs]

theorem euclid_le_l1Dist (x : ℤ × ℤ) : euclid x ≤ (Clock.Compact.l1Dist 0 x : ℝ) := by
  rw [l1Dist_zero, euclid, Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg (x.1 : ℝ), abs_nonneg (x.2 : ℝ), sq_abs (x.1 : ℝ), sq_abs (x.2 : ℝ),
    mul_nonneg (abs_nonneg (x.1 : ℝ)) (abs_nonneg (x.2 : ℝ))]

theorem l1Dist_le_two_euclid (x : ℤ × ℤ) : (Clock.Compact.l1Dist 0 x : ℝ) ≤ 2 * euclid x := by
  have hx : |(x.1 : ℝ)| ≤ euclid x := by
    rw [euclid, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (x.2 : ℝ)])
  have hy : |(x.2 : ℝ)| ≤ euclid x := by
    rw [euclid, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (x.1 : ℝ)])
  rw [l1Dist_zero]
  linarith

/-- An ℓ¹ power-law upper bound with exponent `c` gives a Euclidean one with any exponent
`0 ≤ p ≤ c`. -/
theorem l1Profile_le_euclidProfile {c p : ℝ} (hp : 0 ≤ p) (hpc : p ≤ c) (x : ℤ × ℤ) :
    ((Clock.Compact.l1Dist 0 x : ℝ) + 1) ^ (-c) ≤ (1 + euclid x) ^ (-p) := by
  have he : 0 ≤ euclid x := Real.sqrt_nonneg _
  have h1 : 1 ≤ (Clock.Compact.l1Dist 0 x : ℝ) + 1 := by linarith [euclid_le_l1Dist x]
  calc ((Clock.Compact.l1Dist 0 x : ℝ) + 1) ^ (-c)
      ≤ ((Clock.Compact.l1Dist 0 x : ℝ) + 1) ^ (-p) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    _ ≤ (1 + euclid x) ^ (-p) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [euclid_le_l1Dist x])
          (by linarith)

/-- An ℓ¹ power-law lower bound with exponent `p ≥ 0` gives a Euclidean one at the cost of the
factor `2^{-p}`. -/
theorem euclidProfile_le_l1Profile {p : ℝ} (hp : 0 ≤ p) (x : ℤ × ℤ) :
    (2 : ℝ) ^ (-p) * (1 + euclid x) ^ (-p) ≤ ((Clock.Compact.l1Dist 0 x : ℝ) + 1) ^ (-p) := by
  have he : 0 ≤ euclid x := Real.sqrt_nonneg _
  rw [← Real.mul_rpow (by norm_num) (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [l1Dist_le_two_euclid x])
    (by linarith)

/--
The restricted harmonics of the internal statements are those of the ones.
-/
theorem harmonic_toNat {n : ℕ} {ξ : ℤ} (h1 : 1 ≤ ξ) (h2 : ξ ≤ (n : ℤ) - 1) :
    0 < ξ.toNat ∧ ξ.toNat < n ∧ ((ξ.toNat : ℕ) : ℤ) = ξ := by
  refine ⟨by omega, by omega, Int.toNat_of_nonneg (by omega)⟩

theorem dipoleGap_eq {n : ℕ} {ξ : ℤ} (h1 : 1 ≤ ξ) :
    dipoleGap ((ξ.toNat : ℝ) / n) = min ((ξ : ℝ) / n) (1 - (ξ : ℝ) / n) := by
  have : ((ξ.toNat : ℕ) : ℝ) = (ξ : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (by omega)
  rw [dipoleGap, this]

end FroehlichSpencer.BKT.Bridge.ClockProfile

end
