/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Transition.L1Distance
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
The statements of source's transition package ((1.30), the weak (1.31), the
transition theorem) measure `|j - ℓ|` in the Euclidean norm; the internal `Rotator/Transition`
estimates use the graph distance `l1Norm (j - ℓ)`.

Here `|x|₂ ≤ |x|₁ ≤ √2 |x|₂`
(`euclid_le_l1`, `l1_le_euclid`).

source's `Bridge.PlaneRotatorCorrelation.l1Norm_le_two_euclideanRadius` is the weaker
`|x|₁ ≤ 2 |x|₂`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.PlaneRotatorEuclidean

open FroehlichSpencer.BKT.Rotator.Transition

/-- The Euclidean norm of `j - ℓ`. -/
abbrev euclid (j ℓ : ℤ × ℤ) : ℝ :=
  Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2)

theorem l1Norm_cast (j ℓ : ℤ × ℤ) :
    (l1Norm (j - ℓ) : ℝ) = |((j.1 - ℓ.1 : ℤ) : ℝ)| + |((j.2 - ℓ.2 : ℤ) : ℝ)| := by
  simp only [l1Norm, Prod.fst_sub, Prod.snd_sub, Nat.cast_add, Nat.cast_natAbs, Int.cast_abs]

theorem euclid_le_l1 (j ℓ : ℤ × ℤ) : euclid j ℓ ≤ (l1Norm (j - ℓ) : ℝ) := by
  rw [l1Norm_cast]
  set a : ℝ := ((j.1 - ℓ.1 : ℤ) : ℝ)
  set b : ℝ := ((j.2 - ℓ.2 : ℤ) : ℝ)
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b, mul_nonneg (abs_nonneg a) (abs_nonneg b)]

theorem l1_le_euclid (j ℓ : ℤ × ℤ) : (l1Norm (j - ℓ) : ℝ) ≤ Real.sqrt 2 * euclid j ℓ := by
  rw [l1Norm_cast, euclid, ← Real.sqrt_mul (by norm_num)]
  set a : ℝ := ((j.1 - ℓ.1 : ℤ) : ℝ)
  set b : ℝ := ((j.2 - ℓ.2 : ℤ) : ℝ)
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith [sq_abs a, sq_abs b, sq_nonneg (|a| - |b|)]

end FroehlichSpencer.BKT.Bridge.PlaneRotatorEuclidean

end
