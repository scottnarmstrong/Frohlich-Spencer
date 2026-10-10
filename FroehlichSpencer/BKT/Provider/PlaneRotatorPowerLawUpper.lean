/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.PlaneRotatorCorrelation
public import FroehlichSpencer.BKT.Bridge.PlaneRotatorEuclidean
public import FroehlichSpencer.BKT.Rotator.Transition.PowerLaw
public import FroehlichSpencer.BKT.Surface.PlaneRotatorCorrelation
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.planeRotator_powerLaw_upper_bound`

This module contains `FroehlichSpencer.BKT.Provider.planeRotator_powerLaw_upper_bound`, the proof of
the statement `FroehlichSpencer.BKT.planeRotator_powerLaw_upper_bound` (file
`FroehlichSpencer/BKT/Surface/PlaneRotatorPowerLawUpper.lean`, the weak form of FS81 (1.31)).

It is
imported only by that statement.

Route: the internal McBryan–Spencer bound `freeTwoPointLimit_le_rpow`
(`⟨S_u · S_v⟩ ≤ e^{5/8} (|u-v|₁ + 1)^{-msExponent β}`) and `freeTwoPointLimit_nonneg`, with
`c = 1/32`, `K = e^{5/8}`, and `|·|₂ ≤ |·|₁`.
-/

@[expose] public section

open FroehlichSpencer.BKT.Rotator.Ginibre FroehlichSpencer.BKT.Rotator.Transition
open FroehlichSpencer.BKT.Bridge.PlaneRotatorEuclidean

noncomputable section

namespace FroehlichSpencer.BKT.Provider

theorem planeRotator_powerLaw_upper_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (hβ : 0 ≤ β), 0 < β → ∃ K : ℝ, ∀ j ℓ : ℤ × ℤ,
      0 ≤ planeRotatorCorrelation β hβ 1 j ℓ ∧
        planeRotatorCorrelation β hβ 1 j ℓ ≤
          K * (1 + Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2)) ^
            (-(c * min 1 (1 / β))) := by
  refine ⟨1 / 32, by norm_num, fun β hβ hβpos => ⟨Real.exp (5 / 8), fun j ℓ => ⟨?_, ?_⟩⟩⟩
  · rw [Bridge.PlaneRotatorCorrelation.planeRotatorCorrelation_eq_freeTwoPointLimit]
    exact freeTwoPointLimit_nonneg hβ 1 j ℓ
  · rw [Bridge.PlaneRotatorCorrelation.planeRotatorCorrelation_eq_freeTwoPointLimit]
    refine (freeTwoPointLimit_le_rpow hβpos j ℓ).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have hs : 1 / 32 * min 1 (1 / β) ≤ msExponent β := by
      unfold msExponent
      have e : (1 : ℝ) / (32 * β) = 1 / 32 * (1 / β) := by field_simp
      rw [e]
      refine le_min ?_ ?_
      · have := min_le_left (1 : ℝ) (1 / β)
        linarith
      · have := min_le_right (1 : ℝ) (1 / β)
        linarith
    have hbase : (1 : ℝ) ≤ (l1Norm (j - ℓ) : ℝ) + 1 := by
      linarith [Nat.cast_nonneg (α := ℝ) (l1Norm (j - ℓ))]
    have hepos : 0 < 1 + euclid j ℓ := by positivity
    calc ((l1Norm (j - ℓ) : ℝ) + 1) ^ (-msExponent β)
        ≤ ((l1Norm (j - ℓ) : ℝ) + 1) ^ (-(1 / 32 * min 1 (1 / β))) :=
          Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
      _ ≤ (1 + euclid j ℓ) ^ (-(1 / 32 * min 1 (1 / β))) := by
          refine Real.rpow_le_rpow_of_nonpos hepos (by linarith [euclid_le_l1 j ℓ]) ?_
          have : 0 ≤ 1 / 32 * min 1 (1 / β) := by positivity
          linarith

end FroehlichSpencer.BKT.Provider

end
