/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.PlaneRotatorCorrelation
public import FroehlichSpencer.BKT.Bridge.PlaneRotatorEuclidean
public import FroehlichSpencer.BKT.Rotator.Transition.HighTemperature
public import FroehlichSpencer.BKT.Surface.PlaneRotatorCorrelation
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.planeRotator_highTemperature_expDecay`

This module contains `FroehlichSpencer.BKT.Provider.planeRotator_highTemperature_expDecay`, the proof
of the statement `FroehlichSpencer.BKT.planeRotator_highTemperature_expDecay` (file
`FroehlichSpencer/BKT/Surface/PlaneRotatorHighTemperature.lean`, FS81 (1.30)).

Route: the internal high-temperature bound `freeTwoPointLimit_le_pow` (`⟨S_u · S_v⟩ ≤ (2β)^{|u-v|₁}`),
with `β₁ = 1/2`, `C = 1`, `m = -log (max (2β) (1/2))`, and `|·|₂ ≤ |·|₁`.
-/

@[expose] public section

open FroehlichSpencer.BKT.Rotator.Ginibre FroehlichSpencer.BKT.Rotator.Transition
open FroehlichSpencer.BKT.Bridge.PlaneRotatorEuclidean

noncomputable section

namespace FroehlichSpencer.BKT.Provider

theorem planeRotator_highTemperature_expDecay :
    ∃ β₁ : ℝ, 0 < β₁ ∧ ∀ (β : ℝ) (hβ : 0 ≤ β), β < β₁ →
      ∃ C m : ℝ, 0 < m ∧ ∀ j ℓ : ℤ × ℤ,
        planeRotatorCorrelation β hβ 1 j ℓ ≤
          C * Real.exp (-m * Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2)) := by
  refine ⟨1 / 2, by norm_num, fun β hβ hlt => ?_⟩
  set r := max (2 * β) (1 / 2)
  have hr0 : 0 < r := lt_max_of_lt_right (by norm_num)
  have hr1 : r < 1 := max_lt (by linarith) (by norm_num)
  have hm : 0 < -Real.log r := by linarith [Real.log_neg hr0 hr1]
  refine ⟨1, -Real.log r, hm, fun j ℓ => ?_⟩
  rw [Bridge.PlaneRotatorCorrelation.planeRotatorCorrelation_eq_freeTwoPointLimit, one_mul]
  refine (freeTwoPointLimit_le_pow hβ j ℓ).trans ?_
  have h1 : (2 * β) ^ l1Norm (j - ℓ) ≤ r ^ l1Norm (j - ℓ) :=
    pow_le_pow_left₀ (by positivity) (le_max_left _ _) _
  have h2 : r ^ l1Norm (j - ℓ) = Real.exp (-(-Real.log r) * (l1Norm (j - ℓ) : ℝ)) := by
    rw [neg_neg, ← Real.rpow_natCast, Real.rpow_def_of_pos hr0]
  refine h1.trans (h2 ▸ Real.exp_le_exp.mpr ?_)
  exact mul_le_mul_of_nonpos_left (euclid_le_l1 j ℓ) (by linarith)

end FroehlichSpencer.BKT.Provider

end
