/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Transition.L1Distance
public import FroehlichSpencer.BKT.Surface.PlaneRotatorCorrelationSpec
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import FroehlichSpencer.BKT.Bridge.PlaneRotatorLaw
import Mathlib.Tactic

/-!
The net-limit correlation `planeRotatorCorrelation` is the internal Ginibre free limit
`freeTwoPointLimit` (`planeRotatorCorrelation_eq_freeTwoPointLimit`, from the
characterization `planeRotatorCorrelation_spec`).

`l1Norm_le_two_euclideanRadius` and
`euclideanProfile_le_l1Profile` convert the internal ℓ¹ profile to the Euclidean one.

With
the internal `PlaneRotator.rotator_theoremC` these lemmas prove the roots
`planeRotator_powerLaw_lower_bound` (FS81 Theorem C, plane rotator) and
`planeRotator_harmonic_powerLaw_lower_bound` (FS81 (6.1)); providers in `BKT/Provider/`.
-/

@[expose] public section

open Filter

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.PlaneRotatorCorrelation

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Rotator.Transition
open FroehlichSpencer.BKT.Bridge.PlaneRotatorLaw

/-- The package's net-limit correlation is the internal Ginibre free two-point limit. -/
theorem planeRotatorCorrelation_eq_freeTwoPointLimit
    (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ) (j ℓ : ℤ × ℤ) :
    planeRotatorCorrelation β hβ ξ j ℓ = freeTwoPointLimit β hβ ξ j ℓ := by
  exact ((planeRotatorCorrelation_spec β hβ ξ j ℓ _).mp
    (tendsto_planeRotatorTwoPoint β hβ ξ j ℓ)).symm

/-- The internal graph distance is bounded by twice the Euclidean distance. -/
theorem l1Norm_le_two_euclideanRadius (u v : ℤ × ℤ) :
    (l1Norm (u - v) : ℝ) ≤
      2 * Real.sqrt (((u.1 - v.1 : ℤ) : ℝ) ^ 2 + ((u.2 - v.2 : ℤ) : ℝ) ^ 2) := by
  let dx : ℝ := ((u.1 - v.1 : ℤ) : ℝ)
  let dy : ℝ := ((u.2 - v.2 : ℤ) : ℝ)
  have hx2 : dx ^ 2 ≤ dx ^ 2 + dy ^ 2 := by nlinarith [sq_nonneg dy]
  have hy2 : dy ^ 2 ≤ dx ^ 2 + dy ^ 2 := by nlinarith [sq_nonneg dx]
  have hx : |dx| ≤ Real.sqrt (dx ^ 2 + dy ^ 2) := by
    have h := Real.sqrt_le_sqrt hx2
    rw [Real.sqrt_sq_eq_abs] at h
    exact h
  have hy : |dy| ≤ Real.sqrt (dx ^ 2 + dy ^ 2) := by
    have h := Real.sqrt_le_sqrt hy2
    rw [Real.sqrt_sq_eq_abs] at h
    exact h
  have hl1 : (l1Norm (u - v) : ℝ) = |dx| + |dy| := by
    simp [l1Norm, dx, dy, Nat.cast_natAbs]
  rw [hl1]
  dsimp [dx, dy] at hx hy ⊢
  nlinarith

/--
Replacing the internal ℓ¹ radius by the Euclidean radius costs a factor `2^(-q)`.
-/
theorem euclideanProfile_le_l1Profile (q : ℝ) (hq : 0 ≤ q) (u v : ℤ × ℤ) :
    (Real.exp (-q) * (2 : ℝ) ^ (-q)) *
        (1 + Real.sqrt (((u.1 - v.1 : ℤ) : ℝ) ^ 2 + ((u.2 - v.2 : ℤ) : ℝ) ^ 2)) ^ (-q) ≤
      Real.exp (-q) * ((l1Norm (u - v) : ℝ) + 1) ^ (-q) := by
  let r := Real.sqrt (((u.1 - v.1 : ℤ) : ℝ) ^ 2 + ((u.2 - v.2 : ℤ) : ℝ) ^ 2)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hdist := l1Norm_le_two_euclideanRadius u v
  have hbase : ((l1Norm (u - v) : ℝ) + 1) ≤ 2 * (1 + r) := by
    dsimp [r]
    linarith [hdist]
  have hpow : (2 * (1 + r)) ^ (-q) ≤ ((l1Norm (u - v) : ℝ) + 1) ^ (-q) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
  calc
    (Real.exp (-q) * (2 : ℝ) ^ (-q)) * (1 + r) ^ (-q) =
        Real.exp (-q) * (2 * (1 + r)) ^ (-q) := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
          ring
    _ ≤ Real.exp (-q) * ((l1Norm (u - v) : ℝ) + 1) ^ (-q) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le

end FroehlichSpencer.BKT.Bridge.PlaneRotatorCorrelation

end
