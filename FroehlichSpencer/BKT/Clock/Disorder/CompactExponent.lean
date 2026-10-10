/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Disorder.LowerTransfer
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Power-law and limit-point transfer for clock disorder

This module isolates the final real-variable step of (7.5). A logarithmic vortex-energy bound and
a shifted integral lower bound imply the stated power law. A finite-volume bound uniform along the
centered-square exhaustion passes to each selected limit point.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open Filter Topology

/-- The effective inverse-temperature coefficient arising from a curvature and profile-energy
constant. -/
def clockDisorderEffectiveBeta (κ C : ℝ) : ℝ := 2 * Real.pi * κ * C

private theorem shifted_lower_to_power (r : ℕ) (ξ κ C ε E R : ℝ)
    (hκ : 0 ≤ κ)
    (henergy : E ≤ ξ ^ 2 * C * (1 + Real.log (1 + (r : ℝ))))
    (hbranch : Real.exp (-(κ * E + ε)) ≤ R) :
    Real.exp (-ε - κ * C * ξ ^ 2) *
      (1 + (r : ℝ)) ^ (-(κ * C * ξ ^ 2)) ≤ R := by
  have hx : 0 < 1 + (r : ℝ) := by positivity
  rw [Real.rpow_def_of_pos hx]
  have hmul : κ * E ≤ κ * (ξ ^ 2 * C * (1 + Real.log (1 + (r : ℝ)))) :=
    mul_le_mul_of_nonneg_left henergy hκ
  have hrewrite :
      (-ε - κ * C * ξ ^ 2) + Real.log (1 + (r : ℝ)) * (-(κ * C * ξ ^ 2)) =
        -(κ * (ξ ^ 2 * C * (1 + Real.log (1 + (r : ℝ)))) + ε) := by ring
  calc
    Real.exp (-ε - κ * C * ξ ^ 2) *
        Real.exp (Real.log (1 + (r : ℝ)) * (-(κ * C * ξ ^ 2))) =
      Real.exp (-(κ * (ξ ^ 2 * C * (1 + Real.log (1 + (r : ℝ)))) + ε)) := by
        rw [← Real.exp_add, hrewrite]
    _ ≤ Real.exp (-(κ * E + ε)) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ R := hbranch

/-- If the residual profile has logarithmic energy and the shifted branch has curvature cost
`κ E + ε`, the disorder expectation has a power-law lower bound. The effective parameter is
`β''' = 2π κ C`, with the exponent shared over the twist variable. -/
theorem compactBranch_lower_to_power (r : ℕ) (ξ κ C ε E R β''' : ℝ)
    (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (henergy : E ≤ ξ ^ 2 * C * (1 + Real.log (1 + (r : ℝ))))
    (hbranch : Real.exp (-(κ * E + ε)) ≤ R)
    (hβ''' : β''' = clockDisorderEffectiveBeta κ C) :
    0 ≤ ξ ^ 2 * β''' / (2 * Real.pi) ∧
      Real.exp (-ε - κ * C * ξ ^ 2) *
        (1 + (r : ℝ)) ^ (-(ξ ^ 2 * β''' / (2 * Real.pi))) ≤ R := by
  have hpower := shifted_lower_to_power r ξ κ C ε E R hκ henergy hbranch
  constructor
  · rw [hβ''', clockDisorderEffectiveBeta]
    positivity
  · have hexp : -(ξ ^ 2 * β''' / (2 * Real.pi)) = -(κ * C * ξ ^ 2) := by
      rw [hβ''', clockDisorderEffectiveBeta]
      field_simp
    rw [hexp]
    exact hpower

/-- A lower bound uniform along the free-square exhaustion passes to every selected clock-disorder
limit point. -/
theorem clockDisorderLimitPoint_ge_of_uniformLower (N r : ℕ) (β ξ b c : ℝ) (hN : 0 < N)
    (hr : 0 < r)
    (hfinite : ∀ t, b ≤ clockDisorderExpectationExhaustion N r β ξ hN hr t)
    (hc : IsClockDisorderLimitPoint N r β ξ c hN hr) : b ≤ c :=
  clockDisorderLimitPoint_ge_of_exhaustion N r β ξ b c hN hr hfinite hc

end FroehlichSpencer.BKT.Clock.Disorder

end
