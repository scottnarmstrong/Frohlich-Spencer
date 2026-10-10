/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.PlaneRotatorPowerLaw
public import FroehlichSpencer.BKT.Bridge.PlaneRotatorCorrelation
public import FroehlichSpencer.BKT.Bridge.PlaneRotatorEuclidean
public import FroehlichSpencer.BKT.Rotator.Transition.KTTransition
import Mathlib.Tactic

/-!
The route is the internal `exists_transition_of_powerLaw` (Ginibre monotonicity in
`β`, the high-temperature bound and the McBryan–Spencer bound), with the Euclidean/ℓ¹ comparison of
`Bridge.PlaneRotatorEuclidean` and source's
`Bridge.PlaneRotatorCorrelation.planeRotatorCorrelation_eq_freeTwoPointLimit`.

The provider of the
transition statement applies it to the Theorem C statement.
-/

@[expose] public section

open Filter Topology

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.PlaneRotatorTransition

open FroehlichSpencer.BKT FroehlichSpencer.BKT.Rotator.Ginibre FroehlichSpencer.BKT.Rotator.Transition
open FroehlichSpencer.BKT.Bridge.PlaneRotatorCorrelation FroehlichSpencer.BKT.Bridge.PlaneRotatorEuclidean

/-- source's Theorem C statement implies the transition statement. -/
theorem kosterlitzThouless_of_powerLaw (hTC : type_of% @planeRotator_powerLaw_lower_bound) :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ (β : ℝ) (hβ : 0 ≤ β), β < βc →
        ∃ C m : ℝ, 0 < m ∧ ∀ j ℓ : ℤ × ℤ,
          planeRotatorCorrelation β hβ 1 j ℓ ≤
            C * Real.exp (-m * Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2))) ∧
      (∀ (β : ℝ) (hβ : 0 ≤ β), βc < β →
        (¬ ∃ C m : ℝ, 0 < m ∧ ∀ j ℓ : ℤ × ℤ,
          planeRotatorCorrelation β hβ 1 j ℓ ≤
            C * Real.exp (-m * Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2))) ∧
        ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ j ℓ : ℤ × ℤ,
          R ≤ Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2) →
            planeRotatorCorrelation β hβ 1 j ℓ ≤ ε) := by
  obtain ⟨β₀, β', -, hTC⟩ := hTC
  have hpl : ∃ β₁ : ℝ, ∀ β (hβ : 0 ≤ β), β₁ ≤ β → HasPowerLawLowerBound β hβ := by
    refine ⟨β₀ + 1, fun β hβ hβ₁ => ?_⟩
    obtain ⟨hβ', A, hA, hbound⟩ := hTC β hβ (by linarith)
    have hp : 0 ≤ 1 / (2 * Real.pi * β' β) := by
      have : 0 < β' β := lt_trans (by positivity) hβ'
      positivity
    refine ⟨A, 1 / (2 * Real.pi * β' β), hA, fun u v => ?_⟩
    rw [← planeRotatorCorrelation_eq_freeTwoPointLimit]
    refine le_trans ?_ (hbound u v)
    refine mul_le_mul_of_nonneg_left ?_ hA.le
    have hepos : 0 < 1 + euclid u v := by positivity
    rw [add_comm ((l1Norm (u - v)) : ℝ) 1]
    exact Real.rpow_le_rpow_of_nonpos hepos (by linarith [euclid_le_l1 u v]) (by linarith)
  obtain ⟨βc, hβc, hbelow, habove⟩ := exists_transition_of_powerLaw hpl
  refine ⟨βc, by linarith, fun β hβ hlt => ?_, fun β hβ hlt => ⟨?_, ?_⟩⟩
  · obtain ⟨C, m, hm, hC⟩ := hbelow β hβ hlt
    refine ⟨max C 0, m, hm, fun j ℓ => ?_⟩
    rw [planeRotatorCorrelation_eq_freeTwoPointLimit]
    refine (hC j ℓ).trans ?_
    calc C * Real.exp (-m * l1Norm (j - ℓ)) ≤ max C 0 * Real.exp (-m * l1Norm (j - ℓ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ max C 0 * Real.exp (-m * euclid j ℓ) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (le_max_right _ _)
          exact mul_le_mul_of_nonpos_left (euclid_le_l1 j ℓ) (by linarith)
  · rintro ⟨C, m, hm, hC⟩
    refine (habove β hβ hlt).1 ⟨max C 0, m / Real.sqrt 2, by positivity, fun u v => ?_⟩
    rw [← planeRotatorCorrelation_eq_freeTwoPointLimit]
    refine (hC u v).trans ?_
    have hs : 0 < Real.sqrt 2 := by positivity
    calc C * Real.exp (-m * euclid u v) ≤ max C 0 * Real.exp (-m * euclid u v) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ max C 0 * Real.exp (-(m / Real.sqrt 2) * l1Norm (u - v)) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (le_max_right _ _)
          have h := l1_le_euclid u v
          have : (m / Real.sqrt 2) * l1Norm (u - v) ≤ m * euclid u v := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hs]
            nlinarith [mul_le_mul_of_nonneg_left h hm.le]
          linarith
  · intro ε hε
    obtain ⟨R, hR⟩ := (habove β hβ hlt).2 ε hε
    refine ⟨R, fun j ℓ hjℓ => ?_⟩
    rw [planeRotatorCorrelation_eq_freeTwoPointLimit]
    exact hR j ℓ (by exact_mod_cast hjℓ.trans (euclid_le_l1 j ℓ))

end FroehlichSpencer.BKT.Bridge.PlaneRotatorTransition

end
