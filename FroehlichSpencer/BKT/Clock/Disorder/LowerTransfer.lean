/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Disorder.Insertion
import Mathlib.Tactic

/-!
# Lower-bound transfer interfaces for clock disorder

It also records the elementary exponential-in-seam-length bound as
a positivity check.

These transfers do not establish the logarithmic shifted-profile estimate in
(7.5).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open Filter Topology
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Clock.Compact

/-- A lower bound valid for all sufficiently large Fejér cutoffs passes to the finite clock
disorder expectation. -/
theorem clockDisorderExpectation_ge_of_fejerEventually {r L : ℕ} (N : ℕ) (β ξ b : ℝ)
    (hN : 0 < N) (hβ : 0 ≤ β) (hL : 0 < L) (hr : r ≤ L)
    (hfejer : ∀ᶠ M : ℕ in atTop, b ≤ clockDisorderFejerRatio N β ξ hN hL hr M) :
    b ≤ clockDisorderExpectation N β ξ hN hL hr := by
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    (tendsto_clockDisorderFejerRatio N β ξ hN hβ hL hr) hfejer

/-- A lower bound uniform along the centered-square exhaustion passes to every selected
subsequential disorder limit. -/
theorem clockDisorderLimitPoint_ge_of_exhaustion (N r : ℕ) (β ξ b c : ℝ) (hN : 0 < N)
    (hr : 0 < r)
    (hfinite : ∀ t, b ≤ clockDisorderExpectationExhaustion N r β ξ hN hr t)
    (hc : IsClockDisorderLimitPoint N r β ξ c hN hr) : b ≤ c := by
  rcases hc with ⟨s, hs, htend⟩
  exact le_of_tendsto_of_tendsto tendsto_const_nhds htend
    (eventually_atTop.2 ⟨0, fun t _ => hfinite (s t)⟩)

/-- A single lower bound on all sufficiently large Fejér cutoffs in every exhausting box passes
to every selected thermodynamic disorder limit. -/
theorem clockDisorderLimitPoint_ge_of_fejerEventually (N r : ℕ) (β ξ b c : ℝ)
    (hN : 0 < N) (hβ : 0 ≤ β) (hr : 0 < r)
    (hfejer : ∀ t : ℕ, ∀ᶠ M : ℕ in atTop,
      b ≤ clockDisorderFejerRatio N β ξ hN (show 0 < r + t by omega)
        (show r ≤ r + t by omega) M)
    (hc : IsClockDisorderLimitPoint N r β ξ c hN hr) : b ≤ c := by
  apply clockDisorderLimitPoint_ge_of_exhaustion N r β ξ b c hN hr
  · intro t
    change b ≤ clockDisorderExpectation (r := r) (L := r + t) N β ξ hN (by omega) (by omega)
    exact clockDisorderExpectation_ge_of_fejerEventually N β ξ b hN hβ (by omega) (by omega)
      (hfejer t)
  · exact hc

/-- The one-bond clock disorder factor has a uniform elementary lower bound. -/
theorem clockDisorderFactor_ge {r L : ℕ} (N : ℕ) (β ξ : ℝ)
    (k : RotatorSpinSite (2 * L) → Fin N) (hL : 0 < L) (hr : r ≤ L) (i : Fin r) :
    Real.exp (-2 * |β|) ≤ clockDisorderFactor N β ξ k hL hr i := by
  unfold clockDisorderFactor
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  let d := clockAngles N k (seamUpperSite hL hr i) -
    clockAngles N k (seamLowerSite hL hr i)
  have hcos₁ : |Real.cos (d + 2 * Real.pi * ξ)| ≤ 1 := Real.abs_cos_le_one _
  have hcos₀ : |Real.cos d| ≤ 1 := Real.abs_cos_le_one _
  have h₁ : -( |β|) ≤ β * Real.cos (d + 2 * Real.pi * ξ) := by
    have h := mul_le_of_le_one_right (abs_nonneg β) hcos₁
    calc
      -|β| ≤ -(|β| * |Real.cos (d + 2 * Real.pi * ξ)|) := by linarith
      _ = -|β * Real.cos (d + 2 * Real.pi * ξ)| := by rw [abs_mul]
      _ ≤ β * Real.cos (d + 2 * Real.pi * ξ) := neg_abs_le _
  have h₀ : β * Real.cos d ≤ |β| := by
    calc
      β * Real.cos d ≤ |β * Real.cos d| := le_abs_self _
      _ = |β| * |Real.cos d| := abs_mul _ _
      _ ≤ |β| := mul_le_of_le_one_right (abs_nonneg β) hcos₀
  change -2 * |β| ≤ β * Real.cos (d + 2 * Real.pi * ξ) - β * Real.cos d
  linarith

/-- The full seam disorder insertion is bounded below by the product of the one-bond bounds. -/
theorem clockDisorder_ge {r L : ℕ} (N : ℕ) (β ξ : ℝ) (hN : 0 < N)
    (k : RotatorSpinSite (2 * L) → Fin N) (hL : 0 < L) (hr : r ≤ L) :
    Real.exp (-2 * |β|) ^ r ≤ clockDisorder N β ξ hN k hL hr := by
  unfold clockDisorder
  calc
    Real.exp (-2 * |β|) ^ r = ∏ _i : Fin r, Real.exp (-2 * |β|) := by simp
    _ ≤
        ∏ i : Fin r, clockDisorderFactor N β ξ k hL hr i := by
      refine Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) ?_
      intro i hi
      exact clockDisorderFactor_ge N β ξ k hL hr i
    _ = _ := rfl

/-- Positivity check for the finite clock disorder expectation. The estimate is exponential in
the seam length and is not the logarithmic estimate required by (7.5). -/
theorem clockDisorderExpectation_expLowerBound {r L : ℕ} (N : ℕ) (β ξ : ℝ)
    (hN : 0 < N) (hL : 0 < L) (hr : r ≤ L) :
    Real.exp (-2 * |β|) ^ r ≤ clockDisorderExpectation N β ξ hN hL hr := by
  rw [clockDisorderExpectation_eq_sum N β ξ hN hL hr]
  have hmass := sum_clockCombProbabilityMass_eq_one N L β hN
  have hmass_nonneg (k : RotatorSpinSite (2 * L) → Fin N) :
      0 ≤ clockCombProbabilityMass N L β hN k := by
    unfold clockCombProbabilityMass
    have hweight : 0 < clockBoxWeight N (2 * L) β k := by
      unfold clockBoxWeight
      exact Real.exp_pos _
    exact div_nonneg hweight.le (clockDisorderPartition_pos N L β hN).le
  calc
    Real.exp (-2 * |β|) ^ r =
        ∑ k : RotatorSpinSite (2 * L) → Fin N,
          Real.exp (-2 * |β|) ^ r * clockCombProbabilityMass N L β hN k := by
      rw [← Finset.mul_sum, hmass, mul_one]
    _ ≤ ∑ k : RotatorSpinSite (2 * L) → Fin N,
        clockDisorder N β ξ hN k hL hr * clockCombProbabilityMass N L β hN k :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
        (clockDisorder_ge N β ξ hN k hL hr) (hmass_nonneg k)

/-- Every selected thermodynamic disorder limit inherits the elementary exponential lower bound.
The estimate does not have the logarithmic scale required for (7.5). -/
theorem clockDisorderLimitPoint_expLowerBound (N r : ℕ) (β ξ c : ℝ) (hN : 0 < N)
    (hr : 0 < r) (hc : IsClockDisorderLimitPoint N r β ξ c hN hr) :
    Real.exp (-2 * |β|) ^ r ≤ c := by
  exact clockDisorderLimitPoint_ge_of_exhaustion N r β ξ (Real.exp (-2 * |β|) ^ r) c hN hr
    (fun t => clockDisorderExpectation_expLowerBound N β ξ hN (by omega) (by omega)) hc

end FroehlichSpencer.BKT.Clock.Disorder

end
