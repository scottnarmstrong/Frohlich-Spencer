/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.BranchGaussianD
public import FroehlichSpencer.FS82.XY.AssignmentPattern

/-!
# currents that are not closed drop out of the gauge average

The chart-free form of the reduction in `XY/ClosedLineage3.lean`.

Suppose that whenever a signed
sum `∑ σ_i J_i` of the family is closed, every `J_i` with `σ_i ≠ 0` is closed (for the dual complex
this is `DualD.coClosed_of_separated_sum`).

Then under the gauge average the currents that are not
closed may be removed from a product of cosine factors: their activities are replaced by zero.

* `closedCurrentD`, `closedActivityD`.
* `integral_cosineProduct_eq_closedD`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.XY.GaugeAverage
open FroehlichSpencer.FS82.Gaussian.RenormalizedFamily.RenormalizedCharacters

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]

/-- The current of a lineage, set to zero when it is not closed. -/
def closedCurrentD (D : V → E → ℤ) (j : E → ℤ) : E → ℤ := if ClosedD D j then j else 0

/-- The activity of a lineage, set to zero when its current is not closed. -/
def closedActivityD (D : V → E → ℤ) (K : ℝ) (j : E → ℤ) : ℝ := if ClosedD D j then K else 0

omit [DecidableEq E] in
theorem closedCurrentD_of_closed {D : V → E → ℤ} {j : E → ℤ} (hj : ClosedD D j) :
    closedCurrentD D j = j := by
  simp [closedCurrentD, hj]

omit [DecidableEq E] in
theorem closedCurrentD_of_not_closed {D : V → E → ℤ} {j : E → ℤ} (hj : ¬ ClosedD D j) :
    closedCurrentD D j = 0 := by
  simp [closedCurrentD, hj]

omit [DecidableEq E] in
theorem closedActivityD_of_closed {D : V → E → ℤ} (K : ℝ) {j : E → ℤ} (hj : ClosedD D j) :
    closedActivityD D K j = K := by
  simp [closedActivityD, hj]

omit [DecidableEq E] in
theorem closedActivityD_of_not_closed {D : V → E → ℤ} (K : ℝ) {j : E → ℤ}
    (hj : ¬ ClosedD D j) : closedActivityD D K j = 0 := by
  simp [closedActivityD, hj]

omit [Fintype V] [DecidableEq E] in
theorem closedD_zero (D : V → E → ℤ) : ClosedD D (0 : E → ℤ) := by
  intro v
  simp [divergenceD]

omit [DecidableEq E] in
theorem closedCurrentD_closed (D : V → E → ℤ) (j : E → ℤ) : ClosedD D (closedCurrentD D j) := by
  by_cases hj : ClosedD D j
  · rw [closedCurrentD_of_closed hj]
    exact hj
  · rw [closedCurrentD_of_not_closed hj]
    exact closedD_zero D

omit [DecidableEq E] in
theorem closedCurrentD_ne_zero_imp {D : V → E → ℤ} {j : E → ℤ} {e : E}
    (h : closedCurrentD D j e ≠ 0) : j e ≠ 0 ∧ ClosedD D j := by
  by_cases hj : ClosedD D j
  · rw [closedCurrentD_of_closed hj] at h
    exact ⟨h, hj⟩
  · rw [closedCurrentD_of_not_closed hj] at h
    exact absurd rfl h

/-- **A family of currents under the gauge average**: when closed signed sums split, the currents
that are not closed may be removed. -/
theorem integral_cosineProduct_eq_closedD {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : V → E → ℤ) {S : Matrix E E ℝ} (hS : S.PosSemidef)
    (K : ι → ℝ) (J : ι → E → ℤ) (shift : E → ℝ)
    (hsplit : ∀ σ : ι → Sign, ClosedD D (signedSum J σ) → ∀ i, σ i ≠ 0 → ClosedD D (J i)) :
    ∫ ω, ∏ i, (1 + K i * Real.cos (linkPairing (gaugeFieldD D ω) (J i) +
        linkPairing shift (J i))) ∂gaugeMeasureD V S =
      ∫ ω, ∏ i, (1 + closedActivityD D (K i) (J i) *
        Real.cos (linkPairing (gaugeFieldD D ω) (closedCurrentD D (J i)) +
          linkPairing shift (closedCurrentD D (J i)))) ∂gaugeMeasureD V S := by
  apply Complex.ofReal_injective
  rw [integral_cosineProductD D hS K (fun i => linkPairing shift (J i)) J,
    integral_cosineProductD D hS (fun i => closedActivityD D (K i) (J i))
      (fun i => linkPairing shift (closedCurrentD D (J i))) (fun i => closedCurrentD D (J i))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hP : ∀ i, σ i ≠ 0 → ClosedD D (J i)
  · have hw : signWeight K (fun i => linkPairing shift (J i)) σ =
        signWeight (fun i => closedActivityD D (K i) (J i))
          (fun i => linkPairing shift (closedCurrentD D (J i))) σ := by
      unfold signWeight
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : σ i = 0
      · simp [hi, signCoeff, signValue]
      · beta_reduce
        rw [closedActivityD_of_closed _ (hP i hi), closedCurrentD_of_closed (hP i hi)]
    have hs : signedSum J σ = signedSum (fun i => closedCurrentD D (J i)) σ := by
      funext e
      unfold signedSum
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : σ i = 0
      · simp [hi, signZ]
      · beta_reduce
        rw [closedCurrentD_of_closed (hP i hi)]
    rw [hw, hs]
  · push Not at hP
    obtain ⟨i, hi, hnot⟩ := hP
    have hleft : characterValueD D S (signedSum J σ) = 0 :=
      characterValueD_of_not_closed _ _ fun hsum => hnot (hsplit σ hsum i hi)
    have hright : signWeight (fun i => closedActivityD D (K i) (J i))
        (fun i => linkPairing shift (closedCurrentD D (J i))) σ = 0 := by
      unfold signWeight
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      beta_reduce
      rw [closedActivityD_of_not_closed _ hnot, signCoeff_eq]
      simp [hi]
    rw [hleft, hright, mul_zero, zero_mul]

end FroehlichSpencer.FS82.XY.DualD

end
