/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.CosineFourierSummable
public import FroehlichSpencer.BKT.Rotator.XYDuality

/-!
# Unconditional finite XY duality corollaries

The explicit coefficient summability and pointwise cosine expansion discharge the analytic
hypotheses of the finite XY identities.
-/

@[expose] public section

open Complex MeasureTheory
open FroehlichSpencer.BKT.Rotator

noncomputable section

namespace FroehlichSpencer.BKT.Rotator

variable {L : ℕ}


private theorem rotatorI_pointwise_expansion (b t : ℝ) :
    rotatorBondReal b t = ∑' m : ℤ,
      rotatorI b m * Complex.exp (Complex.I * (m : ℂ) * (t : ℂ)) := by
  simpa [rotatorBondReal] using (hasSum_rotatorI_mul_exp b t).tsum_eq.symm

/-- The internal spin density has its full current expansion, unconditionally in the cosine input.
-/
theorem rotatorSpinDensity_currentSeries_unconditional (b : ℝ)
    (θ : RotatorAngleConfiguration L) :
    (rotatorSpinDensity L b θ : ℂ) =
      ∑' q : RotatorInternalBond L → ℤ,
        rotatorCurrentFourierTerm (rotatorFreeGraph L) (rotatorIReal b) q
          (fun _ => 0) θ := by
  exact rotatorSpinDensity_currentSeries (L := L) b (summable_rotatorI b)
    (rotatorI_pointwise_expansion b) θ

/-- The marked spin density has its source-current expansion, unconditionally in the cosine
Fourier input. -/
theorem rotatorSpinDensity_mulCharacter_currentSeries_unconditional (b : ℝ)
    (a x : RotatorSpinSite L) (ξ : ℤ) (θ : RotatorAngleConfiguration L) :
    (rotatorSpinDensity L b θ : ℂ) * rotatorSpinCharacter L a x ξ θ =
      ∑' q : RotatorInternalBond L → ℤ,
        rotatorCurrentFourierTerm (rotatorFreeGraph L) (rotatorIReal b) q
          (rotatorTwoPointFrequency a x ξ) θ := by
  exact rotatorSpinDensity_mulCharacter_currentSeries (L := L) b
    (summable_rotatorI b) (rotatorI_pointwise_expansion b) a x ξ θ

/-- The exact raw partition identity, with its Fourier hypotheses discharged. -/
theorem rotatorPartitionIntegralInternal_eq_heightFactor_unconditional (b : ℝ) :
    (rotatorPartitionIntegralInternal L b : ℂ) =
      (2 * Real.pi : ℂ) ^ Fintype.card (RotatorSpinSite L) *
        rotatorHeightPartitionFactor L b := by
  exact rotatorPartitionIntegralInternal_eq_heightFactor (L := L) b
    (summable_rotatorI b) (rotatorI_pointwise_expansion b)

/-- The exact height partition factor is real, unconditionally in the cosine Fourier input. -/
theorem rotatorHeightPartitionFactor_im_zero_unconditional (b : ℝ) :
    (rotatorHeightPartitionFactor L b).im = 0 := by
  exact rotatorHeightPartitionFactor_im_zero (L := L) b
    (summable_rotatorI b) (rotatorI_pointwise_expansion b)

/-- The free-box height partition factor is strictly positive on the real axis. -/
theorem rotatorHeightPartitionFactor_re_pos_unconditional (b : ℝ) :
    0 < (rotatorHeightPartitionFactor L b).re := by
  exact rotatorHeightPartitionFactor_re_pos (L := L) b
    (summable_rotatorI b) (rotatorI_pointwise_expansion b)

/-- The raw marked integral identity, with the source current and Fourier input explicit. -/
theorem rotatorMarkedDensityIntegral_eq_heightMarkedFactor_unconditional (b : ℝ)
    (a x : RotatorSpinSite L) (ξ : ℤ) (j : RotatorInternalBond L → ℤ)
    (hj : ∀ v, rotatorCurrentDivergence j v = rotatorTwoPointFrequency a x ξ v) :
    (∫ θ : RotatorAngleConfiguration L,
      (rotatorSpinDensity L b θ : ℂ) * rotatorSpinCharacter L a x ξ θ
        ∂rotatorRawAngleMeasure (RotatorSpinSite L)) =
      (2 * Real.pi : ℂ) ^ Fintype.card (RotatorSpinSite L) *
        rotatorHeightMarkedFactor L b j := by
  exact rotatorMarkedDensityIntegral_eq_heightMarkedFactor (L := L) b
    (summable_rotatorI b) (rotatorI_pointwise_expansion b) a x ξ j hj

/-- The normalized internal-law character expectation is the height-factor ratio. -/
theorem rotatorMeasureInternal_character_integral_eq_heightRatio_unconditional (b : ℝ)
    (a x : RotatorSpinSite L) (ξ : ℤ) (j : RotatorInternalBond L → ℤ)
    (hj : ∀ v, rotatorCurrentDivergence j v = rotatorTwoPointFrequency a x ξ v) :
    (∫ θ, rotatorSpinCharacter L a x ξ θ ∂rotatorMeasureInternal L b) =
      rotatorHeightMarkedFactor L b j / rotatorHeightPartitionFactor L b := by
  exact rotatorMeasureInternal_character_integral_eq_heightRatio (L := L) b
    (summable_rotatorI b) (rotatorI_pointwise_expansion b) a x ξ j hj

/-- The normalized straight-row two-point identity, unconditionally in the cosine Fourier input. -/
theorem rotatorMeasureInternal_straightTwoPoint_eq_heightRatio_unconditional (b : ℝ)
    (n : ℕ) (ξ : ℤ) (hn : 2 ≤ n) (hnL : n ≤ L) :
    (∫ θ, rotatorSpinCharacter L
      ((⟨0, by omega⟩ : Fin (L + 1)), (⟨1, by omega⟩ : Fin (L + 1)))
      ((⟨n, by omega⟩ : Fin (L + 1)), (⟨1, by omega⟩ : Fin (L + 1))) ξ θ
      ∂rotatorMeasureInternal L b) =
      rotatorHeightMarkedFactor L b (rotatorStraightSourceCurrent (L := L) n ξ) /
        rotatorHeightPartitionFactor L b := by
  exact rotatorMeasureInternal_straightTwoPoint_eq_heightRatio (L := L) b
    (summable_rotatorI b) (rotatorI_pointwise_expansion b) n ξ hn hnL

end FroehlichSpencer.BKT.Rotator
end
