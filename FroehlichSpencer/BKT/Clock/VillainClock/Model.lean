/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Ginibre.Models

/-!
# The free Villain-constrained clock model

This is the free-boundary model from FS81 (1.26) and Remark 4 on the finite clock support from
(7.2).

The single-site measure is the counting measure on the N clock angles, and the edge weight
is the periodized Gaussian Villain weight from (1.27).
-/

@[expose] public section

open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Rotator.Ginibre

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

/-- The free-boundary Villain model with the single-site angle constrained to the N clock values.
The finite volume and its thermodynamic limit are inherited from `FreeModel`. -/
def model (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 < β) : FreeModel where
  ν := clockMeasure N
  lam := clockFourier N
  w := villainWeight β
  isFinite := inferInstance
  fourier := hasRealFourier_clock hN
  mass_ne_zero := clockMeasure_univ_ne_zero hN
  kernel := hasEquivKernel_clock N
  bond := isBondWeight_villain hβ
  pair _ _ := isGinibrePair_villain hβ le_rfl
  pair_one _ _ := isGinibrePair_villain_one hβ

/-- **Villain-clock Theorem 7.1(1), finite volume.** The clock-constrained Villain correlation
bounds the continuous Villain correlation from below for every finite free-boundary domain. -/
theorem finite_correlation_dominates {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 0 < β)
    (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    (villainModel β hβ).twoPoint ξ Λ u v ≤ (model N hN β hβ).twoPoint ξ Λ u v := by
  exact FreeModel.twoPoint_le_of_pair (model N hN β hβ) (villainModel β hβ)
    (hasEquivKernel_clock_circle N) (fun _ _ => isGinibrePair_villain hβ le_rfl) ξ Λ u v

/-- **Villain-clock Theorem 7.1(1), thermodynamic limit.** -/
theorem limit_correlation_dominates {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 0 < β)
    (ξ : ℤ) (u v : ℤ × ℤ) :
    (villainModel β hβ).twoPointLimit ξ u v ≤ (model N hN β hβ).twoPointLimit ξ u v := by
  exact FreeModel.twoPointLimit_le_of_pair (model N hN β hβ) (villainModel β hβ)
    (hasEquivKernel_clock_circle N) (fun _ _ => isGinibrePair_villain hβ le_rfl) ξ u v

end FroehlichSpencer.BKT.Clock.VillainClock

end
