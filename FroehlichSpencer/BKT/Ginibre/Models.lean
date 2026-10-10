/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Ginibre.FreeLattice
public import FroehlichSpencer.BKT.Ginibre.VillainPair
public import FroehlichSpencer.BKT.Bridge.VillainMeasure
public import FroehlichSpencer.BKT.Villain.CosineExpectation

/-!
# The plane rotator, the `ℤ_N` clock and the Villain model with free boundary conditions

Three instances of `FreeModel`:

For each, Ginibre I/II, domain monotonicity and the free thermodynamic two-point limit follow from
`FreeModel`.

In addition: all three are nondecreasing in `β`, and the clock two-point function
dominates the rotator one at the same `β` in every finite domain and in the limit (FS81 Theorem
7.1(1), J p. 585).
-/

@[expose] public section

open MeasureTheory
open FroehlichSpencer.BKT.Rotator.Ginibre
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Ginibre

theorem circleMeasure_univ_ne_zero : circleMeasure Set.univ ≠ 0 := by
  rw [circleMeasure_univ, Ne, ENNReal.ofReal_eq_zero, not_le]
  positivity

theorem clockMeasure_univ_ne_zero {N : ℕ} (hN : 0 < N) : clockMeasure N Set.univ ≠ 0 := by
  rw [clockMeasure_univ]
  exact_mod_cast hN.ne'

theorem isBondWeight_villain {β : ℝ} (hβ : 0 < β) : IsBondWeight (villainWeight β) :=
  ⟨Villain.continuous_villainWeight β hβ, VillainWeight.villainWeight_pos hβ,
    ⟨_, villainWeight_fourier_bound β hβ⟩⟩

/-- The free-boundary plane rotator at inverse temperature `β ≥ 0`. -/
def rotatorModel (β : ℝ) (hβ : 0 ≤ β) : FreeModel where
  ν := circleMeasure
  lam := circleFourier
  w := expCosWeight β
  isFinite := inferInstance
  fourier := hasRealFourier_circle
  mass_ne_zero := circleMeasure_univ_ne_zero
  kernel := hasEquivKernel_circle
  bond := isBondWeight_expCos β
  pair _ _ := isGinibrePair_expCos hβ le_rfl
  pair_one _ _ := isGinibrePair_expCos_one hβ

/-- The free-boundary `ℤ_N` clock model at inverse temperature `β ≥ 0`, FS81 (7.1). -/
def clockModel (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 ≤ β) : FreeModel where
  ν := clockMeasure N
  lam := clockFourier N
  w := expCosWeight β
  isFinite := inferInstance
  fourier := hasRealFourier_clock hN
  mass_ne_zero := clockMeasure_univ_ne_zero hN
  kernel := hasEquivKernel_clock N
  bond := isBondWeight_expCos β
  pair _ _ := isGinibrePair_expCos hβ le_rfl
  pair_one _ _ := isGinibrePair_expCos_one hβ

/-- The free-boundary Villain model at inverse temperature `β > 0`. -/
def villainModel (β : ℝ) (hβ : 0 < β) : FreeModel where
  ν := circleMeasure
  lam := circleFourier
  w := villainWeight β
  isFinite := inferInstance
  fourier := hasRealFourier_circle
  mass_ne_zero := circleMeasure_univ_ne_zero
  kernel := hasEquivKernel_circle
  bond := isBondWeight_villain hβ
  pair _ _ := isGinibrePair_villain hβ le_rfl
  pair_one _ _ := isGinibrePair_villain_one hβ


theorem rotatorModel_pairWeight (β : ℝ) (hβ : 0 ≤ β) (Λ : Finset (ℤ × ℤ)) :
    pairWeight (bondFrequency Λ) ((rotatorModel β hβ).bondWeight Λ) =
      cosineWeight (bondFrequency Λ) (freeCoupling β Λ) := by
  funext θ
  rw [pairWeight, cosineWeight, cosineEnergy, Real.exp_sum]
  refine Finset.prod_congr rfl fun b _ => ?_
  simp only [FreeModel.bondWeight, freeCoupling, rotatorModel]
  split_ifs
  · rfl
  · simp

theorem rotatorModel_gibbs (β : ℝ) (hβ : 0 ≤ β) (Λ : Finset (ℤ × ℤ)) :
    (rotatorModel β hβ).gibbs Λ = freeRotatorMeasure β Λ := by
  rw [FreeModel.gibbs, pairGibbs, freeRotatorMeasure, cosineGibbs, pairPartition, cosinePartition,
    rotatorModel_pairWeight]
  rfl

theorem rotatorModel_twoPoint (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    (rotatorModel β hβ).twoPoint ξ Λ u v = freeTwoPoint β ξ Λ u v := by
  rw [FreeModel.twoPoint, freeTwoPoint, rotatorModel_gibbs]

theorem rotatorModel_twoPointLimit (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ) (u v : ℤ × ℤ) :
    (rotatorModel β hβ).twoPointLimit ξ u v = freeTwoPointLimit β hβ ξ u v := by
  have h := (rotatorModel β hβ).tendsto_twoPointLimit ξ u v
  simp only [rotatorModel_twoPoint] at h
  exact tendsto_nhds_unique h (tendsto_freeTwoPointLimit hβ ξ u v)

/-! ### Clock versus rotator, FS81 Theorem 7.1 (1) -/

/-- **FS81 Theorem 7.1 (1), finite volume.** At the same `β ≥ 0` the `ℤ_N` clock two-point
function dominates the plane-rotator one in every finite domain with free boundary conditions. -/
theorem freeTwoPoint_le_clock (N : ℕ) (hN : 0 < N) {β : ℝ} (hβ : 0 ≤ β) (ξ : ℤ)
    (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    freeTwoPoint β ξ Λ u v ≤ (clockModel N hN β hβ).twoPoint ξ Λ u v := by
  rw [← rotatorModel_twoPoint β hβ]
  exact FreeModel.twoPoint_le_of_pair (clockModel N hN β hβ) (rotatorModel β hβ)
    (hasEquivKernel_clock_circle N) (fun _ _ => isGinibrePair_expCos hβ le_rfl) ξ Λ u v

/-- **FS81 Theorem 7.1 (1), infinite volume.** -/
theorem freeTwoPointLimit_le_clock (N : ℕ) (hN : 0 < N) {β : ℝ} (hβ : 0 ≤ β) (ξ : ℤ)
    (u v : ℤ × ℤ) :
    freeTwoPointLimit β hβ ξ u v ≤ (clockModel N hN β hβ).twoPointLimit ξ u v := by
  rw [← rotatorModel_twoPointLimit β hβ]
  exact FreeModel.twoPointLimit_le_of_pair (clockModel N hN β hβ) (rotatorModel β hβ)
    (hasEquivKernel_clock_circle N) (fun _ _ => isGinibrePair_expCos hβ le_rfl) ξ u v

/-! ### Monotonicity in the inverse temperature -/

theorem clockModel_twoPoint_mono (N : ℕ) (hN : 0 < N) {β β' : ℝ} (hβ : 0 ≤ β) (hββ' : β ≤ β')
    (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    (clockModel N hN β hβ).twoPoint ξ Λ u v ≤
      (clockModel N hN β' (hβ.trans hββ')).twoPoint ξ Λ u v :=
  FreeModel.twoPoint_le_of_pair _ _ (hasEquivKernel_clock N)
    (fun _ _ => isGinibrePair_expCos hβ hββ') ξ Λ u v

theorem clockModel_twoPointLimit_mono (N : ℕ) (hN : 0 < N) {β β' : ℝ} (hβ : 0 ≤ β)
    (hββ' : β ≤ β') (ξ : ℤ) (u v : ℤ × ℤ) :
    (clockModel N hN β hβ).twoPointLimit ξ u v ≤
      (clockModel N hN β' (hβ.trans hββ')).twoPointLimit ξ u v :=
  FreeModel.twoPointLimit_le_of_pair _ _ (hasEquivKernel_clock N)
    (fun _ _ => isGinibrePair_expCos hβ hββ') ξ u v

/-- The Villain two-point function is nondecreasing in `β`. -/
theorem villainModel_twoPoint_mono {β β' : ℝ} (hβ : 0 < β) (hββ' : β ≤ β') (ξ : ℤ)
    (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    (villainModel β hβ).twoPoint ξ Λ u v ≤
      (villainModel β' (hβ.trans_le hββ')).twoPoint ξ Λ u v :=
  FreeModel.twoPoint_le_of_pair _ _ hasEquivKernel_circle
    (fun _ _ => isGinibrePair_villain hβ hββ') ξ Λ u v

theorem villainModel_twoPointLimit_mono {β β' : ℝ} (hβ : 0 < β) (hββ' : β ≤ β') (ξ : ℤ)
    (u v : ℤ × ℤ) :
    (villainModel β hβ).twoPointLimit ξ u v ≤
      (villainModel β' (hβ.trans_le hββ')).twoPointLimit ξ u v :=
  FreeModel.twoPointLimit_le_of_pair _ _ hasEquivKernel_circle
    (fun _ _ => isGinibrePair_villain hβ hββ') ξ u v

end FroehlichSpencer.BKT.Ginibre

end
