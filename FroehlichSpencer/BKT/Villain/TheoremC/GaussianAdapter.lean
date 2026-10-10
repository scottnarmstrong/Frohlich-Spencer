/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Villain.TheoremC.FiniteBound
public import FroehlichSpencer.BKT.Villain.TheoremC.GaussianCombLimit
public import FroehlichSpencer.BKT.Rotator.TheoremC.PinnedAdapter

/-! # Rooted Gaussian Villain integrals as pinned comb pairings -/

@[expose] public section

open Complex MeasureTheory
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.Villain
open FroehlichSpencer.BKT.Villain.TheoremC

noncomputable section

namespace FroehlichSpencer.BKT.Villain.TheoremC

/-- At angle `2πa`, the Gaussian Villain weight is the pinned Gaussian height density weight
when the Villain parameter is `4π² β`. -/
theorem gaussianVillainWeight_twoPi {β : ℝ} (_hβ : 0 < β) (a : ℝ) :
    gaussianVillainWeight (4 * Real.pi ^ 2 * β) (((2 * Real.pi * a : ℝ) : ℂ)) =
      gaussianWeight β⁻¹ (a : ℂ) := by
  rw [gaussianVillainWeight, gaussianWeight_ofReal, gaussianWeight_ofReal]
  congr 1
  field_simp [Real.pi_ne_zero, _hβ.ne']
  ring_nf

/-- The real-coordinate integrand obtained after removing the root phase from the Gaussian Villain
edge law. -/
def gaussianVillainPinnedCombIntegrand (L N : ℕ) (B : ℝ)
    (j : RotatorInternalBond L → ℤ) (y : SquareFreeVertex L → ℝ) : ℝ :=
  (∏ e, (gaussianVillainWeight B
      (((rotatorDualGraph L).grad (rotatorPinnedRealFieldOfCoords y).1 e +
        2 * Real.pi * (j e : ℝ) : ℝ) : ℂ)).re) *
    ∏ x, dirichletComb N (y x)

private theorem offsetEdgeDensity_gaussianVillain_pinnedComb_shear (L N : ℕ) (B : ℝ)
    (j : RotatorInternalBond L → ℤ) (φ : RotatorDualFace L → ℝ) :
    (fun ψ : RotatorDualFace L → ℝ =>
      Generic.offsetEdgeDensity (rotatorDualGraph L) (gaussianVillainWeight B)
        (fun e => 2 * Real.pi * (j e : ℝ)) none ψ *
      ∏ k, pinnedCombLam L N k (ψ k - ψ none))
      (Generic.shear none (rootShearVector L) φ) =
    (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ none) *
      gaussianVillainPinnedCombIntegrand L N B j (fun x => φ (some x)) := by
  simp only
  have hψ := shear_rootShearVector_apply L φ
  have hnone : Generic.shear none (rootShearVector L) φ none = φ none := by
    rw [hψ]
    simp [rotatorPinnedRealFieldOfCoords]
  have hgrad : ∀ e,
      (rotatorDualGraph L).grad (Generic.shear none (rootShearVector L) φ) e =
        (rotatorDualGraph L).grad
          (rotatorPinnedRealFieldOfCoords (fun x => φ (some x))).1 e := by
    intro e
    simp only [Multigraph.grad, hψ]
    ring
  have hcomb :
      ∏ k, pinnedCombLam L N k
        (Generic.shear none (rootShearVector L) φ k -
          Generic.shear none (rootShearVector L) φ none) =
        ∏ x, dirichletComb N (φ (some x)) := by
    rw [Fintype.prod_option]
    simp only [pinnedCombLam, Option.elim, one_mul, hψ]
    refine Finset.prod_congr rfl fun x _ => ?_
    simp [rotatorPinnedRealFieldOfCoords]
  unfold Generic.offsetEdgeDensity gaussianVillainPinnedCombIntegrand
  rw [hcomb, hnone]
  simp_rw [hgrad]
  ring

private theorem gaussianVillainPinnedCombIntegrand_smul {L N : ℕ} {β : ℝ}
    (hβ : 0 < β) (j : RotatorInternalBond L → ℤ) (y : SquareFreeVertex L → ℝ) :
    (((gaussianVillainPinnedCombIntegrand L N (4 * Real.pi ^ 2 * β) j
        ((2 * Real.pi) • y) : ℝ) : ℂ)) =
      faceCombCutoff (ι := SquareFreeVertex L) N y *
        villainPinnedGaussianDensityCoords L β j y := by
  have hgrad (e : RotatorInternalBond L) :
      (rotatorDualGraph L).grad
          (rotatorPinnedRealFieldOfCoords ((2 * Real.pi) • y)).1 e +
        2 * Real.pi * (j e : ℝ) =
      2 * Real.pi * (rotatorCoordsGradientLinearMap L y e + (j e : ℝ)) := by
    change (rotatorPinnedRealFieldOfCoords ((2 * Real.pi) • y)).1
          ((rotatorDualGraph L).src e) -
        (rotatorPinnedRealFieldOfCoords ((2 * Real.pi) • y)).1
          ((rotatorDualGraph L).tgt e) + 2 * Real.pi * (j e : ℝ) =
      2 * Real.pi * (rotatorPinnedCoordsField y ((rotatorDualGraph L).src e) -
        rotatorPinnedCoordsField y ((rotatorDualGraph L).tgt e) + (j e : ℝ))
    rw [rotatorPinnedRealFieldOfCoords_smul, rotatorPinnedRealFieldOfCoords_smul]
    simp [rotatorPinnedRealFieldOfCoords, rotatorPinnedCoordsField]
    ring
  let angle : RotatorInternalBond L → ℝ := fun e =>
    (rotatorDualGraph L).grad
        (rotatorPinnedRealFieldOfCoords ((2 * Real.pi) • y)).1 e +
      2 * Real.pi * (j e : ℝ)
  have hweight (e : RotatorInternalBond L) :
      gaussianVillainWeight (4 * Real.pi ^ 2 * β) ((angle e : ℂ)) =
        gaussianWeight β⁻¹
          ((rotatorCoordsGradientLinearMap L y e + (j e : ℝ) : ℝ) : ℂ) := by
    dsimp [angle]
    rw [hgrad, gaussianVillainWeight_twoPi hβ]
  have hdensity : villainPinnedGaussianDensityCoords L β j y =
      ((∏ e, (gaussianVillainWeight (4 * Real.pi ^ 2 * β)
          (angle e : ℂ)).re : ℝ) : ℂ) := by
    unfold villainPinnedGaussianDensityCoords
    rw [Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro e he
    rw [hweight e]
    simp only [gaussianWeight_ofReal, Complex.ofReal_re]
  unfold gaussianVillainPinnedCombIntegrand
  rw [faceCombCutoff_eq_prod, hdensity, Complex.ofReal_mul, Complex.ofReal_prod]
  conv_rhs => rw [mul_comm]
  congr 1

/-- The Gaussian Villain rooted comb integral is the real part of the pinned Gaussian pairing. -/
theorem integral_offsetEdgeDensity_villainGaussianPinnedComb {L : ℕ} (N : ℕ)
    {β : ℝ} (hβ : 0 < β) (j : RotatorInternalBond L → ℤ) :
    ∫ φ : RotatorDualFace L → ℝ,
      Generic.offsetEdgeDensity (rotatorDualGraph L) (gaussianVillainWeight (4 * Real.pi ^ 2 * β))
        (fun e => 2 * Real.pi * (j e : ℝ)) none φ *
      ∏ k, pinnedCombLam L N k (φ k - φ none) =
      (2 * Real.pi) ^ (Fintype.card (SquareFreeVertex L) + 1) *
        (villainPinnedGaussianCombCutoffPairing L β j N).re := by
  have hu : rootShearVector L none = 0 := rfl
  rw [← Generic.integral_comp_shear hu]
  simp_rw [offsetEdgeDensity_gaussianVillain_pinnedComb_shear]
  rw [integral_option_mul (SquareFreeVertex L) _
      (gaussianVillainPinnedCombIntegrand L N (4 * Real.pi ^ 2 * β) j),
    integral_indicator_Ico_pi]
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsmul := Measure.integral_comp_smul
    (volume : Measure (SquareFreeVertex L → ℝ))
    (gaussianVillainPinnedCombIntegrand L N (4 * Real.pi ^ 2 * β) j) (2 * Real.pi)
  rw [Module.finrank_fintype_fun_eq_card, abs_of_pos (inv_pos.mpr (pow_pos h2π _)),
    smul_eq_mul] at hsmul
  have hscale :
      ∫ y, gaussianVillainPinnedCombIntegrand L N (4 * Real.pi ^ 2 * β) j y =
        (2 * Real.pi) ^ Fintype.card (SquareFreeVertex L) *
          ∫ y, gaussianVillainPinnedCombIntegrand L N (4 * Real.pi ^ 2 * β) j
            ((2 * Real.pi) • y) := by
    rw [hsmul, ← mul_assoc, mul_inv_cancel₀ (pow_pos h2π _).ne', one_mul]
  have hpair :
      (villainPinnedGaussianCombCutoffPairing L β j N).re =
        ∫ y, gaussianVillainPinnedCombIntegrand L N (4 * Real.pi ^ 2 * β) j
          ((2 * Real.pi) • y) := by
    have hc : villainPinnedGaussianCombCutoffPairing L β j N =
        ∫ y, (gaussianVillainPinnedCombIntegrand L N (4 * Real.pi ^ 2 * β) j
          ((2 * Real.pi) • y) : ℂ) := by
      unfold villainPinnedGaussianCombCutoffPairing
      apply integral_congr_ae
      filter_upwards [] with y
      exact (gaussianVillainPinnedCombIntegrand_smul hβ j y).symm
    have hr := congrArg Complex.re hc
    rw [integral_complex_ofReal, Complex.ofReal_re] at hr
    exact hr
  rw [hscale, hpair, pow_succ]
  ring

/-- The unmarked Gaussian Villain edge integral on `squareZero` is the real part of the unmarked
pinned Gaussian pairing. -/
theorem integral_edgeDensity_villainGaussianPinnedComb {L : ℕ} (N : ℕ)
    {β : ℝ} (hβ : 0 < β) {W : ℝ} {c : ℝ → ℝ}
    (hw : IsStripWeight (gaussianVillainWeight (4 * Real.pi ^ 2 * β)) W c) :
    ∫ φ : RotatorDualFace L → ℝ,
      edgeDensity (squareZero L) (gaussianVillainWeight (4 * Real.pi ^ 2 * β)) none φ *
        ∏ k, pinnedCombLam L N k (φ k - φ none) =
      (2 * Real.pi) ^ (Fintype.card (SquareFreeVertex L) + 1) *
        (villainPinnedGaussianCombCutoffPairing L β (fun _ => 0) N).re := by
  rw [← integral_offsetEdgeDensity_villainGaussianPinnedComb N hβ (fun _ => 0)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  have hzero : (fun e : RotatorInternalBond L =>
      2 * Real.pi * (((fun _ => (0 : ℤ)) e : ℤ) : ℝ)) = 0 := by
    funext e
    simp
  simp only [hzero, offsetEdgeDensity_zero, edgeDensity_squareZero hw]

/-- Translation of the rooted field absorbs the harmonic correction in the Gaussian Villain
integral; the resulting integral is the marked pinned Gaussian comb pairing. -/
theorem integral_offsetEdgeDensity_villainGaussianPinnedComb_shift {L : ℕ} (N : ℕ)
    {β : ℝ} (hβ : 0 < β) {W : ℝ} {c : ℝ → ℝ}
    (hw : IsStripWeight (gaussianVillainWeight (4 * Real.pi ^ 2 * β)) W c)
    (j : RotatorInternalBond L → ℤ) (σ : RotatorDualFace L → ℝ) (hσ : σ none = 0) :
    ∫ φ : RotatorDualFace L → ℝ,
      offsetEdgeDensity (squareZero L) (gaussianVillainWeight (4 * Real.pi ^ 2 * β))
        (squareZeroField L fun e =>
          2 * Real.pi * (j e : ℝ) + (rotatorDualGraph L).grad σ e) none φ *
        ∏ k, pinnedCombLam L N k (φ k + σ k - (φ none + σ none)) =
      (2 * Real.pi) ^ (Fintype.card (SquareFreeVertex L) + 1) *
        (villainPinnedGaussianCombCutoffPairing L β j N).re := by
  rw [← integral_offsetEdgeDensity_villainGaussianPinnedComb N hβ j,
    ← integral_sub_right_eq_self _ σ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  have hsplit :
      (squareZeroField L fun e => 2 * Real.pi * (j e : ℝ) +
          (rotatorDualGraph L).grad σ e) =
        squareZeroField L (fun e => 2 * Real.pi * (j e : ℝ)) +
          fun e => (squareZero L).grad σ e := by
    rw [← squareZeroField_grad, ← squareZeroField_add]
    rfl
  have hprod :
      ∏ k, pinnedCombLam L N k ((φ - σ) k + σ k - ((φ - σ) none + σ none)) =
        ∏ k, pinnedCombLam L N k (φ k - φ none) := by
    refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    simp only [Pi.sub_apply]
    ring
  beta_reduce
  rw [hprod, hsplit, ← offsetEdgeDensity_squareZeroField hw L
    (fun e => 2 * Real.pi * (j e : ℝ))]
  congr 1
  unfold offsetEdgeDensity
  congr 1
  · refine Finset.prod_congr rfl fun e _ => ?_
    congr 3
    simp only [Multigraph.grad, Pi.sub_apply, Pi.add_apply]
    ring
  · simp only [Pi.sub_apply, hσ, sub_zero]

end FroehlichSpencer.BKT.Villain.TheoremC

end
