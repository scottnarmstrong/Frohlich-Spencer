/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.Layer
public import FroehlichSpencer.BKT.SOS.Literal.CombLimit
public import FroehlichSpencer.BKT.SOS.Roughening.Comb

/-!
# The rooted comb integral of the comb on a region (the finite comb construction)

The tilted rooted law of the angle variable `ψ = 2πh` on `squareZero L` with the root-relative
observable `combOnLam L N A` (`D_N` on `A`, `D_N(N·)` off `A`, `1` at the root) integrates to
`(2π)^{L²+1}` times the mixed comb pairing of the tilted height density
(`integral_tiltDensity_combOnLam`): the shear of the root phase, the root integral `2π` and the
rescaling by `2π`, exactly as `Roughening.integral_tiltDensity_pinnedComb` for the comb on every
face.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory Complex
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.PinnedCharges (SquareZeroBond Site)
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.SOS.Tilt
open FroehlichSpencer.BKT.SOS.Roughening

variable {L : ℕ}

/-- The bounded-coordinate integrand of the tilted rooted integral of the comb on `A`. -/
def combOnIntegrand (L N : ℕ) (A : Finset (Site L)) (β : ℝ) (bt : SquareZeroBond L → ℝ)
    (y : Site L → ℝ) : ℝ :=
  Real.exp (tiltExponent (gradLinear (squareZero L)) bt (pinnedField y)) *
    (∏ e, (sosWeightψ β (((squareZero L).grad (pinnedField y) e : ℝ) : ℂ)).re) *
      ∏ x, dirichletComb N ((combMult A N x : ℝ) * y x)

theorem tiltDensity_combOnLam_shear (L N : ℕ) (A : Finset (Site L)) (β : ℝ)
    (bt : SquareZeroBond L → ℝ) (φ : RotatorDualFace L → ℝ) :
    (fun ψ : RotatorDualFace L → ℝ => tiltDensity (squareZero L) (sosWeightψ β) 0 bt none ψ *
        ∏ k, combOnLam L N A k (ψ k - ψ none)) (Generic.shear none (rootShearVector L) φ) =
      (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ none) *
        combOnIntegrand L N A β bt (fun x => φ (some x)) := by
  simp only
  have hψ := shear_root_apply φ
  have hnone : Generic.shear none (rootShearVector L) φ none = φ none := by
    rw [hψ]; simp [pinnedField]
  have hgrad : ∀ e, (squareZero L).grad (Generic.shear none (rootShearVector L) φ) e =
      (squareZero L).grad (pinnedField (fun x => φ (some x))) e := by
    intro e
    simp only [Multigraph.grad, hψ]
    ring
  have htilt : tiltExponent (gradLinear (squareZero L)) bt
      (Generic.shear none (rootShearVector L) φ) =
      tiltExponent (gradLinear (squareZero L)) bt (pinnedField (fun x => φ (some x))) := by
    unfold tiltExponent
    simp only [gradLinear_apply, hgrad]
  have hcomb : ∏ k, combOnLam L N A k (Generic.shear none (rootShearVector L) φ k -
      Generic.shear none (rootShearVector L) φ none) =
      ∏ x, dirichletComb N ((combMult A N x : ℝ) * φ (some x)) := by
    rw [Fintype.prod_option]
    simp only [combOnLam, Option.elim, one_mul, hψ]
    refine Finset.prod_congr rfl fun x _ => ?_
    simp [pinnedField]
  unfold tiltDensity offsetEdgeDensity combOnIntegrand
  rw [hcomb, hnone, htilt]
  simp_rw [hgrad]
  simp only [Pi.zero_apply, add_zero]
  ring

theorem combOnIntegrand_smul (L N : ℕ) (A : Finset (Site L)) {β : ℝ} (hβ : 0 ≤ β)
    (bt : SquareZeroBond L → ℝ) (y : Site L → ℝ) :
    ((combOnIntegrand L N A β bt ((2 * Real.pi) • y) : ℝ) : ℂ) =
      mixedComb A N y * sosDensityCoords L β (fun e => 2 * Real.pi * bt e) y := by
  have hreal : ∀ a : ℝ, (((Interp.sosInterp β (a : ℂ)).re : ℝ) : ℂ) =
      Interp.sosInterp β (a : ℂ) :=
    fun a => Complex.ext rfl (by simp [(Interp.sosInterp_ofReal_im_eq_zero_and_re_pos hβ a).1])
  have hgrad2 : ∀ e, (squareZero L).grad (pinnedField ((2 * Real.pi) • y)) e =
      2 * Real.pi * pinnedGrad L y e := fun e => by
    rw [pinnedGrad_apply]
    simp only [Multigraph.grad, pinnedField_smul]
    ring
  have hedge : ∀ e, (sosWeightψ β (((squareZero L).grad (pinnedField ((2 * Real.pi) • y)) e :
      ℝ) : ℂ)).re = (Interp.sosInterp β (pinnedGrad L y e : ℂ)).re := fun e => by
    rw [hgrad2, sosWeightψ_two_pi_mul]
  have htilt : tiltExponent (gradLinear (squareZero L)) bt (pinnedField ((2 * Real.pi) • y)) =
      ∑ e, 2 * Real.pi * bt e * pinnedGrad L y e := by
    unfold tiltExponent
    simp only [gradLinear_apply, hgrad2]
    exact Finset.sum_congr rfl fun e _ => by ring
  have hD : sosDensityCoords L β (fun e => 2 * Real.pi * bt e) y =
      ((Real.exp (∑ e, 2 * Real.pi * bt e * pinnedGrad L y e) *
        ∏ e, (Interp.sosInterp β (pinnedGrad L y e : ℂ)).re : ℝ) : ℂ) := by
    unfold sosDensityCoords sosTiltFactor
    rw [Real.exp_sum, ← Finset.prod_mul_distrib, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [Complex.ofReal_mul (Real.exp _), hreal, Complex.ofReal_exp]
    push_cast
    ring_nf
  have hM : mixedComb A N y =
      ((∏ x, dirichletComb N ((combMult A N x : ℝ) * ((2 * Real.pi) • y) x) : ℝ) : ℂ) := by
    unfold mixedComb
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun x _ => ?_
    congr 2
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hM, hD, ← Complex.ofReal_mul]
  congr 1
  unfold combOnIntegrand
  simp_rw [hedge, htilt]
  ring

/-- **The tilted rooted integral of the comb on `A` is the mixed comb pairing** of the tilted
height density. -/
theorem integral_tiltDensity_combOnLam (N : ℕ) (A : Finset (Site L)) {β : ℝ} (hβ : 0 ≤ β)
    (bt : SquareZeroBond L → ℝ) :
    ∫ φ : RotatorDualFace L → ℝ,
        tiltDensity (squareZero L) (sosWeightψ β) 0 bt none φ *
          ∏ k, combOnLam L N A k (φ k - φ none) =
      (2 * Real.pi) ^ (Fintype.card (Site L) + 1) *
        (∫ y, mixedComb A N y * sosDensityCoords L β (fun e => 2 * Real.pi * bt e) y).re := by
  have hu : rootShearVector L none = 0 := rfl
  rw [← Generic.integral_comp_shear hu]
  simp_rw [tiltDensity_combOnLam_shear]
  rw [integral_option_mul (Site L) _ (combOnIntegrand L N A β bt), integral_indicator_Ico_pi]
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsmul := Measure.integral_comp_smul (volume : Measure (Site L → ℝ))
    (combOnIntegrand L N A β bt) (2 * Real.pi)
  rw [Module.finrank_fintype_fun_eq_card, abs_of_pos (inv_pos.mpr (pow_pos h2π _)),
    smul_eq_mul] at hsmul
  have hscale : ∫ y, combOnIntegrand L N A β bt y =
      (2 * Real.pi) ^ Fintype.card (Site L) *
        ∫ y, combOnIntegrand L N A β bt ((2 * Real.pi) • y) := by
    rw [hsmul, ← mul_assoc, mul_inv_cancel₀ (pow_pos h2π _).ne', one_mul]
  have hpair : (∫ y, mixedComb A N y *
      sosDensityCoords L β (fun e => 2 * Real.pi * bt e) y).re =
      ∫ y, combOnIntegrand L N A β bt ((2 * Real.pi) • y) := by
    simp_rw [← combOnIntegrand_smul L N A hβ bt]
    rw [integral_complex_ofReal, Complex.ofReal_re]
  rw [hscale, hpair, pow_succ]
  ring

end FroehlichSpencer.BKT.SOS.Literal

end
