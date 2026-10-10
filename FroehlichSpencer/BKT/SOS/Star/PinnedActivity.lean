/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Rooted.LayerD
public import FroehlichSpencer.BKT.Rotator.Contour.Factor
public import FroehlichSpencer.BKT.Rotator.FreeBox
public import FroehlichSpencer.BKT.Rotator.TheoremC.MainD
public import FroehlichSpencer.BKT.SOS.Star.ActivityRate

/-!
# SOS activity on the pinned Appendix-D carrier

The SOS zero-mass reference measure is exhausted by fields pinned to zero outside a finite volume.
After the 2π change of variables, the finite comb is the root-relative comb on the augmented
Appendix-D carrier. The generic rooted layer is independent of the bond weight, so its activity
estimate can use the SOS interpolation cost. This module records that transfer without identifying
the SOS carrier with a KP free or periodic square.

The scale-choice hypotheses below are the numerical inequalities needed by the generic cost
envelope theorem. They are deliberately visible: the KP-square rate theorem alone does not prove
that the Appendix-D selection has a rooted layer.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Star

open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.PinnedCharges
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Contour
open FroehlichSpencer.BKT.Rotator.TheoremC

/-- The numerical scale data needed to run the generic rooted-layer activity theorem with the SOS
strip cost. Here T is log (1 / β), and rate is the logarithmic activity exponent. -/
structure SOSPinnedScaleChoice (T D₁ D₂ K₀ K₁ a₁ a₂ : ℝ) where
  amp : ℝ
  k₀ : ℕ
  amp_nonneg : 0 ≤ amp
  width : amp * K₁ ≤ Real.pi * Real.exp (T / 3)
  k₀_pos : 1 ≤ k₀
  exponential_cost :
    100 * 4 ^ k₀ * costMajorant (interpolationCostConstant * Real.exp (-2 * T / 3))
      (interpolationCostConstant * Real.exp (-2 * T / 3)) (amp * K₁) ≤ amp / 2
  quadratic_base :
    amp ≤ 1 / (2 * (interpolationCostConstant * Real.exp (-2 * T / 3)) * K₀)
  quadratic_scales :
    amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4 : ℝ) * k₀) / K₁
  rate_mass :
    T / (448000 * max 1 D₁) ≤ amp / 8 - a₁
  rate_area :
    T / (448000 * max 1 D₁) ≤ amp / (8 * D₁) - D₂ - a₂

/-- **Transfer to a pinned SOS rooted layer.** If an Appendix-D rooted layer is available and the
SOS logarithmic scale inequalities hold, its renormalized activities have the same logarithmic
decay in charge mass and layer area that the square SOS estimate obtained on KP squares. The endpoint field is not
part of this theorem; its source-profile control is the remaining input to the endpoint sum. -/
theorem sos_pinned_activity_rate
    {L N : ℕ} {D₁ D₂ α K₀ K₁ Kv a₁ a₂ : ℝ} {Kov : ℕ}
    {T : ℝ} (hT : 0 < T)
    (hscale : SOSPinnedScaleChoice T D₁ D₂ K₀ K₁ a₁ a₂)
    (hD₁ : 0 < D₁) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁)
    (hα : α = 7 / 4)
    (Wit : PinnedLayerWitnessD L N D₁ D₂ α K₀ K₁ Kv a₁ a₂ Kov)
    (i : Fin Wit.layer.n) (ρ : RotatorDualFace L → ℤ) (hρ : ρ ∈ Wit.layer.N i) :
    |rootedActivityD Wit.layer (fun u =>
        Real.exp (-2 * T / 3) * cEnvelope interpolationCostConstant
          (u / (2 * Real.pi)))
        (interpolationCostConstant * Real.exp (-2 * T / 3)) hscale.amp hscale.k₀ i ρ|
      ≤ Real.exp (-(T / (448000 * max 1 D₁)) *
          (∑ j, |(ρ j : ℝ)| + Wit.A ρ)) := by
  have hβ : 0 < Real.exp (-T) := Real.exp_pos _
  have hC0 : 0 < interpolationCostConstant := by
    unfold interpolationCostConstant
    have h := (Classical.choose_spec exists_isStripWeight_sosInterp).1
    linarith
  have hκ : 0 < interpolationCostConstant * Real.exp (-2 * T / 3) :=
    mul_pos hC0 (Real.exp_pos _)
  have hcost : IsCostEnvelope
      (fun u => Real.exp (-2 * T / 3) *
        cEnvelope interpolationCostConstant (u / (2 * Real.pi)))
      (interpolationCostConstant * Real.exp (-2 * T / 3))
      (interpolationCostConstant * Real.exp (-2 * T / 3))
      (Real.pi * Real.exp (T / 3)) := by
    have h := sosScaled_costEnvelope (β := Real.exp (-T)) hβ.le
      (Real.pi * Real.exp (T / 3))
    have hpow1 : Real.exp (-T) ^ (2 / 3 : ℝ) = Real.exp (-2 * T / 3) := by
      rw [← Real.exp_mul]
      ring_nf
    rw [hpow1] at h
    simpa [interpolationCostConstant, mul_comm, mul_left_comm, mul_assoc] using h
  have hW1 : 1 ≤ Real.pi * Real.exp (T / 3) := by
    have hpi : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
    have hexp : 1 ≤ Real.exp (T / 3) := Real.one_le_exp (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hpi) (sub_nonneg.mpr hexp)]
  have hZ : ∀ ϱ : RotatorDualFace L → ℤ,
      Wit.Zent ϱ ≤ Real.exp (a₁ * ∑ j, |(ϱ j : ℝ)| + a₂ * Wit.A ϱ) :=
    Wit.entropy_exp
  have hrate_nonneg : 0 ≤ T / (448000 * max 1 D₁) := by positivity
  have hquadScales : hscale.amp ≤ (2 : ℝ) ^ (gradExponent α * hscale.k₀) / K₁ := by
    simpa [hα] using hscale.quadratic_scales
  have h := abs_rootedActivityD_le Wit.layer hcost hκ hK₀ hK₁ hD₁
    hscale.amp_nonneg hscale.width hscale.k₀_pos hscale.exponential_cost
    hscale.quadratic_base hquadScales hZ hrate_nonneg
    hscale.rate_mass hscale.rate_area i ρ hρ
    (ℓ := Wit.A ρ) (by
      have hd : (1 : ℝ) ≤ (Wit.dsc ρ : ℝ) := by
        exact_mod_cast Wit.isLocal.one_le_dsc i ρ hρ
      have hdarg : (1 : ℝ) ≤ (Wit.dsc ρ : ℝ) + 1 := by linarith
      exact le_trans (Real.logb_nonneg (by norm_num) hdarg)
        (Wit.isLocal.cover i ρ hρ)) le_rfl
  simpa using h

/-- The source model uses a zero-exterior exhaustion. This is the pinned-carrier convention used
by PinnedLayerWitnessD; a KP free or periodic square hypothesis does not provide this datum. -/
abbrev SOSPinnedCarrierHypothesis : Prop := PinnedLayerHypothesisD

end FroehlichSpencer.BKT.SOS.Star

end
