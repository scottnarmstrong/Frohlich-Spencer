/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Layer.Scale
public import FroehlichSpencer.BKT.SOS.Star.PinnedActivity
public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileA3CertTerminal

/-!
# The pinned SOS carrier and its uniform activity rate from the single lemma (the SOS activity estimate)

The comb charge layer is independent of the bond weight, and the SOS weight enters only through
its strip cost.

The amplitude is
  `amp = T/(8πK₁)` and the cutoff `k₀ = ⌈log₂T/γ⌉ + 1` (`exists_sosScaleChoice`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.PinnedCharges
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Contour
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.SOS.Star

/-! ## The carrier from the single lemma -/

/-- **The pinned SOS carrier from the support control.** -/
theorem sosPinnedCarrierHypothesis_of_collapsedSupportControl
    (h : TerminalCollapsedSupportControl) : SOSPinnedCarrierHypothesis :=
  pinnedLayerHypothesisD_of_terminalWavesW
    (Real.log_nonneg (by norm_num)) (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))
    combCoefficientBound (α := 7 / 4) (by norm_num) (lt_max_of_lt_left (by norm_num))
    (lt_max_of_lt_left (by norm_num)) (by norm_num : (0 : ℝ) < 1 / 3) routineKv_nonneg
    (pinnedTerminalWavesW_of_profilesW (by norm_num) (pinnedTerminalProfilesW_of_split
      (pinnedTerminalProfilesG_of_supportControl (by norm_num)
        (terminalSupportControl_of_collapsed h)) badSelectedBound_proof))

/-- **The pinned SOS carrier from the rooted component decomposition.** -/
theorem sosPinnedCarrierHypothesis_of_rootedComponents
    (h : TerminalProfileA3RootedComponentsLarge) : SOSPinnedCarrierHypothesis :=
  sosPinnedCarrierHypothesis_of_collapsedSupportControl (terminalCollapsedSupportControl_of_large
    (terminalCollapsedSupportControlLarge_of_rootedComponents h))

/-! ## The SOS cost at `β = e^{−T}` -/

/-- The angle-scaled SOS interpolation cost at `β = e^{−T}`. -/
def sosCost (T : ℝ) : ℝ → ℝ := fun u =>
  Real.exp (-2 * T / 3) * cEnvelope interpolationCostConstant (u / (2 * Real.pi))

/-- Its envelope coefficient `κ = C e^{−2T/3}`. -/
def sosKappa (T : ℝ) : ℝ := interpolationCostConstant * Real.exp (-2 * T / 3)

/-- The amplitude `T/(8πK₁)`. -/
def sosAmp (K₁ T : ℝ) : ℝ := T / (8 * Real.pi * K₁)

theorem interpolationCostConstant_pos : 0 < interpolationCostConstant := by
  unfold interpolationCostConstant
  have h := (Classical.choose_spec exists_isStripWeight_sosInterp).1
  linarith

theorem sosCost_isCostEnvelope (T W : ℝ) :
    IsCostEnvelope (sosCost T) (sosKappa T) (sosKappa T) W := by
  have h := sosScaled_costEnvelope (β := Real.exp (-T)) (Real.exp_pos _).le W
  have hpow : Real.exp (-T) ^ (2 / 3 : ℝ) = Real.exp (-2 * T / 3) := by
    rw [← Real.exp_mul]; ring_nf
  rw [hpow] at h
  have hc : sosCost T = fun u =>
      Real.exp (-2 * T / 3) * cEnvelope interpolationCostConstant (u / (2 * Real.pi)) := rfl
  rw [hc]
  simpa [sosKappa, mul_comm] using h

/-! ## The uniform activity rate -/

/-- **The uniform logarithmic SOS activity rate on any pinned carrier.** -/
theorem sos_uniform_activity_rate (hyp : SOSPinnedCarrierHypothesis) :
    ∃ (D₁ D₂ α K₀ K₁ Kv a₁ a₂ : ℝ) (Kov L₀ : ℕ) (r T₀ : ℝ), 0 < r ∧ 1 ≤ T₀ ∧
      ∀ T, T₀ ≤ T → ∀ L, L₀ ≤ L → ∀ N, 1 ≤ N →
        ∃ Wit : PinnedLayerWitnessD L N D₁ D₂ α K₀ K₁ Kv a₁ a₂ Kov,
          ∀ i (ρ : RotatorDualFace L → ℤ), ρ ∈ Wit.layer.N i →
            |rootedActivityD Wit.layer (sosCost T) (sosKappa T) (sosAmp K₁ T)
                (sosCutoff (gradExponent α) T) i ρ| ≤
              Real.exp (-(r * T) * (∑ j, |(ρ j : ℝ)| + Wit.A ρ)) := by
  obtain ⟨D₁, D₂, α, K₀, K₁, Kv, a₁, a₂, Kov, L₀, hα, hK₀, hK₁, hD₁, -, hwit⟩ := hyp
  obtain ⟨r, T₀, hr, hT₀, hscale⟩ := exists_sosScaleChoice (D₂ := D₂) (a₁ := a₁) (a₂ := a₂) hα
    hD₁ hK₀ hK₁ interpolationCostConstant_pos
  refine ⟨D₁, D₂, α, K₀, K₁, Kv, a₁, a₂, Kov, L₀, r, T₀, hr, hT₀,
    fun T hT L hL N hN => ?_⟩
  obtain ⟨hamp, hampW, hk₀, hexp, hquad₁, hquad₂, hb0, hb₁, hb₂⟩ := hscale T hT
  obtain ⟨Wit⟩ := hwit L hL N hN
  refine ⟨Wit, fun i ρ hρ => ?_⟩
  have hκ : 0 < sosKappa T := mul_pos interpolationCostConstant_pos (Real.exp_pos _)
  have hA0 : 0 ≤ Wit.A ρ := by
    have hd : (1 : ℝ) ≤ (Wit.dsc ρ : ℝ) := by exact_mod_cast Wit.isLocal.one_le_dsc i ρ hρ
    exact le_trans (Real.logb_nonneg (by norm_num) (by linarith)) (Wit.isLocal.cover i ρ hρ)
  exact abs_rootedActivityD_le Wit.layer (sosCost_isCostEnvelope T _) hκ hK₀ hK₁ hD₁ hamp hampW
    hk₀ hexp hquad₁ hquad₂ Wit.entropy_exp hb0 hb₁ hb₂ i ρ hρ hA0 le_rfl

/-- **The uniform SOS activity rate from the single lemma.** -/
theorem sos_uniform_activity_rate_of_rootedComponents
    (h : TerminalProfileA3RootedComponentsLarge) :
    ∃ (D₁ D₂ α K₀ K₁ Kv a₁ a₂ : ℝ) (Kov L₀ : ℕ) (r T₀ : ℝ), 0 < r ∧ 1 ≤ T₀ ∧
      ∀ T, T₀ ≤ T → ∀ L, L₀ ≤ L → ∀ N, 1 ≤ N →
        ∃ Wit : PinnedLayerWitnessD L N D₁ D₂ α K₀ K₁ Kv a₁ a₂ Kov,
          ∀ i (ρ : RotatorDualFace L → ℤ), ρ ∈ Wit.layer.N i →
            |rootedActivityD Wit.layer (sosCost T) (sosKappa T) (sosAmp K₁ T)
                (sosCutoff (gradExponent α) T) i ρ| ≤
              Real.exp (-(r * T) * (∑ j, |(ρ j : ℝ)| + Wit.A ρ)) :=
  sos_uniform_activity_rate (sosPinnedCarrierHypothesis_of_rootedComponents h)

end FroehlichSpencer.BKT.SOS.Layer

end
