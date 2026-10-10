/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Disorder.FejerChargeLayer
public import FroehlichSpencer.BKT.Clock.Compact.Theorem71
import Mathlib.Tactic

/-!
# Explicit large-clock threshold for the free-square Fejér layer

The Fejér mixture entropy costs `2∑|ρ| + 200 A(ρ)`. Taking amplitude `2000·max(D₁,1)` leaves
decay rate `b=2` after both entropy losses. The threshold below is an explicit ceiling of the
unmarked compact-renormalization bounds; it grows at least linearly in `β+1`. For every `N` above
it, the free-square KP layer exists and its renormalized activities have the required scale decay.
-/

@[expose] public section

noncomputable section

open Filter Topology
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.SpinWaves

namespace FroehlichSpencer.BKT.Clock.Disorder

/-- Fixed constants leaving a positive activity-decay margin after the Fejér mixture entropy. -/
structure ClockFejerAbsorptionParameters where
  amp : ℝ
  W : ℝ
  k₀ : ℕ
  amp_pos : 0 < amp
  W_eq : W = amp * 28
  W_ge_one : 1 ≤ W
  k₀_ge_one : 1 ≤ k₀
  hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4) * (k₀ : ℝ)) / 28
  activity_one : 2 ≤ amp / 8 - 2
  activity_two : 2 ≤ amp / (8 * kpD₁) - 200

theorem exists_clockFejerAbsorptionParameters : Nonempty ClockFejerAbsorptionParameters := by
  let D := max kpD₁ 1
  have hD : 1 ≤ D := le_max_right _ _
  have hDpos : 0 < D := by linarith
  have hkpd : kpD₁ ≤ D := le_max_left _ _
  let amp := 2000 * D
  have hamp : 0 < amp := by dsimp [amp]; positivity
  have hamp_lower : 2000 ≤ amp := by dsimp [amp]; nlinarith
  let W := amp * 28
  have hW : W = amp * 28 := rfl
  have hWone : 1 ≤ W := by rw [hW]; nlinarith
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (28 * amp) (by norm_num : (1 : ℝ) < 8)
  have hm8 : 28 * amp ≤ (8 : ℝ) ^ (m + 1) := by
    have hpow : (8 : ℝ) ^ m ≤ 8 ^ (m + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  let k₀ := 7 * (m + 1)
  have hk₀ : 1 ≤ k₀ := by dsimp [k₀]; omega
  have hrpow : (2 : ℝ) ^ (gradExponent (7 / 4) * (k₀ : ℝ)) = 8 ^ (m + 1) := by
    simpa [k₀] using rpow_gradExponent_seven (m + 1)
  have hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4) * (k₀ : ℝ)) / 28 := by
    rw [hrpow]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 28)]
    nlinarith [hm8]
  have hact₁ : 2 ≤ amp / 8 - 2 := by nlinarith [hamp_lower]
  have hratio : 1 ≤ D / kpD₁ := (le_div_iff₀ kpD₁_pos).2 (by simpa using hkpd)
  have hratio' : 250 ≤ amp / (8 * kpD₁) := by
    dsimp [amp]
    rw [show 2000 * D / (8 * kpD₁) = 250 * (D / kpD₁) by ring]
    nlinarith
  have hact₂ : 2 ≤ amp / (8 * kpD₁) - 200 := by linarith
  exact ⟨⟨amp, W, k₀, hamp, hW, hWone, hk₀, hquad₂, hact₁, hact₂⟩⟩

/-- The fixed amplitude, strip width, and scale selected by the KP constants. -/
noncomputable def clockFejerAbsorptionParameters : ClockFejerAbsorptionParameters :=
  Classical.choice exists_clockFejerAbsorptionParameters

/-- The real threshold whose ceiling makes all compact unmarked conditions hold. -/
noncomputable def clockFejerThresholdSize (β : ℝ) : ℝ :=
  max (max clockFejerAbsorptionParameters.W
      (8192 * (β + 1) * clockFejerAbsorptionParameters.amp))
    (200 * 4 ^ clockFejerAbsorptionParameters.k₀ * (β + 1) *
      clockFejerAbsorptionParameters.W ^ 2 *
      (1 + Real.exp (2 * Real.pi * clockFejerAbsorptionParameters.W)) /
      clockFejerAbsorptionParameters.amp)

/-- An explicit natural threshold for the compact Fejér charge layer. -/
noncomputable def clockFejerLayerThreshold (β : ℝ) : ℕ :=
  Nat.ceil (clockFejerThresholdSize β) + 1

theorem clockFejerThresholdSize_le_threshold (β : ℝ) :
    clockFejerThresholdSize β ≤ (clockFejerLayerThreshold β : ℝ) := by
  unfold clockFejerLayerThreshold
  have h := Nat.le_ceil (clockFejerThresholdSize β)
  exact h.trans (by norm_cast; omega)

theorem clockFejerThreshold_activity_le_size (β : ℝ) :
    8192 * (β + 1) * clockFejerAbsorptionParameters.amp ≤ clockFejerThresholdSize β := by
  unfold clockFejerThresholdSize
  exact le_trans (le_max_right _ _) (le_max_left _ _)

/-- The chosen clock threshold tends to infinity with the inverse temperature. -/
theorem tendsto_clockFejerLayerThreshold :
    Tendsto clockFejerLayerThreshold atTop atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  have hc : 0 < 8192 * clockFejerAbsorptionParameters.amp := by
    have := clockFejerAbsorptionParameters.amp_pos
    positivity
  filter_upwards [eventually_ge_atTop ((b : ℝ) / (8192 * clockFejerAbsorptionParameters.amp))]
    with β hβ
  have hlin : (b : ℝ) ≤ 8192 * (β + 1) * clockFejerAbsorptionParameters.amp := by
    have hmul := mul_le_mul_of_nonneg_left hβ hc.le
    have hbc : (8192 * clockFejerAbsorptionParameters.amp) *
        ((b : ℝ) / (8192 * clockFejerAbsorptionParameters.amp)) = b := by
      field_simp [clockFejerAbsorptionParameters.amp_pos.ne']
    rw [hbc] at hmul
    nlinarith
  have htotal : (b : ℝ) ≤ (clockFejerLayerThreshold β : ℝ) :=
    hlin.trans ((clockFejerThreshold_activity_le_size β).trans
      (clockFejerThresholdSize_le_threshold β))
  exact_mod_cast htotal

/-- Above the explicit threshold, the compact shift envelope and the unmarked KP smallness
conditions hold with the selected amplitude and scale. -/
theorem clockFejerAbsorption_of_largeN {β : ℝ} (hβ : 0 ≤ β) {N : ℕ}
    (hN : clockFejerLayerThreshold β ≤ N) :
    ∃ κ κ' : ℝ,
      κ = (β + 1) / (N : ℝ) ^ 2 ∧
      κ' = (β + 1) * clockFejerAbsorptionParameters.W ^ 2 / (N : ℝ) ^ 2 ∧
      0 < κ ∧
      IsCostEnvelope (clockShiftCost β N) κ κ' clockFejerAbsorptionParameters.W ∧
      100 * 4 ^ clockFejerAbsorptionParameters.k₀ *
        costMajorant κ κ' (clockFejerAbsorptionParameters.amp * 28) ≤
          clockFejerAbsorptionParameters.amp / 2 ∧
      clockFejerAbsorptionParameters.amp ≤ 1 / (2 * κ * 4096) := by
  let P := clockFejerAbsorptionParameters
  let κ : ℝ := (β + 1) / (N : ℝ) ^ 2
  let κ' : ℝ := (β + 1) * P.W ^ 2 / (N : ℝ) ^ 2
  have hsize : clockFejerThresholdSize β ≤ (N : ℝ) := by
    have hle : (clockFejerLayerThreshold β : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact (clockFejerThresholdSize_le_threshold β).trans hle
  have hWle : P.W ≤ (N : ℝ) := by
    have hWsize : P.W ≤ clockFejerThresholdSize β := by
      unfold clockFejerThresholdSize
      exact le_trans (le_max_left _ _) (le_max_left _ _)
    exact hWsize.trans hsize
  have hX8 : 8192 * (β + 1) * P.amp ≤ (N : ℝ) ^ 2 := by
    have h8size := clockFejerThreshold_activity_le_size β
    have hNle : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
      have hN1 : 1 ≤ (N : ℝ) := P.W_ge_one.trans hWle
      nlinarith
    exact (h8size.trans hsize).trans hNle
  have hXe : 200 * 4 ^ P.k₀ * (β + 1) * P.W ^ 2 *
      (1 + Real.exp (2 * Real.pi * P.W)) / P.amp ≤ (N : ℝ) ^ 2 := by
    have hEsize : 200 * 4 ^ P.k₀ * (β + 1) * P.W ^ 2 *
        (1 + Real.exp (2 * Real.pi * P.W)) / P.amp ≤ clockFejerThresholdSize β := by
      unfold clockFejerThresholdSize
      exact le_max_right _ _
    have hNle : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
      have hN1 : 1 ≤ (N : ℝ) := P.W_ge_one.trans hWle
      nlinarith
    exact (hEsize.trans hsize).trans hNle
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := P.W_ge_one.trans hWle
  have hNpos : (0 : ℝ) < N := by linarith
  have ⟨hexp, hquad₁⟩ := clock_unmarked_conditions hβ P.amp_pos hNpos hXe hX8 P.W_eq
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hc : IsCostEnvelope (clockShiftCost β N) κ κ' P.W := by
    have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    have hc₀ := clockShiftCost_isCostEnvelope hβ hN1 hWle
    refine isCostEnvelope_mono hc₀ ?_ ?_
    · exact div_le_div_of_nonneg_right (by linarith) hN2.le
    · exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg P.W]) hN2.le
  refine ⟨κ, κ', rfl, rfl, hκ, hc, ?_, ?_⟩
  · simpa [κ, κ', P.W_eq] using hexp
  · simpa [κ] using hquad₁

/-- The KP free-square layer data, its all-shifts clock renormalization identity, and the
Fejér-specific activity decay at the explicit `N` threshold. -/
structure ClockFejerChargeLayerData (L n M : ℕ) (β : ℝ) where
  centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L
  CL : ChargeLayer (squareFree L) (fun _ φ => fejerPolynomial M (φ - clockOffset n))
    centerOf (fun ϱ => (chargeCoverCost .free L ϱ : ℝ))
    (fun ϱ => ∏ j ∈ chargeSupport ϱ,
      mixtureLeaf (fun _ => M) (fun _ q => fejerShiftCoeff M (clockOffset n) q)
        (fun _ => geomMixture M) j (ϱ j).natAbs)
    kpD₁ 200 (7 / 4) 4096 28
  hCL : ∀ i, CL.R i = neutralPart (CL.N i) ∧ AtMostOneNonNeutral (CL.N i) ∧
    IsChargeEnsemble (CL.N i) ∧ IsScaleSeparated .free L (CL.N i)
  z : Fin CL.n → (Fin L × Fin L → ℤ) → ℝ
  a : Fin CL.n → (Fin L × Fin L → ℤ) → Fin L × Fin L → ℝ
  expansion : ∀ σ : Fin L × Fin L → ℝ,
    ∫ φ, ((∏ j, fejerClockMultiplier n M (φ j + σ j) : ℝ) : ℂ)
        ∂clockLaw β n (squareFree L) =
      ∑ i, (CL.c i : ℂ) * ∫ φ, ∏ ϱ ∈ CL.R i,
        ((1 : ℂ) + (z i ϱ : ℂ) *
          localFactor (clockEdgeWeight β n) (clockShiftCost β n)
            (gradLinear (squareFree L) (a i ϱ))
            (gradLinear (squareFree L) φ)
            (∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ)))
        ∂clockLaw β n (squareFree L)
  activityDecay : ∀ i, ∀ ϱ ∈ CL.R i,
    |z i ϱ| ≤ Real.exp (-2 * ((∑ j, |(ϱ j : ℝ)|) +
      Real.logb 2 ((squareFree L).densityDiameter ϱ + 1)))

/-- At `N ≥ n₁(β)`, instantiate the KP free-square layer and obtain both its exact shifted
compact-law expansion and the explicit decay rate needed by the T1.5 packing estimate. -/
theorem exists_clockFejerChargeLayer_of_largeN {L n M : ℕ} (hL : 1 < L) (hM : 1 ≤ M)
    {β : ℝ} (hβ : 0 ≤ β) (hN : clockFejerLayerThreshold β ≤ n) :
    Nonempty (ClockFejerChargeLayerData L n M β) := by
  let P := clockFejerAbsorptionParameters
  obtain ⟨κ, κ', rfl, rfl, hκ, hc, hexp, hquad₁⟩ :=
    clockFejerAbsorption_of_largeN hβ hN
  have hWsize : P.W ≤ clockFejerThresholdSize β := by
    unfold clockFejerThresholdSize
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hthreshold : (1 : ℝ) ≤ (n : ℝ) :=
    P.W_ge_one.trans (hWsize.trans
      (clockFejerThresholdSize_le_threshold β |>.trans (by exact_mod_cast hN)))
  have hn : 0 < n := by
    have hnreal : (0 : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast hnreal
  have hAmpW : P.amp * 28 ≤ P.W := by rw [P.W_eq]
  have hMpos : 0 < M := by omega
  obtain ⟨centerOf, CL, hCL, z, a, hid, hz⟩ := exists_freeSquare_fejerChargeLayer
    hL hn hM hβ hc hκ P.amp_pos.le hAmpW P.W_ge_one P.k₀_ge_one
    hexp hquad₁ P.hquad₂
  have hlog8 : Real.log 8 / 2 ≤ (2 : ℝ) := by
    have h4 : 8 ≤ Real.exp 4 := by
      rw [show (4 : ℝ) = 2 + 2 by norm_num, Real.exp_add]
      nlinarith [Real.add_one_le_exp (2 : ℝ), sq_nonneg (Real.exp 2 - 3)]
    have hlog : Real.log 8 ≤ 4 :=
      (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 8)).2 h4
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by linarith)
  have hdecay := fejerChargeLayer_decay_bound hL hMpos centerOf CL hCL z hlog8
    P.activity_one P.activity_two hz
  exact ⟨⟨centerOf, CL, hCL, z, a, hid, hdecay⟩⟩

end FroehlichSpencer.BKT.Clock.Disorder

end
