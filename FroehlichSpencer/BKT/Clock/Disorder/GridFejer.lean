/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Disorder.GridShiftBound
public import FroehlichSpencer.BKT.Clock.Disorder.FejerThreshold
public import FroehlichSpencer.BKT.Generic.Moment.KPLayer
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# The compact T1.5 for the free-square Fejér clock layer

The KP free-square charge layer for the compact Fejér multiplier (`FejerChargeLayer.lean`), fed into
the compact T1.5 (`integral_gridShift_ge_of_chargeLayer`). The packing threshold of KP's
estimate needs an activity decay rate `b ≥ b₀`, with `b₀` from `exists_touching_threshold`
(`(d + 1)⁵` against `2^{−b log₂(d+1)}`). The rate `b = 2` of `FejerThreshold.lean` is not enough.
This file therefore chooses its own amplitude:

* `gridRate`, `gridPackingEps`: the rate `b` and the packing constant `ε = C e^{−b}`;
* `GridAbsorptionParameters`, `gridAbsorptionParameters`: the amplitude, width and scale leaving
  activity margin `b` after the Fejér mixture entropy (`2∑|ϱ|`) and the ensemble entropy
  (`200 A(ϱ)`);
* **`gridThreshold β`**: an explicit natural threshold with `gridThreshold β → ∞` as `β → ∞`. Above
  it the compact cost envelope, the unmarked smallness conditions and the logarithmic-derivative
  bound `m ≤ 1` all hold;
* **`gridFejer_shift_ge`**: for `N ≥ gridThreshold β`, every site shift `σ` and bond offset `θ`,

  `exp(−(2β/N²)‖θ‖² − ε ∑_e ([∇σ]²_{2π} + θ²)) ∫ ρ₀ ∏_j F(φ_j) dν ≤ ∫ ρ_θ ∏_j F(φ_j + σ_j) dν`,

  with `F` the Fejér clock multiplier.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open Filter Topology MeasureTheory
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.SpinWaves
open FroehlichSpencer.BKT.Reduction
open FroehlichSpencer.BKT.Lattice2D

/-! ### The packing constants -/

/-- KP's packing threshold for the free square (`Kv = 64`, `p = q = 4`). -/
theorem gridTouching_exists :
    ∃ C b₀ : ℝ, 0 ≤ C ∧ 0 < b₀ ∧ ∀ b : ℝ, b₀ ≤ b → ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      2 * (8 * ((64 : ℝ) + 2 * 64 ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
        Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ C * Real.exp (-b) :=
  exists_touching_threshold (8 * ((64 : ℝ) + 2 * 64 ^ 2)) (by norm_num) 4 4

/-- The packing prefactor `C`. -/
def gridPackingC : ℝ := Classical.choose gridTouching_exists

/-- The activity decay rate used by the packing estimate. -/
def gridRate : ℝ := max (Classical.choose (Classical.choose_spec gridTouching_exists)) 2

/-- The packing constant `ε = C e^{−b}`. -/
def gridPackingEps : ℝ := gridPackingC * Real.exp (-gridRate)

theorem gridPackingEps_nonneg : 0 ≤ gridPackingEps :=
  mul_nonneg (Classical.choose_spec (Classical.choose_spec gridTouching_exists)).1
    (Real.exp_pos _).le

theorem gridRate_ge_two : 2 ≤ gridRate := le_max_right _ _

theorem gridThr {d u : ℝ} (hd : 1 ≤ d) (hu : 2 ≤ u) :
    2 * (8 * ((64 : ℝ) + 2 * 64 ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
      Real.exp (-gridRate * (u + Real.logb 2 (d + 1))) ≤ gridPackingEps :=
  (Classical.choose_spec (Classical.choose_spec gridTouching_exists)).2.2 gridRate
    (le_max_left _ _) d u hd hu

theorem log_eight_div_two_le_gridRate : Real.log 8 / 2 ≤ gridRate := by
  have h4 : 8 ≤ Real.exp 4 := by
    rw [show (4 : ℝ) = 2 + 2 by norm_num, Real.exp_add]
    nlinarith [Real.add_one_le_exp (2 : ℝ), sq_nonneg (Real.exp 2 - 3)]
  have hlog : Real.log 8 ≤ 4 :=
    (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 8)).2 h4
  have := gridRate_ge_two
  linarith

/-! ### The absorption parameters -/

/-- Amplitude, width and scale leaving an activity margin `b` after both entropy losses. -/
structure GridAbsorptionParameters (b : ℝ) where
  amp : ℝ
  W : ℝ
  k₀ : ℕ
  amp_pos : 0 < amp
  W_eq : W = amp * 28
  W_ge_one : 1 ≤ W
  k₀_ge_one : 1 ≤ k₀
  hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4) * (k₀ : ℝ)) / 28
  activity_one : b ≤ amp / 8 - 2
  activity_two : b ≤ amp / (8 * kpD₁) - 200

theorem exists_gridAbsorptionParameters (b : ℝ) : Nonempty (GridAbsorptionParameters b) := by
  let D := max kpD₁ 1
  have hD : 1 ≤ D := le_max_right _ _
  have hkpd : kpD₁ ≤ D := le_max_left _ _
  let amp := 8 * D * (|b| + 250)
  have hamp : 0 < amp := by dsimp [amp]; positivity
  have hamp_lower : 2000 ≤ amp := by
    dsimp [amp]
    have := abs_nonneg b
    nlinarith
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
    rw [hrpow, le_div_iff₀ (by norm_num : (0 : ℝ) < 28)]
    nlinarith [hm8]
  have hact₁ : b ≤ amp / 8 - 2 := by
    have h1 : amp / 8 = D * (|b| + 250) := by dsimp [amp]; ring
    rw [h1]
    have := le_abs_self b
    nlinarith [abs_nonneg b]
  have hratio : 1 ≤ D / kpD₁ := (le_div_iff₀ kpD₁_pos).2 (by simpa using hkpd)
  have hact₂ : b ≤ amp / (8 * kpD₁) - 200 := by
    have h1 : amp / (8 * kpD₁) = (D / kpD₁) * (|b| + 250) := by
      dsimp [amp]; field_simp
    rw [h1]
    have := le_abs_self b
    nlinarith [abs_nonneg b]
  exact ⟨⟨amp, W, k₀, hamp, hW, hWone, hk₀, hquad₂, hact₁, hact₂⟩⟩

/-- The fixed parameters at the rate `gridRate`. -/
def gridAbsorptionParameters : GridAbsorptionParameters gridRate :=
  Classical.choice (exists_gridAbsorptionParameters gridRate)

/-- The real threshold. -/
def gridThresholdSize (β : ℝ) : ℝ :=
  max (max (max gridAbsorptionParameters.W (8192 * (β + 1) * gridAbsorptionParameters.amp))
    (200 * 4 ^ gridAbsorptionParameters.k₀ * (β + 1) * gridAbsorptionParameters.W ^ 2 *
      (1 + Real.exp (2 * Real.pi * gridAbsorptionParameters.W)) / gridAbsorptionParameters.amp))
    (8 * (β + 1))

/-- **The explicit clock threshold** `n₁(β)`. -/
def gridThreshold (β : ℝ) : ℕ := Nat.ceil (gridThresholdSize β) + 1

theorem gridThresholdSize_le (β : ℝ) : gridThresholdSize β ≤ (gridThreshold β : ℝ) := by
  unfold gridThreshold
  have h := Nat.le_ceil (gridThresholdSize β)
  exact h.trans (by norm_cast; omega)

/-- **`n₁(β) → ∞` as `β → ∞`.** -/
theorem tendsto_gridThreshold : Tendsto gridThreshold atTop atTop := by
  refine Filter.tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop (b : ℝ)] with β hβ
  have h1 : (b : ℝ) ≤ 8 * (β + 1) := by linarith
  have h2 : 8 * (β + 1) ≤ gridThresholdSize β := le_max_right _ _
  have := (h1.trans h2).trans (gridThresholdSize_le β)
  exact_mod_cast this

/-- The logarithmic-derivative bound of the clock weight. -/
def gridLogDerivBound (β n : ℝ) (u : ℝ) : ℝ := (β / n + β / n ^ 2) * (Real.exp (|u| / n) + 1)

theorem clock_hasLogDerivBounds {β n : ℝ} (hβ : 0 ≤ β) (hn : 0 < n) (W : ℝ) :
    HasLogDerivBounds (clockEdgeWeight β n) W (gridLogDerivBound β n) := by
  have hβn : 0 ≤ β / n := div_nonneg hβ hn.le
  have hβn2 : 0 ≤ β / n ^ 2 := div_nonneg hβ (sq_nonneg n)
  refine ⟨fun t u _ => ?_, fun t u _ => ?_⟩
  · have h1 := clockEdgeWeight_logDeriv_le β n hβ hn t u
    have h0 := clockEdgeWeight_logDeriv_le β n hβ hn t 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h0
    unfold clockLogDerivBound₁ at h1 h0
    simp only [abs_zero, zero_div, Real.exp_zero, mul_one] at h0
    calc _ ≤ ‖logDeriv (clockEdgeWeight β n) ((t : ℂ) + (u : ℂ) * Complex.I)‖ +
          ‖logDeriv (clockEdgeWeight β n) (t : ℂ)‖ := norm_sub_le _ _
      _ ≤ β / n * Real.exp (|u| / n) + β / n := add_le_add h1 h0
      _ ≤ gridLogDerivBound β n u := by
          unfold gridLogDerivBound
          have := Real.exp_pos (|u| / n)
          nlinarith
  · have h1 := clockEdgeWeight_deriv_logDeriv_le β n hβ hn t u
    have h0 := clockEdgeWeight_deriv_logDeriv_le β n hβ hn t 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h0
    unfold clockLogDerivBound₂ at h1 h0
    simp only [abs_zero, zero_div, Real.exp_zero, mul_one] at h0
    calc _ ≤ ‖deriv (logDeriv (clockEdgeWeight β n)) ((t : ℂ) + (u : ℂ) * Complex.I)‖ +
          ‖deriv (logDeriv (clockEdgeWeight β n)) (t : ℂ)‖ := norm_sub_le _ _
      _ ≤ β / n ^ 2 * Real.exp (|u| / n) + β / n ^ 2 := add_le_add h1 h0
      _ ≤ gridLogDerivBound β n u := by
          unfold gridLogDerivBound
          have := Real.exp_pos (|u| / n)
          nlinarith

/-- Above the threshold: the cost envelope, the unmarked smallness conditions, and the
logarithmic-derivative margin. -/
theorem gridAbsorption_of_largeN {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : gridThreshold β ≤ N) :
    let P := gridAbsorptionParameters
    1 ≤ (N : ℝ) ∧ P.W ≤ N ∧ 8 * (β + 1) ≤ N ∧
      IsCostEnvelope (clockShiftCost β N) ((β + 1) / (N : ℝ) ^ 2)
        ((β + 1) * P.W ^ 2 / (N : ℝ) ^ 2) P.W ∧
      100 * 4 ^ P.k₀ * costMajorant ((β + 1) / (N : ℝ) ^ 2)
        ((β + 1) * P.W ^ 2 / (N : ℝ) ^ 2) (P.amp * 28) ≤ P.amp / 2 ∧
      P.amp ≤ 1 / (2 * ((β + 1) / (N : ℝ) ^ 2) * 4096) := by
  intro P
  have hsize : gridThresholdSize β ≤ (N : ℝ) := by
    have hle : (gridThreshold β : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact (gridThresholdSize_le β).trans hle
  have hWle : P.W ≤ (N : ℝ) := by
    have : P.W ≤ gridThresholdSize β := by
      unfold gridThresholdSize
      exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
    exact this.trans hsize
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := P.W_ge_one.trans hWle
  have hNle : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hX8 : 8192 * (β + 1) * P.amp ≤ (N : ℝ) ^ 2 := by
    have : 8192 * (β + 1) * P.amp ≤ gridThresholdSize β := by
      unfold gridThresholdSize
      exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
    exact (this.trans hsize).trans hNle
  have hXe : 200 * 4 ^ P.k₀ * (β + 1) * P.W ^ 2 *
      (1 + Real.exp (2 * Real.pi * P.W)) / P.amp ≤ (N : ℝ) ^ 2 := by
    have : 200 * 4 ^ P.k₀ * (β + 1) * P.W ^ 2 *
        (1 + Real.exp (2 * Real.pi * P.W)) / P.amp ≤ gridThresholdSize β := by
      unfold gridThresholdSize
      exact le_trans (le_max_right _ _) (le_max_left _ _)
    exact (this.trans hsize).trans hNle
  have h8 : 8 * (β + 1) ≤ (N : ℝ) := (le_max_right _ _).trans hsize
  have hNpos : (0 : ℝ) < N := by linarith
  have ⟨hexp, hquad₁⟩ := clock_unmarked_conditions hβ P.amp_pos hNpos hXe hX8 P.W_eq
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hc₀ := clockShiftCost_isCostEnvelope hβ hN1 hWle
  have hc : IsCostEnvelope (clockShiftCost β N) ((β + 1) / (N : ℝ) ^ 2)
      ((β + 1) * P.W ^ 2 / (N : ℝ) ^ 2) P.W := by
    refine isCostEnvelope_mono hc₀ ?_ ?_
    · exact div_le_div_of_nonneg_right (by linarith) hN2.le
    · exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg P.W]) hN2.le
  exact ⟨hN1, hWle, h8, hc, by simpa [P.W_eq] using hexp, hquad₁⟩

/-! ### The free-square Fejér instance -/

/-- **The compact T1.5 for the Fejér clock product on the free square.** -/
theorem gridFejer_shift_ge {L N M : ℕ} (hL : 1 < L) (hM : 1 ≤ M) {β : ℝ} (hβ : 0 ≤ β)
    (hN : gridThreshold β ≤ N) (σ : Fin L × Fin L → ℝ) (θ : SquareFreeEdge L → ℝ) :
    Real.exp (-(2 * β / (N : ℝ) ^ 2 * ∑ e, θ e ^ 2) -
        gridPackingEps * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi)
          ((squareFree L).grad σ e) ^ 2 + θ e ^ 2)) *
        ∫ φ, compactClockBondProduct (squareFree L) β N φ 0 *
          ∏ j, fejerClockMultiplier N M (φ j) ∂gridBoxMeasure N (Fin L × Fin L) ≤
      ∫ φ, compactClockBondProduct (squareFree L) β N φ θ *
          ∏ j, fejerClockMultiplier N M (φ j + σ j) ∂gridBoxMeasure N (Fin L × Fin L) := by
  classical
  set P := gridAbsorptionParameters
  obtain ⟨hN1, hWle, h8, hc, hexp, hquad₁⟩ := gridAbsorption_of_largeN hβ hN
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := by linarith
    exact_mod_cast this
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hMpos : 0 < M := hM
  -- the KP layer
  have hcex : ∀ ϱ : Fin L × Fin L → ℤ, ∃ j, ϱ ≠ 0 → (squareFree L).IsDensityCenter ϱ j := by
    intro ϱ
    by_cases h : ϱ = 0
    · exact ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), fun h' => absurd h h'⟩
    · obtain ⟨j, hj⟩ := (squareFree L).exists_isDensityCenter ϱ h
      exact ⟨j, fun _ => hj⟩
  choose centerOf hcenter using hcex
  obtain ⟨CL, hCL⟩ := exists_kpChargeLayer .free hL (Or.inl rfl) (squareFree L)
    (squareFree_connected L hL) (fun _ _ => rfl)
    (SpinWaves.squareFreeBipartiteDegreeFour L hL)
    (SpinWaves.BoundaryShellPacking.l46Statement_holds L hL).1 kpD₁_pos.le
    (p21Step_kpD₁ hL).1 centerOf hcenter
    (fun _ φ => fejerClockMultiplier N M φ) (fun _ => M)
    (fun _ q => fejerShiftCoeff M (clockOffset N) q) (fun _ => geomMixture M)
    (fun _ => hMpos)
    (by
      intro _ q hq
      unfold fejerShiftCoeff fejerFourierCoefficient
      rw [ite_eq_right (by intro h; omega), zero_mul])
    (by
      intro j φ
      exact fejerPolynomial_sub_clockOffset M N φ)
    (by
      intro j q
      unfold geomMixture
      exact div_pos (by positivity) (geomNorm_pos hMpos))
    (by
      intro j
      unfold geomMixture
      rw [← Finset.sum_div]
      exact div_self (geomNorm_pos hMpos).ne')
  have hne : ∀ i, ∀ ϱ ∈ CL.R i, ϱ ≠ 0 := fun i ϱ hϱ => by
    rw [(hCL i).1] at hϱ
    exact (hCL i).2.2.1.1 ϱ (mem_neutralPart.mp hϱ).1
  have hamp28 : max (P.amp * 28) 1 = P.W := by
    rw [P.W_eq]
    exact max_eq_left (by rw [← P.W_eq]; exact P.W_ge_one)
  -- the logarithmic-derivative margin
  set m : ℝ := (β / N + β / (N : ℝ) ^ 2) * (Real.exp 1 + 1) with hm
  have hβN : β / N ≤ 1 / 8 := by
    rw [div_le_div_iff₀ hNr (by norm_num)]
    linarith
  have hβN2 : β / (N : ℝ) ^ 2 ≤ β / N := by
    apply div_le_div_of_nonneg_left hβ hNr
    nlinarith
  have he1 : Real.exp 1 + 1 ≤ 4 := by
    have := Real.exp_one_lt_three
    linarith
  have hm0 : 0 ≤ m := by positivity
  have hm1 : m ≤ 1 := by
    have h1 : β / N + β / (N : ℝ) ^ 2 ≤ 1 / 4 := by linarith
    calc m ≤ (1 / 4) * 4 := mul_le_mul h1 he1 (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hM : ∀ u : ℝ, |u| ≤ max (P.amp * 28) 1 → gridLogDerivBound β N u ≤ m := by
    intro u hu
    rw [hamp28] at hu
    unfold gridLogDerivBound
    have hun : |u| / N ≤ 1 := by
      rw [div_le_one hNr]
      linarith
    have he : Real.exp (|u| / N) ≤ Real.exp 1 := Real.exp_le_exp.mpr hun
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hleaf := fun (j : Fin L × Fin L) (q : ℕ) => mixtureLeaf_fejer_le hMpos N j q
  refine integral_gridShift_ge_of_chargeLayer (squareFree_connected L hL) CL
    (fun i => ⟨(hCL i).1, (hCL i).2.1⟩) hne (fun i ϱ hϱ => hcenter ϱ (hne i ϱ hϱ)) ?_ ?_
    (Kv := 64) (by norm_num) (card_edgesTouching_densityDomain_squareFree_le hL) hNpos hβ
    (clock_hasLogDerivBounds hβ hNr P.W) (clockEdgeWeight_hasCurvatureBound hβ hNr) hc
    (by positivity) (by norm_num) (by norm_num) kpD₁_pos P.amp_pos.le (by rw [P.W_eq])
    P.W_ge_one P.k₀_ge_one hexp hquad₁ P.hquad₂ hm0 hm1 hM (a₂ := 0)
    (fun ϱ => (prod_mixtureLeaf_le _ _ _ (fun j q => div_pos (by positivity)
      (geomNorm_pos hMpos)) hleaf ϱ).trans_eq (by rw [zero_mul, add_zero]))
    log_eight_div_two_le_gridRate P.activity_one (by rw [sub_zero]; exact P.activity_two)
    (fun d u hd hu => gridThr hd hu) σ θ
  · intro i ϱ₁ h₁ ϱ₂ h₂ hne' k hk hd₁ hd₂ j₁ j₂ hj₁ hj₂
    rw [(hCL i).1] at h₁ h₂
    exact Reduction.densityDomain_inter_eq_empty .free (squareFree L)
      (squareFree_connected L hL) (fun _ _ => rfl)
      ((hCL i).2.2.2.1 ϱ₁ (mem_neutralPart.mp h₁).1 ϱ₂ (mem_neutralPart.mp h₂).1 hne') hk hd₁ hd₂
      hj₁ hj₂
  · intro i ϱ hϱ
    have h := ((p21Step_kpD₁ hL).1 (fun ϱ k => sharedMinimumSquareCover .free L ϱ (by omega) k) ϱ
      (hne i ϱ hϱ)).1
    rwa [chargeDiameter_eq_densityDiameter .free (squareFree L) (fun _ _ => rfl)] at h

end FroehlichSpencer.BKT.Clock.Disorder

end
