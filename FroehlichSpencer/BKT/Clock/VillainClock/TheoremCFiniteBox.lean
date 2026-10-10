/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.PlaneRotator.TheoremC

/-!
# The finite-box form of FS81 Theorem C for the Villain model

`PlaneRotator.villain_theoremC` states FS81 Theorem C for the free thermodynamic limit. Its proof
(`Villain/TheoremC/MainD.lean`) first proves a bound on every sufficiently large centred free box
`[-L, L]²`, uniformly in `L`, and then passes to the limit. The self-dual route to the Villain-clock
(7.5) needs the finite-box bound itself, so this module restates it:

* **`villain_finiteBox_lowerBound`**: there are `β₀ ≥ 1`, `C₀ > 0`, a coefficient `p(β) ≥ 0` and a
  cutoff `L₀` such that for `β ≥ β₀`, every integer harmonic `ξ`, all sites `u, v` and every box
  radius `L ≥ |u − v|₁ + |u|_∞ + |v|_∞ + L₀ + 2`,
  `exp(−p(β) C₀ ξ² (1 + log(1 + |u − v|₁))) ≤ ⟨cos(ξ(θ_u − θ_v))⟩_{[-L,L]²}`.

The proof is the finite-box part of `villain_theoremC_of_pinnedLayerD`, applied to the
unconditional pinned layer `PlaneRotator.pinnedLayerHypothesisD_holds`. The coefficient is
`p(β) = (4π²β)⁻¹ + 2ε(4π²β)`, with `ε` the packing loss of the pinned layer.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.PinnedCharges
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.Rotator.Transition
open FroehlichSpencer.BKT.Villain
open FroehlichSpencer.BKT.Villain.TheoremC
open FroehlichSpencer.BKT.PlaneRotator

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

theorem villainClockDual_villainTwoPoint_self {β : ℝ} (hβ : 0 < β) (ξ : ℤ)
    (Λ : Finset (ℤ × ℤ)) (u : ℤ × ℤ) :
    (villainModel β hβ).twoPoint ξ Λ u u = 1 := by
  let M := villainModel β hβ
  have hprob : IsProbabilityMeasure (M.gibbs Λ) := by
    rw [FreeModel.gibbs]
    exact isProbabilityMeasure_pairGibbs circleMeasure_univ_ne_zero
      (M.isBondWeight_bondWeight Λ)
  rw [FreeModel.twoPoint]
  have hcos : (fun θ : Λ → ℝ =>
      Real.cos (ξ * (latticeAngle θ u - latticeAngle θ u))) = fun _ => 1 := by
    funext θ
    simp
  rw [hcos, integral_const]
  simp

theorem villainClockDual_rootedShiftCutoff (hyp : PinnedLayerHypothesisD) :
    ∃ (L₀ : ℕ) (B₀ : ℝ) (ε : ℝ → ℝ),
      1 ≤ B₀ ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ B : ℝ, B₀ ≤ B → 0 ≤ ε B ∧
          ∀ L : ℕ, L₀ ≤ L → 1 < L → ∀ N : ℕ, 1 ≤ N →
            ∀ σ : RotatorDualFace L → ℝ, ∀ θ : SquareZeroBond L → ℝ,
              Real.exp (-(B⁻¹ * ∑ e, θ e ^ 2) -
                  ε B * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi)
                    ((squareZero L).grad σ e) ^ 2 + θ e ^ 2)) *
                  ∫ φ, edgeDensity (squareZero L) (gaussianVillainWeight B) none φ *
                    ∏ j, pinnedCombLam L N j (φ j - φ none) ≤
                ∫ φ, offsetEdgeDensity (squareZero L) (gaussianVillainWeight B) θ none φ *
                  ∏ j, pinnedCombLam L N j
                    (φ j + σ j - (φ none + σ none)) := by
  obtain ⟨D₁, D₂, α, K₀, K₁, Kv, a₁, a₂, Kov, L₀,
      hα, hK₀, hK₁, hD₁, hKv, hwit⟩ := hyp
  obtain ⟨B₀, amp, b, ε, k₀, hB₀, hεlim, hN⟩ :=
    exists_gaussianVillainNumbers (D₂ := D₂) (α := α) (K₀ := K₀) (K₁ := K₁)
      (Kv := Kv) (a₁ := a₁) (a₂ := a₂) Kov hα hK₀ hK₁ hD₁ hKv
  refine ⟨L₀, B₀, ε, hB₀, hεlim, fun B hB => ?_⟩
  have hBpos : 0 < B := by linarith [hB₀, hB]
  obtain ⟨hamp, hampW, hk₀, hexp, hquad₁, hquad₂, hM, hb8, hb₁, hb₂,
    hε0, hthr⟩ := hN B hB
  refine ⟨hε0, fun L hL₀ hL N hN σ θ => ?_⟩
  have hW0 : 0 ≤ Real.pi * B := by positivity
  have hW1 : 1 ≤ Real.pi * B := by nlinarith [Real.two_le_pi]
  obtain ⟨Wt⟩ := hwit L hL₀ N hN
  obtain ⟨hw, hnzero, hlog, hcurv, hcost⟩ :=
    gaussianVillainWeight_data hBpos (Real.pi * B) hW0
  exact integral_shift_ge_of_rootedLayerD (squareZero_connected L hL) none Wt.layer
    Wt.isLocal hKv hw hnzero hlog hcurv hcost (inv_pos.mpr hBpos) hK₀ hK₁ hD₁
    hamp hampW hW1 hk₀ hexp hquad₁ hquad₂ zero_le_one le_rfl hM Wt.entropy_exp
    hb8 hb₁ hb₂ hthr σ θ


/-- **The finite-box Villain Theorem C** (the uniform finite-volume bound inside the proof of
FS81 Theorem C for the Villain model). -/
theorem villain_finiteBox_lowerBound :
    ∃ (β₀ C₀ : ℝ) (p : ℝ → ℝ) (L₀ : ℕ), 0 < C₀ ∧ 1 ≤ β₀ ∧
      ∀ β (hβ : 0 < β), β₀ ≤ β → 0 ≤ p β ∧
        ∀ (ξ : ℤ) (u v : ℤ × ℤ) (L : ℕ),
          l1Norm (u - v) + boxRadius u + boxRadius v + L₀ + 2 ≤ L →
            Real.exp (-((p β * C₀) * ((ξ : ℝ) ^ 2 *
              (1 + Real.log (1 + (l1Norm (u - v) : ℝ)))))) ≤
              (villainModel β hβ).twoPoint ξ (freeBox L) u v := by
  obtain ⟨L₀, B₀, ε, hB₀, hεlim, hShift⟩ :=
    villainClockDual_rootedShiftCutoff pinnedLayerHypothesisD_holds
  obtain ⟨C₀, hC₀, hJ⟩ := exists_harmonicField
  let β₀ : ℝ := max 1 (B₀ / (4 * Real.pi ^ 2))
  let B : ℝ → ℝ := fun β => 4 * Real.pi ^ 2 * β
  let p : ℝ → ℝ := fun β => (B β)⁻¹ + 2 * ε (B β)
  have hscale : 0 < 4 * Real.pi ^ 2 := by positivity
  have hβ₀_one : 1 ≤ β₀ := le_max_left _ _
  have hB₀_le : B₀ / (4 * Real.pi ^ 2) ≤ β₀ := le_max_right _ _
  have hBpos : ∀ β, β₀ ≤ β → 0 < B β := by
    intro β hβ
    have hβpos : 0 < β := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (le_trans hβ₀_one hβ)
    dsimp [B]
    positivity
  have hBlarge : ∀ β, β₀ ≤ β → B₀ ≤ B β := by
    intro β hβ
    have hβ : B₀ / (4 * Real.pi ^ 2) ≤ β := le_trans hB₀_le hβ
    dsimp [B]
    have hmul := mul_le_mul_of_nonneg_right hβ hscale.le
    calc
      B₀ = (B₀ / (4 * Real.pi ^ 2)) * (4 * Real.pi ^ 2) := by
        field_simp [hscale.ne']
      _ ≤ β * (4 * Real.pi ^ 2) := hmul
      _ = 4 * Real.pi ^ 2 * β := by ring
  have hεnonneg : ∀ β, β₀ ≤ β → 0 ≤ ε (B β) := by
    intro β hβ
    exact (hShift (B β) (hBlarge β hβ)).1
  refine ⟨β₀, C₀, p, L₀, hC₀, hβ₀_one, fun β hβ hβlarge => ?_⟩
  have hpNonneg : 0 ≤ p β := by
    dsimp [p]
    exact add_nonneg (inv_nonneg.mpr (hBpos β hβlarge).le)
      (mul_nonneg (by norm_num) (hεnonneg β hβlarge))
  refine ⟨hpNonneg, fun ξ u v L hL => ?_⟩
  by_cases huv : u = v
  · subst v
    rw [villainClockDual_villainTwoPoint_self hβ ξ]
    have hq : 0 ≤ (p β * C₀) * ((ξ : ℝ) ^ 2 *
        (1 + Real.log (1 + (l1Norm (u - u) : ℝ)))) := by
      have hdist : l1Norm (u - u) = 0 := by simp [l1Norm]
      rw [hdist]
      simp only [Nat.cast_zero, add_zero, Real.log_one]
      positivity
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hβL : 1 ≤ β := le_trans hβ₀_one hβlarge
  let R := l1Norm (u - v)
  have hu : boxRadius u ≤ L := by omega
  have hv : boxRadius v ≤ L := by omega
  have hR := siteL1_boxSite hu hv
  have hu1 := coe_boxSite_fst hu
  have hu2 := coe_boxSite_snd hu
  have hv1 := coe_boxSite_fst hv
  have hv2 := coe_boxSite_snd hv
  have hbu1 : u.1.natAbs ≤ boxRadius u := le_max_left _ _
  have hbu2 : u.2.natAbs ≤ boxRadius u := le_max_right _ _
  have hbv1 : v.1.natAbs ≤ boxRadius v := le_max_left _ _
  have hbv2 : v.2.natAbs ≤ boxRadius v := le_max_right _ _
  obtain ⟨j, σ, hj, hσ, hEharm⟩ := hJ (2 * L) (boxSite L u) (boxSite L v)
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  have hne : boxSite L u ≠ boxSite L v := by
    intro h
    apply huv
    have h' := congrArg siteToZ h
    rw [siteToZ_boxSite hu, siteToZ_boxSite hv] at h'
    exact add_right_cancel h'
  have hsource (w : RotatorSpinSite (2 * L)) :
      currentDivergence (rotatorFreeGraph (2 * L)) j w =
        freeBoxEndpointCharge (boxSite L v) (boxSite L u) w := by
    change rotatorCurrentDivergence j w = _
    rw [hj]
    by_cases hu' : w = boxSite L u
    · subst w
      simp [rotatorTwoPointFrequency, freeBoxEndpointCharge, hne]
    · by_cases hv' : w = boxSite L v
      · subst w
        simp [rotatorTwoPointFrequency, freeBoxEndpointCharge, hne.symm]
      · simp [rotatorTwoPointFrequency, freeBoxEndpointCharge, hu', hv']
  let jξ : RotatorInternalBond (2 * L) → ℤ := fun e => ξ * j e
  let σξ : RotatorDualFace (2 * L) → ℝ := fun f => (ξ : ℝ) * σ f
  have hσξ : σξ none = 0 := by simp [σξ, hσ]
  let θd : RotatorInternalBond (2 * L) → ℝ := fun e =>
    2 * Real.pi * (jξ e : ℝ) + (rotatorDualGraph (2 * L)).grad σξ e
  let θ : SquareZeroBond (2 * L) → ℝ := squareZeroField (2 * L) θd
  let E : ℝ := ∑ e, θd e ^ 2
  let Ebase : ℝ := ∑ e, (2 * Real.pi * (j e : ℝ) +
    (rotatorDualGraph (2 * L)).grad σ e) ^ 2
  let P₀ : ℕ → ℂ := fun N =>
    villainPinnedGaussianCombCutoffPairing (2 * L) β (fun _ => 0) N
  let P₁ : ℕ → ℂ := fun N => villainPinnedGaussianCombCutoffPairing (2 * L) β jξ N
  have hEscale : E = (ξ : ℝ) ^ 2 * Ebase := by
    simpa [E, Ebase, θd, jξ, σξ] using sum_sq_intMul ξ j σ
  have hscalePos : (0 : ℝ) < (2 * Real.pi) ^
      (Fintype.card (SquareFreeVertex (2 * L)) + 1) := by positivity
  have hθsum : ∑ e, θ e ^ 2 = E := by
    simpa [θ, θd, E] using sum_sq_squareZeroField (2 * L) θd
  have hW0 : 0 ≤ Real.pi * B β := by positivity
  obtain ⟨hw, -, -, -, -⟩ :=
    gaussianVillainWeight_data (hBpos β hβlarge) (Real.pi * B β) hW0
  let Q : ℝ := ∑ e : SquareZeroBond (2 * L),
    toIcoMod Real.two_pi_pos (-Real.pi)
      ((squareZero (2 * L)).grad σξ e) ^ 2
  let Rε : ℝ := (B β)⁻¹ * E + ε (B β) * (Q + E)
  have hmod : Q ≤ E := by
    simpa [Q, E, θd, jξ, σξ] using sum_toIcoMod_grad_sq_le jξ σξ
  have hEnonneg : 0 ≤ E := Finset.sum_nonneg fun e _ => sq_nonneg (θd e)
  have hRle : Rε ≤ p β * E := by
    have hQsum : Q + E ≤ E + E := add_le_add_left hmod E
    have hmul := mul_le_mul_of_nonneg_left hQsum
      (hεnonneg β hβlarge)
    dsimp [Rε, p]
    nlinarith
  have hcut : ∀ N : ℕ, 1 ≤ N → Real.exp (-Rε) * (P₀ N).re ≤ (P₁ N).re := by
    intro N hN
    have hNfinite := ((hShift (B β) (hBlarge β hβlarge)).2
      (2 * L) (by omega) (by omega) N hN σξ θ)
    rw [integral_edgeDensity_villainGaussianPinnedComb (L := 2 * L) N hβ hw,
      integral_offsetEdgeDensity_villainGaussianPinnedComb_shift (L := 2 * L) N
        hβ hw jξ σξ hσξ] at hNfinite
    have hsum2 : ∑ e : SquareZeroBond (2 * L),
        (toIcoMod Real.two_pi_pos (-Real.pi)
            ((squareZero (2 * L)).grad σξ e) ^ 2 + θ e ^ 2) = Q + E := by
      rw [Finset.sum_add_distrib, hθsum]
    have hexp : Real.exp (-((B β)⁻¹ * ∑ e, θ e ^ 2) -
        ε (B β) * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi)
          ((squareZero (2 * L)).grad σξ e) ^ 2 + θ e ^ 2)) = Real.exp (-Rε) := by
      rw [hθsum, hsum2]
      dsimp [Rε]
      congr 1; ring
    rw [hexp] at hNfinite
    have hscaled : (2 * Real.pi) ^
        (Fintype.card (SquareFreeVertex (2 * L)) + 1) *
          (Real.exp (-Rε) * (P₀ N).re) ≤
        (2 * Real.pi) ^ (Fintype.card (SquareFreeVertex (2 * L)) + 1) *
          (P₁ N).re := by
      convert hNfinite using 1; ring
    exact le_of_mul_le_mul_left hscaled hscalePos
  have hlim₀ : Tendsto (fun N => (P₀ N).re) atTop
      (𝓝 (∑' h : RotatorFaceHeight (2 * L),
        gaussianVillainHeightWeight (2 * L) β h)) := by
    have h := (Complex.continuous_re.tendsto _).comp
      (villainPinnedGaussianCombCutoffPairing_tendsto_unmarked
        (L := 2 * L) hβ)
    simpa only [Function.comp_def, P₀, ← Complex.ofReal_tsum,
      Complex.ofReal_re] using h
  have hlim₁ : Tendsto (fun N => (P₁ N).re) atTop
      (𝓝 (∑' h : RotatorFaceHeight (2 * L),
        gaussianVillainMarkedHeightWeight (2 * L) β (fun e => ξ * j e) h)) := by
    have h := (Complex.continuous_re.tendsto _).comp
      (villainPinnedGaussianCombCutoffPairing_tendsto (L := 2 * L) hβ
        (fun e => ξ * j e))
    simpa only [Function.comp_def, P₁, ← Complex.ofReal_tsum,
      Complex.ofReal_re] using h
  let Z : ℝ := ∑' h : RotatorFaceHeight (2 * L),
    gaussianVillainHeightWeight (2 * L) β h
  let M : ℝ := ∑' h : RotatorFaceHeight (2 * L),
    gaussianVillainMarkedHeightWeight (2 * L) β (fun e => ξ * j e) h
  have hZpos : 0 < Z := by
    exact gaussianVillainHeightPartitionSum_pos (L := 2 * L) (β := β) hβ
  have hratio : Real.exp (-Rε) * Z ≤ M := by
    exact le_of_tendsto_of_tendsto (hlim₀.const_mul _) hlim₁
      (eventually_atTop.mpr ⟨1, fun N hN => hcut N hN⟩)
  have hchar := villainFrequencyCharacterExpectation_eq_gaussianHeightRatio
    (L := 2 * L) β hβ (boxSite L v) (boxSite L u) hne ξ j hsource
  have hratioReal :
      (villainFrequencyCharacterExpectation (rotatorFreeGraph (2 * L))
        (boxSite L v) β ⟨boxSite L u, hne⟩ ξ).re =
          (∑' h : RotatorFaceHeight (2 * L),
            gaussianVillainMarkedHeightWeight (2 * L) β (fun e => ξ * j e) h) / Z := by
    rw [hchar]
    simp only [Complex.div_ofReal_re, Complex.ofReal_re, Z]
  have hcos : (villainModel β hβ).twoPoint ξ (freeBox L) u v = M / Z := by
    rw [villainModel_twoPoint_eq_rootedFrequency_box L β hβ ξ u v hu hv huv]
    exact hratioReal
  have hfiniteBound : Real.exp (-(p β * E)) ≤
      (villainModel β hβ).twoPoint ξ (freeBox L) u v := by
    rw [hcos, le_div_iff₀ hZpos]
    calc
      Real.exp (-(p β * E)) * Z ≤ Real.exp (-Rε) * Z :=
        mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by linarith [hRle])) hZpos.le
      _ ≤ M := hratio
  have hEbaseBound : Ebase ≤ C₀ * (1 + Real.log (1 + (R : ℝ))) := by
    simpa only [hR] using hEharm
  have hEbound : E ≤ (ξ : ℝ) ^ 2 *
      (C₀ * (1 + Real.log (1 + (R : ℝ)))) := by
    rw [hEscale]
    exact mul_le_mul_of_nonneg_left hEbaseBound (sq_nonneg (ξ : ℝ))
  have hcoef : 0 ≤ (p β * C₀) * (ξ : ℝ) ^ 2 := by positivity
  have hExpOrder :
      -((p β * C₀) * ((ξ : ℝ) ^ 2 *
        (1 + Real.log (1 + (R : ℝ))))) ≤ -(p β * E) := by
    have hle : p β * E ≤ (p β * C₀) * ((ξ : ℝ) ^ 2 *
        (1 + Real.log (1 + (R : ℝ)))) := by
      calc
        p β * E ≤ p β * ((ξ : ℝ) ^ 2 *
            (C₀ * (1 + Real.log (1 + (R : ℝ)))) ) :=
          mul_le_mul_of_nonneg_left hEbound hpNonneg
        _ = (p β * C₀) * ((ξ : ℝ) ^ 2 *
            (1 + Real.log (1 + (R : ℝ)))) := by ring
    exact neg_le_neg hle
  exact le_trans (Real.exp_le_exp.mpr hExpOrder) hfiniteBound

end FroehlichSpencer.BKT.Clock.VillainClock

end
