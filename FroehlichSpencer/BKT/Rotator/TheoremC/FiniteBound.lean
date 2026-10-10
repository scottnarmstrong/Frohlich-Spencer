/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.TheoremC.Hypothesis
public import FroehlichSpencer.BKT.Generic.Rooted.Moment
public import FroehlichSpencer.BKT.Rotator.TheoremC.BesselWeight
public import FroehlichSpencer.BKT.Rotator.TheoremC.MarkedComb
public import FroehlichSpencer.BKT.Rotator.TheoremC.PinnedAdapter
public import FroehlichSpencer.BKT.Rotator.XYDualityFourier
public import FroehlichSpencer.BKT.Rotator.Ginibre.SquareBox

/-!
# The finite-volume lower bound of FS81 Theorem C

On the free spin box `{0, …, L}²` at inverse temperature `β`, for a mark `ξ (δ_a − δ_x)` with an
integer source current `j` (`div j = ξ(δ_a − δ_x)`) and a dual-face correction `σ` (`σ = 0` on the
exterior face), the two-point function of the internal law satisfies

`⟨cos(ξ(θ_a − θ_x))⟩_L(β) ≥ exp(−(C/β + 2ε) ∑_e (2π j(e) + ∇σ(e))²)`

as soon as the pinned layer witnesses exist for every comb cutoff (`integral_cos_ge_of_witnesses`).

1. the T1.5-NG bound for the rooted layer on `squareZero L` (`integral_shift_ge_of_rootedLayer`)
   with the Bessel weight in the angle variable, at the edge field `θ = 2πj + ∇σ` read on
   `squareZero` (`squareZeroField`) and the shift `σ`;
2. the translation `φ ↦ φ − σ` turns the right side into the marked rooted integral, and both
   sides are `(2π)^{L²+1}` times the comb pairings (`integral_offsetEdgeDensity_pinnedComb`);
3. as the cutoff `N → ∞` the pairings converge to the pinned height sums
   (`rotatorPinnedMarkedCombCutoffPairing_tendsto`), whose ratio is the two-point function (FS81
   (1.37), `rotatorMeasureInternal_character_integral_eq_heightRatio_unconditional`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.TheoremC

open MeasureTheory Filter Topology Complex
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Lattice2D

/-! ## The rooted integrals as comb pairings -/

theorem integral_edgeDensity_pinnedComb {L : ℕ} (N : ℕ) {β : ℝ} (hβ : 0 < β)
    {W : ℝ} {c : ℝ → ℝ} (hw : IsStripWeight (besselWeightψ β) W c) :
    ∫ φ : RotatorDualFace L → ℝ,
        edgeDensity (squareZero L) (besselWeightψ β) none φ *
          ∏ k, pinnedCombLam L N k (φ k - φ none) =
      (2 * Real.pi) ^ (Fintype.card (SquareFreeVertex L) + 1) *
        (rotatorPinnedMarkedCombCutoffPairing L β (fun _ => 0) N).re := by
  rw [← integral_offsetEdgeDensity_pinnedComb N hβ (fun _ => 0)]
  refine integral_congr_ae (Eventually.of_forall fun φ => ?_)
  have h0 : (fun e : RotatorInternalBond L => 2 * Real.pi * (((fun _ => (0 : ℤ)) e : ℤ) : ℝ)) =
      0 := by
    funext e; simp
  simp only [h0, offsetEdgeDensity_zero, edgeDensity_squareZero hw]

theorem integral_offsetEdgeDensity_shift_pinnedComb {L : ℕ} (N : ℕ) {β : ℝ} (hβ : 0 < β)
    {W : ℝ} {c : ℝ → ℝ} (hw : IsStripWeight (besselWeightψ β) W c)
    (j : RotatorInternalBond L → ℤ) (σ : RotatorDualFace L → ℝ) (hσ : σ none = 0) :
    ∫ φ : RotatorDualFace L → ℝ,
        offsetEdgeDensity (squareZero L) (besselWeightψ β)
            (squareZeroField L fun e => 2 * Real.pi * (j e : ℝ) + (rotatorDualGraph L).grad σ e)
            none φ *
          ∏ k, pinnedCombLam L N k (φ k + σ k - (φ none + σ none)) =
      (2 * Real.pi) ^ (Fintype.card (SquareFreeVertex L) + 1) *
        (rotatorPinnedMarkedCombCutoffPairing L β j N).re := by
  rw [← integral_offsetEdgeDensity_pinnedComb N hβ j,
    ← integral_sub_right_eq_self _ σ]
  refine integral_congr_ae (Eventually.of_forall fun φ => ?_)
  have hsplit : (squareZeroField L fun e => 2 * Real.pi * (j e : ℝ) +
      (rotatorDualGraph L).grad σ e) =
      squareZeroField L (fun e => 2 * Real.pi * (j e : ℝ)) +
        fun e => (squareZero L).grad σ e := by
    rw [← squareZeroField_grad, ← squareZeroField_add]
    rfl
  have hprod : ∏ k, pinnedCombLam L N k ((φ - σ) k + σ k - ((φ - σ) none + σ none)) =
      ∏ k, pinnedCombLam L N k (φ k - φ none) := by
    refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    simp only [Pi.sub_apply]
    ring
  beta_reduce
  rw [hprod, hsplit, ← offsetEdgeDensity_squareZeroField hw L (fun e => 2 * Real.pi * (j e : ℝ))]
  congr 1
  unfold offsetEdgeDensity
  congr 1
  · refine Finset.prod_congr rfl fun e _ => ?_
    congr 3
    simp only [Multigraph.grad, Pi.sub_apply, Pi.add_apply]
    ring
  · simp only [Pi.sub_apply, hσ, sub_zero]

/-! ## The reduced phases of the correction -/

theorem sum_toIcoMod_grad_sq_le {L : ℕ} (j : RotatorInternalBond L → ℤ)
    (σ : RotatorDualFace L → ℝ) :
    ∑ e, toIcoMod Real.two_pi_pos (-Real.pi) ((squareZero L).grad σ e) ^ 2 ≤
      ∑ e, (2 * Real.pi * (j e : ℝ) + (rotatorDualGraph L).grad σ e) ^ 2 := by
  rw [← sum_sq_squareZeroField L]
  refine Finset.sum_le_sum fun e _ => ?_
  obtain ⟨n, hn⟩ := squareZeroField_eq_add_intMul_or L j e
  have hsplit : (squareZero L).grad σ e =
      squareZeroField L (fun e => 2 * Real.pi * (j e : ℝ) + (rotatorDualGraph L).grad σ e) e -
        n • (2 * Real.pi) := by
    have h1 := congrFun (squareZeroField_grad L σ) e
    have h2 := congrFun (squareZeroField_add L (fun e => 2 * Real.pi * (j e : ℝ))
      (fun e => (rotatorDualGraph L).grad σ e)) e
    simp only [Pi.add_apply] at h2
    rw [zsmul_eq_mul, ← hn, ← h1]
    change _ = squareZeroField L ((fun e => 2 * Real.pi * (j e : ℝ)) +
      fun e => (rotatorDualGraph L).grad σ e) e - _
    rw [h2]
    ring
  rw [hsplit, toIcoMod_sub_zsmul, ← sq_abs (toIcoMod _ _ _)]
  calc |toIcoMod Real.two_pi_pos (-Real.pi) _| ^ 2 ≤ |squareZeroField L
        (fun e => 2 * Real.pi * (j e : ℝ) + (rotatorDualGraph L).grad σ e) e| ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_toIcoMod_le_abs _) 2
    _ = _ := sq_abs _

/-! ## The finite-volume bound -/

/-- **The finite-volume lower bound.** Given pinned-layer witnesses on the box for every comb
cutoff, the Bessel-weight bounds at `β` and the T1.5-NG numbers, the internal two-point function
is at least `exp(−(C/β + 2ε) ∑_e (2πj + ∇σ)²)`. -/
theorem integral_cos_ge_of_witnesses {D₁ D₂ α K₀ K₁ Kv a₁ a₂ : ℝ} {Kov : ℕ}
    (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hD₁ : 0 < D₁) (hKv : 0 ≤ Kv)
    {β C amp b ε : ℝ} {k₀ : ℕ} (hβ : 1 ≤ β) (hC : 0 < C)
    (hw : IsStripWeight (besselWeightψ β) (Real.pi * β) (besselCostψ C β))
    (hnzero : ∀ z : ℂ, |z.im| ≤ Real.pi * β → besselWeightψ β z ≠ 0)
    (hlog : HasLogDerivBounds (besselWeightψ β) (Real.pi * β) (fun u => C / β * Real.exp |u|))
    (hcurv : HasCurvatureBound (besselWeightψ β) (C / β))
    (hcost : IsCostEnvelope (besselCostψ C β) (C / β) (C / β) (Real.pi * β))
    (hamp : 0 ≤ amp) (hampW : amp * K₁ ≤ Real.pi * β) (hk₀ : 1 ≤ k₀)
    (hexp : 100 * 4 ^ k₀ * costMajorant (C / β) (C / β) (amp * K₁) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * (C / β) * K₀))
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁)
    (hM : ∀ u : ℝ, |u| ≤ max (amp * K₁) 1 → C / β * Real.exp |u| ≤ 1)
    (hb8 : Real.log 8 / 2 ≤ b) (hb₁ : b ≤ amp / 8 - a₁) (hb₂ : b ≤ amp / (8 * D₁) - D₂ - a₂)
    (hε : 0 ≤ ε)
    (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      (Kov : ℝ) * (8 * (Kv + 2 * Kv ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
        Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ ε)
    {L : ℕ} (hL : 1 < L)
    (hwit : ∀ N : ℕ, 1 ≤ N → Nonempty (PinnedLayerWitness L N D₁ D₂ α K₀ K₁ Kv a₁ a₂ Kov))
    (a x : RotatorSpinSite L) (ξ : ℤ) (j : RotatorInternalBond L → ℤ)
    (σ : RotatorDualFace L → ℝ)
    (hj : ∀ v, rotatorCurrentDivergence j v = rotatorTwoPointFrequency a x ξ v)
    (hσ : σ none = 0) :
    Real.exp (-((C / β + 2 * ε) *
        ∑ e, (2 * Real.pi * (j e : ℝ) + (rotatorDualGraph L).grad σ e) ^ 2)) ≤
      ∫ θ, Real.cos (ξ * (θ a - θ x)) ∂rotatorMeasureInternal L β := by
  have hβ0 : 0 < β := lt_of_lt_of_le one_pos hβ
  have hW1 : 1 ≤ Real.pi * β := by nlinarith [Real.two_le_pi]
  set θd : RotatorInternalBond L → ℝ :=
    fun e => 2 * Real.pi * (j e : ℝ) + (rotatorDualGraph L).grad σ e with hθd
  set E := ∑ e, θd e ^ 2 with hE
  set θz := squareZeroField L θd with hθz
  set Rx := C / β * ∑ e, θz e ^ 2 +
    ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) ((squareZero L).grad σ e) ^ 2 + θz e ^ 2)
    with hRx
  set P₀ : ℕ → ℂ := fun N => rotatorPinnedMarkedCombCutoffPairing L β (fun _ => 0) N
  set P₁ : ℕ → ℂ := fun N => rotatorPinnedMarkedCombCutoffPairing L β j N
  have hpos : (0 : ℝ) < (2 * Real.pi) ^ (Fintype.card (SquareFreeVertex L) + 1) := by positivity
  -- every cutoff
  have hcut : ∀ N : ℕ, 1 ≤ N → Real.exp (-Rx) * (P₀ N).re ≤ (P₁ N).re := by
    intro N hN
    obtain ⟨Wt⟩ := hwit N hN
    have h := integral_shift_ge_of_rootedLayer (squareZero_connected L hL) none Wt.layer
      Wt.isLocal hKv hw hnzero hlog hcurv hcost (div_pos hC hβ0) hK₀ hK₁ hD₁ hamp hampW hW1
      hk₀ hexp hquad₁ hquad₂ zero_le_one le_rfl hM Wt.entropy_exp hb8 hb₁ hb₂ hthr σ θz
    rw [integral_edgeDensity_pinnedComb N hβ0 hw,
      integral_offsetEdgeDensity_shift_pinnedComb N hβ0 hw j σ hσ] at h
    have hexpeq : Real.exp (-(C / β * ∑ e, θz e ^ 2) - ε * ∑ e,
        (toIcoMod Real.two_pi_pos (-Real.pi) ((squareZero L).grad σ e) ^ 2 + θz e ^ 2)) =
        Real.exp (-Rx) := by
      rw [hRx]; ring_nf
    rw [hexpeq, mul_left_comm] at h
    exact le_of_mul_le_mul_left h hpos
  -- the cutoff limits
  have hlim₀ : Tendsto (fun N => (P₀ N).re) atTop
      (𝓝 (rotatorHeightPartitionFactor L β).re) := by
    have h := rotatorPinnedMarkedCombCutoffPairing_tendsto hβ (L := L) (fun _ => 0)
    have hfac : rotatorHeightMarkedFactor L β (fun _ => 0) = rotatorHeightPartitionFactor L β := by
      simp [rotatorHeightMarkedFactor, rotatorHeightPartitionFactor]
    rw [hfac] at h
    exact (Complex.continuous_re.tendsto _).comp h
  have hlim₁ : Tendsto (fun N => (P₁ N).re) atTop (𝓝 (rotatorHeightMarkedFactor L β j).re) :=
    (Complex.continuous_re.tendsto _).comp (rotatorPinnedMarkedCombCutoffPairing_tendsto hβ j)
  have hratio : Real.exp (-Rx) * (rotatorHeightPartitionFactor L β).re ≤
      (rotatorHeightMarkedFactor L β j).re :=
    le_of_tendsto_of_tendsto (hlim₀.const_mul _) hlim₁
      (eventually_atTop.mpr ⟨1, fun N hN => hcut N hN⟩)
  -- the two-point function is the height ratio
  have hchar := rotatorMeasureInternal_character_integral_eq_heightRatio_unconditional
    (L := L) β a x ξ j hj
  rw [Ginibre.integral_rotatorSpinCharacter] at hchar
  have hZre := rotatorHeightPartitionFactor_re_pos_unconditional (L := L) β
  have hZim := rotatorHeightPartitionFactor_im_zero_unconditional (L := L) β
  have hZ : rotatorHeightPartitionFactor L β = ((rotatorHeightPartitionFactor L β).re : ℂ) :=
    Complex.ext rfl (by rw [hZim, Complex.ofReal_im])
  have hcos : ∫ θ, Real.cos (ξ * (θ a - θ x)) ∂rotatorMeasureInternal L β =
      (rotatorHeightMarkedFactor L β j).re / (rotatorHeightPartitionFactor L β).re := by
    have h := congrArg Complex.re hchar
    rw [Complex.ofReal_re, hZ, Complex.div_ofReal_re] at h
    exact h
  -- the exponent
  have hθz : ∑ e, θz e ^ 2 = E := sum_sq_squareZeroField L θd
  have hgradσ := sum_toIcoMod_grad_sq_le j σ
  have hRxle : Rx ≤ (C / β + 2 * ε) * E := by
    rw [hRx, hθz, Finset.sum_add_distrib, hθz]
    have h1 : ε * (∑ e, toIcoMod Real.two_pi_pos (-Real.pi) ((squareZero L).grad σ e) ^ 2 + E) ≤
        ε * (E + E) := mul_le_mul_of_nonneg_left (by linarith) hε
    linarith
  rw [hcos, le_div_iff₀ hZre]
  calc Real.exp (-((C / β + 2 * ε) * E)) * (rotatorHeightPartitionFactor L β).re
      ≤ Real.exp (-Rx) * (rotatorHeightPartitionFactor L β).re :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hZre.le
    _ ≤ _ := hratio

end FroehlichSpencer.BKT.Rotator.TheoremC

end
