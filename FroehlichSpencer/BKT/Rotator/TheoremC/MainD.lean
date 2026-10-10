/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Rooted.MomentD
public import FroehlichSpencer.BKT.Rotator.TheoremC.Main

/-!
# FS81 Theorem C under the weaker pinned-layer hypothesis (D-form)

the rooted charge layer's `PinnedLayerHypothesis`
(`Rotator/TheoremC/Hypothesis.lean`) asks for a `RootedChargeLayer` on `squareZero L`, whose waves
carry spin-wave construction's graph-ball constancy relative to the whole ensemble.

On the wired carrier these clauses
exclude configurations FS81 Appendix D needs (`Generic/Wired/Obstructions.lean`, boundary geometry).

This module
replaces the layer by a `RootedChargeLayerD` (`Generic/Rooted/LayerD.lean`: waves as data,
cross-density gradient disjointness and orthogonality stated directly):

* `PinnedLayerWitnessD`, `PinnedLayerHypothesisD`: the D-form of the rooted charge layer hypothesis;
* `pinnedLayerHypothesisD_of_pinnedLayerHypothesis`: the rooted charge layer hypothesis implies it (so it is
  strictly weaker);
* `integral_cos_ge_of_witnessesD`, `freeTwoPointLimit_ge_of_pinnedLayerD`,
  `theoremC_of_pinnedLayerD`, `hasPowerLawLowerBound_of_pinnedLayerD`,
  `exists_transition_of_pinnedLayerD`: FS81 Theorem C (with the harmonics (6.1)) and the
  Kosterlitz–Thouless transition, conditional only on `PinnedLayerHypothesisD`.

The proofs are
  those of the rooted charge layer with `integral_shift_ge_of_rootedLayerD`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.TheoremC

open MeasureTheory Filter Topology Complex
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Rotator.Transition
open FroehlichSpencer.BKT.Villain

/-- The Appendix D data on one augmented box at comb cutoff `N`, D-form. -/
structure PinnedLayerWitnessD (L N : ℕ) (D₁ D₂ α K₀ K₁ Kv a₁ a₂ : ℝ) (Kov : ℕ) where
  /-- The density centers. -/
  centerOf : (RotatorDualFace L → ℤ) → RotatorDualFace L
  /-- The cover cost `A(ϱ)`. -/
  A : (RotatorDualFace L → ℤ) → ℝ
  /-- The entropy factor `Z(ϱ)`. -/
  Zent : (RotatorDualFace L → ℤ) → ℝ
  /-- The rooted charge layer of the root-relative comb, D-form. -/
  layer : RootedChargeLayerD (squareZero L) none (pinnedCombLam L N) centerOf A Zent
    D₁ D₂ α K₀ K₁
  /-- The density sizes. -/
  dsc : (RotatorDualFace L → ℤ) → ℕ
  /-- The local geometry. -/
  isLocal : layer.IsLocal dsc Kv Kov
  /-- The exponential entropy bound. -/
  entropy_exp : ∀ ϱ : RotatorDualFace L → ℤ,
    Zent ϱ ≤ Real.exp (a₁ * ∑ j, |(ϱ j : ℝ)| + a₂ * A ϱ)

/-- **The pinned charge-layer hypothesis, D-form.** -/
def PinnedLayerHypothesisD : Prop :=
  ∃ (D₁ D₂ α K₀ K₁ Kv a₁ a₂ : ℝ) (Kov L₀ : ℕ),
    1 < α ∧ 0 < K₀ ∧ 0 < K₁ ∧ 0 < D₁ ∧ 0 ≤ Kv ∧
    ∀ L : ℕ, L₀ ≤ L → ∀ N : ℕ, 1 ≤ N →
      Nonempty (PinnedLayerWitnessD L N D₁ D₂ α K₀ K₁ Kv a₁ a₂ Kov)

/-- A the rooted charge layer witness is a D-form witness. -/
def PinnedLayerWitness.toD {L N : ℕ} {D₁ D₂ α K₀ K₁ Kv a₁ a₂ : ℝ} {Kov : ℕ}
    (W : PinnedLayerWitness L N D₁ D₂ α K₀ K₁ Kv a₁ a₂ Kov) :
    PinnedLayerWitnessD L N D₁ D₂ α K₀ K₁ Kv a₁ a₂ Kov where
  centerOf := W.centerOf
  A := W.A
  Zent := W.Zent
  layer := W.layer.toD
  dsc := W.dsc
  isLocal := W.isLocal.toD
  entropy_exp := W.entropy_exp

/-- **The D-form hypothesis is weaker than the rooted charge layer hypothesis.** -/
theorem pinnedLayerHypothesisD_of_pinnedLayerHypothesis :
    PinnedLayerHypothesis → PinnedLayerHypothesisD := by
  rintro ⟨D₁, D₂, α, K₀, K₁, Kv, a₁, a₂, Kov, L₀, hα, hK₀, hK₁, hD₁, hKv, h⟩
  exact ⟨D₁, D₂, α, K₀, K₁, Kv, a₁, a₂, Kov, L₀, hα, hK₀, hK₁, hD₁, hKv,
    fun L hL N hN => (h L hL N hN).map PinnedLayerWitness.toD⟩

/-- **The finite-volume lower bound** (D-form). Given pinned-layer witnesses on the box for every
comb cutoff, the Bessel-weight bounds at `β` and the T1.5-NG numbers, the internal two-point
function is at least `exp(−(C/β + 2ε) ∑_e (2πj + ∇σ)²)`. -/
theorem integral_cos_ge_of_witnessesD {D₁ D₂ α K₀ K₁ Kv a₁ a₂ : ℝ} {Kov : ℕ}
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
    (hwit : ∀ N : ℕ, 1 ≤ N → Nonempty (PinnedLayerWitnessD L N D₁ D₂ α K₀ K₁ Kv a₁ a₂ Kov))
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
    have h := integral_shift_ge_of_rootedLayerD (squareZero_connected L hL) none Wt.layer
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

/-- **FS81 Theorem C, explicit form, conditional on the pinned charge layer (D-form).** -/
theorem freeTwoPointLimit_ge_of_pinnedLayerD (hyp : PinnedLayerHypothesisD) :
    ∃ (β₀ C₀ C : ℝ) (ε : ℝ → ℝ), 1 ≤ β₀ ∧ 0 < C₀ ∧ 0 < C ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ β (hβ : 0 ≤ β), β₀ ≤ β → 0 ≤ ε β ∧ ∀ (ξ : ℤ) (u v : ℤ × ℤ),
        Real.exp (-((C / β + 2 * ε β) *
          ((ξ : ℝ) ^ 2 * (C₀ * (1 + Real.log (1 + (l1Norm (u - v) : ℝ))))))) ≤
          freeTwoPointLimit β hβ ξ u v := by
  obtain ⟨D₁, D₂, α, K₀, K₁, Kv, a₁, a₂, Kov, L₀, hα, hK₀, hK₁, hD₁, hKv, hwit⟩ := hyp
  obtain ⟨βH, C, hβH, hC, hH⟩ := exists_besselWeightψ
  obtain ⟨βK, amp, b, ε, k₀, hβK, hεlim, hK⟩ := exists_besselNumbers (D₂ := D₂) (a₁ := a₁)
    (a₂ := a₂) Kov hα hK₀ hK₁ hD₁ hKv hC
  obtain ⟨C₀, hC₀, hJ⟩ := exists_harmonicField
  refine ⟨max βH βK, C₀, C, ε, le_trans hβH (le_max_left _ _), hC₀, hC, hεlim,
    fun β hβ0 hβ => ?_⟩
  have hβH' : βH ≤ β := le_trans (le_max_left _ _) hβ
  have hβK' : βK ≤ β := le_trans (le_max_right _ _) hβ
  obtain ⟨hw, hnz, hlog, hcurv, hcost⟩ := hH β hβH'
  obtain ⟨hamp, hampW, hk₀, hexp, hquad₁, hquad₂, hM, hb8, hb₁, hb₂, hε0, hthr⟩ := hK β hβK'
  refine ⟨hε0, fun ξ u v => ?_⟩
  have hlim := tendsto_integral_rotatorSpinCharacter hβ0 ξ u v
  have hlimre : Tendsto (fun L : ℕ => ∫ θ, Real.cos (ξ * (θ (boxSite L u) - θ (boxSite L v)))
      ∂rotatorMeasureInternal (2 * L) β) atTop (𝓝 (freeTwoPointLimit β hβ0 ξ u v)) := by
    have h := (Complex.continuous_re.tendsto _).comp hlim
    simpa only [Function.comp_def, integral_rotatorSpinCharacter, Complex.ofReal_re] using h
  set R := l1Norm (u - v) with hRdef
  refine ge_of_tendsto hlimre (eventually_atTop.mpr ⟨R + boxRadius u + boxRadius v + L₀ + 2,
    fun L hL => ?_⟩)
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
  obtain ⟨j, σ, hj, hσ, hE⟩ := hJ (2 * L) (boxSite L u) (boxSite L v)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hfin := integral_cos_ge_of_witnessesD hK₀ hK₁ hD₁ hKv (le_trans hβH hβH') hC hw hnz hlog
    hcurv hcost hamp hampW hk₀ hexp hquad₁ hquad₂ hM hb8 hb₁ hb₂ hε0 hthr (L := 2 * L)
    (by omega) (fun N hN => hwit (2 * L) (by omega) N hN) (boxSite L u) (boxSite L v) ξ
    (fun e => ξ * j e) (fun f => (ξ : ℝ) * σ f)
    (fun w => by rw [rotatorCurrentDivergence_intMul, hj, rotatorTwoPointFrequency_intMul _ _ ξ])
    (by rw [hσ, mul_zero])
  rw [sum_sq_intMul] at hfin
  refine le_trans (Real.exp_le_exp.mpr ?_) hfin
  rw [hR] at hE
  have hp : 0 ≤ C / β + 2 * ε β := by
    have : 0 < C / β := div_pos hC (lt_of_lt_of_le one_pos (le_trans hβH hβH'))
    linarith
  refine neg_le_neg (mul_le_mul_of_nonneg_left ?_ hp)
  exact mul_le_mul_of_nonneg_left hE (sq_nonneg _)

/-- **FS81 Theorem C (with the harmonics (6.1)), conditional on the pinned charge layer
(D-form).** For `β` large,
`⟨cos(ξ(θ_u − θ_v))⟩(β) ≥ e^{−ξ²/(2πβ′)} (1 + |u − v|₁)^{−ξ²/(2πβ′)}` with `β′(β) > 1/(4π)` and
`β′(β) → ∞`. -/
theorem theoremC_of_pinnedLayerD (hyp : PinnedLayerHypothesisD) :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ), Tendsto β' atTop atTop ∧
      ∀ β (hβ : 0 ≤ β), β₀ ≤ β → 1 / (4 * Real.pi) < β' β ∧
        ∀ (ξ : ℤ) (u v : ℤ × ℤ),
          Real.exp (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) *
              ((l1Norm (u - v) : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) ≤
            freeTwoPointLimit β hβ ξ u v := by
  obtain ⟨β₀, C₀, C, ε, hβ₀, hC₀, hC, hεlim, hbound⟩ := freeTwoPointLimit_ge_of_pinnedLayerD hyp
  set p : ℝ → ℝ := fun β => (C / β + 2 * ε β) * C₀ with hp
  have hplim : Tendsto p atTop (𝓝 0) := by
    have h1 : Tendsto (fun β : ℝ => C / β) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul C
    have h2 := (h1.add (hεlim.const_mul 2)).mul_const C₀
    simpa [hp] using h2
  have hppos : ∀ β, β₀ ≤ β → 0 < p β := fun β hβ => by
    have hβ0 : 0 ≤ β := le_trans zero_le_one (le_trans hβ₀ hβ)
    have hε := (hbound β hβ0 hβ).1
    have : 0 < C / β := div_pos hC (lt_of_lt_of_le one_pos (le_trans hβ₀ hβ))
    exact mul_pos (by linarith) hC₀
  obtain ⟨β₁, hβ₁⟩ :=
    eventually_atTop.mp (hplim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 2)))
  set β' : ℝ → ℝ := fun β => 1 / (2 * Real.pi * p β) with hβ'
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨max β₀ β₁, β', ?_, fun β hβ0 hβ => ⟨?_, fun ξ u v => ?_⟩⟩
  · -- `β′ → ∞`
    have hpw : Tendsto p atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hplim, eventually_atTop.mpr ⟨β₀, fun β hβ => hppos β hβ⟩⟩
    have h := (tendsto_inv_nhdsGT_zero.comp hpw).const_mul_atTop (inv_pos.mpr (by positivity :
      (0 : ℝ) < 2 * Real.pi))
    refine h.congr fun β => ?_
    simp only [hβ', Function.comp_apply]
    field_simp
  · have hpβ := hppos β (le_trans (le_max_left _ _) hβ)
    have hp2 : p β < 2 := hβ₁ β (le_trans (le_max_right _ _) hβ)
    simp only [hβ']
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · have hβ₀' : β₀ ≤ β := le_trans (le_max_left _ _) hβ
    have hpβ := hppos β hβ₀'
    have hkey : (ξ : ℝ) ^ 2 / (2 * Real.pi * β' β) = (ξ : ℝ) ^ 2 * p β := by
      simp only [hβ']
      field_simp
    rw [hkey]
    have hR : (0 : ℝ) < (l1Norm (u - v) : ℝ) + 1 := by positivity
    rw [Real.rpow_def_of_pos hR, ← Real.exp_add]
    refine le_trans (Real.exp_le_exp.mpr (le_of_eq ?_)) ((hbound β hβ0 hβ₀').2 ξ u v)
    simp only [hp]
    rw [add_comm (1 : ℝ) ((l1Norm (u - v) : ℝ))]
    ring

/-- The power-law lower bound of `Transition.KTTransition`, conditional on the pinned charge
layer (D-form). -/
theorem hasPowerLawLowerBound_of_pinnedLayerD (hyp : PinnedLayerHypothesisD) :
    ∃ β₀ : ℝ, ∀ β (hβ : 0 ≤ β), β₀ ≤ β → HasPowerLawLowerBound β hβ := by
  obtain ⟨β₀, β', -, h⟩ := theoremC_of_pinnedLayerD hyp
  refine ⟨β₀, fun β hβ hβ₀ => ?_⟩
  obtain ⟨-, hb⟩ := h β hβ hβ₀
  refine ⟨Real.exp (-((1 : ℤ) : ℝ) ^ 2 / (2 * Real.pi * β' β)), ((1 : ℤ) : ℝ) ^ 2 /
    (2 * Real.pi * β' β), Real.exp_pos _, fun u v => ?_⟩
  have := hb 1 u v
  simpa [neg_div] using this

/-- **The Kosterlitz–Thouless transition of the plane rotator, conditional on the pinned charge
layer (D-form)**: a single `β_c ≥ 1/2` with exponential decay for `β < β_c` and, for `β > β_c`,
neither exponential decay nor long-range order. -/
theorem exists_transition_of_pinnedLayerD (hyp : PinnedLayerHypothesisD) :
    ∃ βc : ℝ, 1 / 2 ≤ βc ∧ (∀ β (hβ : 0 ≤ β), β < βc → HasExpDecay β hβ) ∧
      (∀ β (hβ : 0 ≤ β), βc < β → ¬ HasExpDecay β hβ ∧ HasNoLongRangeOrder β hβ) :=
  exists_transition_of_powerLaw (hasPowerLawLowerBound_of_pinnedLayerD hyp)

end FroehlichSpencer.BKT.Rotator.TheoremC

end
