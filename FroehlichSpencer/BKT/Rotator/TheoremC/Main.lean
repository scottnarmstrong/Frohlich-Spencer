/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.TheoremC.FiniteBound
public import FroehlichSpencer.BKT.Rotator.TheoremC.BesselNumbers
public import FroehlichSpencer.BKT.Rotator.TheoremC.HarmonicField
public import FroehlichSpencer.BKT.Rotator.Transition.KTTransition

/-!
# FS81 Theorem C for the plane rotator, conditional on the pinned charge layer

`⟨cos(ξ(θ_u − θ_v))⟩(β) ≥ A (1 + |u − v|)^{−ξ²/(2πβ′(β))}`,  `β′(β) → ∞`, `β′ > 1/(4π)`,

for the infinite-volume free-boundary two-point function `freeTwoPointLimit` (Ginibre).

Here it is
proved **conditional only on `PinnedLayerHypothesis`** (the FS81 Appendix D charge layer on the
augmented pinned carrier, `Rotator/TheoremC/Hypothesis.lean`), with `|u − v|` the `ℓ¹` distance.

* `freeTwoPointLimit_ge_of_pinnedLayer`: the explicit bound
  `exp(−(C/β + 2ε(β)) ξ² C₀ (1 + log(1 + |u − v|₁)))`, from the finite-volume bound
  (`integral_cos_ge_of_witnesses`) on the boxes `{0, …, 2L}²` centred at `(L, L)`, the explicit
  harmonic field of logarithmic energy (`exists_harmonicField`, the arbitrary-endpoint path adapter
  of the charge-layer construction), the Bessel weight bounds (`exists_besselWeightψ`), the T1.5-NG numbers
  (`exists_besselNumbers`), and the Ginibre limit (`tendsto_integral_rotatorSpinCharacter`).
* `theoremC_of_pinnedLayer`: the source form, with `β′(β) = 1/(2π (C/β + 2ε(β)) C₀) → ∞`.
* `hasPowerLawLowerBound_of_pinnedLayer` and `exists_transition_of_pinnedLayer`: the Kosterlitz–
  Thouless transition (`Transition.exists_transition_of_powerLaw`) conditional on the same
  hypothesis.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.TheoremC

open MeasureTheory Filter Topology
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Rotator.Transition
open FroehlichSpencer.BKT.Villain

/-! ## Scaling the mark by `ξ` -/

theorem rotatorCurrentDivergence_intMul {L : ℕ} (ξ : ℤ) (j : RotatorInternalBond L → ℤ)
    (v : RotatorSpinSite L) :
    rotatorCurrentDivergence (fun e => ξ * j e) v = ξ * rotatorCurrentDivergence j v := by
  unfold rotatorCurrentDivergence currentDivergence
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun e _ => ?_ <;> split_ifs <;> simp

theorem rotatorTwoPointFrequency_intMul {L : ℕ} (a x : RotatorSpinSite L) (ξ : ℤ)
    (v : RotatorSpinSite L) :
    rotatorTwoPointFrequency a x ξ v = ξ * rotatorTwoPointFrequency a x 1 v := by
  unfold rotatorTwoPointFrequency
  split_ifs <;> ring

theorem sum_sq_intMul {L : ℕ} (ξ : ℤ) (j : RotatorInternalBond L → ℤ)
    (σ : RotatorDualFace L → ℝ) :
    ∑ e, (2 * Real.pi * (((fun e => ξ * j e) e : ℤ) : ℝ) +
        (rotatorDualGraph L).grad (fun f => (ξ : ℝ) * σ f) e) ^ 2 =
      (ξ : ℝ) ^ 2 * ∑ e, (2 * Real.pi * (j e : ℝ) + (rotatorDualGraph L).grad σ e) ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Multigraph.grad]
  push_cast
  ring

/-! ## The centred boxes -/

theorem coe_boxSite_fst {L : ℕ} {z : ℤ × ℤ} (h : boxRadius z ≤ L) :
    (((boxSite L z).1 : ℕ) : ℤ) = z.1 + L := by
  have := congrArg Prod.fst (siteToZ_boxSite h)
  simpa [siteToZ] using this

theorem coe_boxSite_snd {L : ℕ} {z : ℤ × ℤ} (h : boxRadius z ≤ L) :
    (((boxSite L z).2 : ℕ) : ℤ) = z.2 + L := by
  have := congrArg Prod.snd (siteToZ_boxSite h)
  simpa [siteToZ] using this

theorem siteL1_boxSite {L : ℕ} {u v : ℤ × ℤ} (hu : boxRadius u ≤ L) (hv : boxRadius v ≤ L) :
    siteL1 (boxSite L u) (boxSite L v) = l1Norm (u - v) := by
  unfold siteL1 l1Norm
  rw [coe_boxSite_fst hu, coe_boxSite_fst hv, coe_boxSite_snd hu, coe_boxSite_snd hv]
  simp only [Prod.fst_sub, Prod.snd_sub]
  congr 1 <;> congr 1 <;> ring

/-! ## The infinite-volume bound -/

/-- **FS81 Theorem C, explicit form, conditional on the pinned charge layer.** -/
theorem freeTwoPointLimit_ge_of_pinnedLayer (hyp : PinnedLayerHypothesis) :
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
  have hfin := integral_cos_ge_of_witnesses hK₀ hK₁ hD₁ hKv (le_trans hβH hβH') hC hw hnz hlog
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

/-- **FS81 Theorem C (with the harmonics (6.1)), conditional on the pinned charge layer.** For `β`
large, `⟨cos(ξ(θ_u − θ_v))⟩(β) ≥ e^{−ξ²/(2πβ′)} (1 + |u − v|₁)^{−ξ²/(2πβ′)}` with
`β′(β) > 1/(4π)` and `β′(β) → ∞`. -/
theorem theoremC_of_pinnedLayer (hyp : PinnedLayerHypothesis) :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ), Tendsto β' atTop atTop ∧
      ∀ β (hβ : 0 ≤ β), β₀ ≤ β → 1 / (4 * Real.pi) < β' β ∧
        ∀ (ξ : ℤ) (u v : ℤ × ℤ),
          Real.exp (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) *
              ((l1Norm (u - v) : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) ≤
            freeTwoPointLimit β hβ ξ u v := by
  obtain ⟨β₀, C₀, C, ε, hβ₀, hC₀, hC, hεlim, hbound⟩ := freeTwoPointLimit_ge_of_pinnedLayer hyp
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
layer. -/
theorem hasPowerLawLowerBound_of_pinnedLayer (hyp : PinnedLayerHypothesis) :
    ∃ β₀ : ℝ, ∀ β (hβ : 0 ≤ β), β₀ ≤ β → HasPowerLawLowerBound β hβ := by
  obtain ⟨β₀, β', -, h⟩ := theoremC_of_pinnedLayer hyp
  refine ⟨β₀, fun β hβ hβ₀ => ?_⟩
  obtain ⟨-, hb⟩ := h β hβ hβ₀
  refine ⟨Real.exp (-((1 : ℤ) : ℝ) ^ 2 / (2 * Real.pi * β' β)), ((1 : ℤ) : ℝ) ^ 2 /
    (2 * Real.pi * β' β), Real.exp_pos _, fun u v => ?_⟩
  have := hb 1 u v
  simpa [neg_div] using this

/-- **The Kosterlitz–Thouless transition of the plane rotator, conditional on the pinned charge
layer**: a single `β_c ≥ 1/2` with exponential decay for `β < β_c` and, for `β > β_c`, neither
exponential decay nor long-range order. -/
theorem exists_transition_of_pinnedLayer (hyp : PinnedLayerHypothesis) :
    ∃ βc : ℝ, 1 / 2 ≤ βc ∧ (∀ β (hβ : 0 ≤ β), β < βc → HasExpDecay β hβ) ∧
      (∀ β (hβ : 0 ≤ β), βc < β → ¬ HasExpDecay β hβ ∧ HasNoLongRangeOrder β hβ) :=
  exists_transition_of_powerLaw (hasPowerLawLowerBound_of_pinnedLayer hyp)

end FroehlichSpencer.BKT.Rotator.TheoremC

end
