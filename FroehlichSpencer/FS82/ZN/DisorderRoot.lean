/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.ZN.DisorderTransport

/-!
# the finite-box disorder perimeter root (3.54) on centred cubes

`fs82_zn_disorder_perimeter_root`: there is a universal constant `C` such that for every `β > 0`
there is a threshold `N₀(β)` with

`exp(−C β (ξ/N)² (L + T)) ≤ ⟨D^ξ_{L×T}⟩_{cube M}(β, h)`

for all `N ≥ N₀(β)`, all twists `1 ≤ ξ < N`, all `L, T ≥ 1`, all centred cubes `cube M` with
`M ≥ max(L, T)`, all `0 ≤ h < ∞`, and for the `ℤ_N` endpoint `h = ∞`.

The constant is `C = 12π² + 2`.

The threshold depends on `β` only: it does not depend on
`h`, the box, `L`, `T` or `ξ`.

The printed lower bound (3.53) is replaced by a perimeter upper bound.
The proof of (3.54) uses the upper bound `‖ε‖² ≤ 24π² (ξ/N)² (L+T)` on the
source residual, in place of the printed lower bound (3.53).
-/

open scoped BigOperators
open Filter Topology
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.ZN.Renormalization

@[expose] public section

namespace FroehlichSpencer.FS82.ZN

noncomputable section

/-- The universal constant of the disorder perimeter bound. -/
def znDisorderConstant : ℝ := 12 * Real.pi ^ 2 + 2

theorem znDisorderConstant_pos : 0 < znDisorderConstant := by
  unfold znDisorderConstant
  positivity

theorem znStateError_eq (β : ℝ) (N : ℕ) :
    znStateError β N = 12 * Real.pi ^ 2 * β +
      (72 * znPackingCoefficient (znActivityRate β N) N +
        168 * Real.pi ^ 2 * (6 * β * (Real.exp 1 - 1) + 72 * β ^ 2 * (Real.exp 1 - 1) ^ 2) *
          Real.exp (-(znActivityRate β N))) := by
  unfold znStateError
  ring

theorem tendsto_exp_neg_znActivityRate (β : ℝ) :
    Tendsto (fun N : ℕ => Real.exp (-(znActivityRate β N))) atTop (𝓝 0) := by
  have hrate : Tendsto (fun N : ℕ => znActivityRate β N) atTop atTop := by
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) / 36) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const (by norm_num)
    have h2 := tendsto_atTop_add_const_right atTop
      (-((1 + (sourceKLengthCoefficient + 6 * β * (Real.cosh 1 - 1))) / 2)) h1
    refine h2.congr fun N => ?_
    rw [znActivityRate_eq]
    ring
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hrate

/-- **The threshold.** For `β > 0` and all large `N` the rate is at least `11` and the error
coefficient of one ensemble is at most `(12π² + 2) β`. -/
theorem exists_znDisorderThreshold {β : ℝ} (hβ : 0 < β) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N ∧ 11 ≤ znActivityRate β N ∧
      znStateError β N ≤ znDisorderConstant * β := by
  have hpi := Real.pi_pos
  have h1 : ∀ᶠ N : ℕ in atTop, znRateThreshold β ≤ (N : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  have h2 : ∀ᶠ N : ℕ in atTop, 72 * znPackingCoefficient (znActivityRate β N) N < β := by
    have ht := (tendsto_znPackingCoefficient β).const_mul 72
    rw [mul_zero] at ht
    exact ht.eventually (gt_mem_nhds hβ)
  have h3 : ∀ᶠ N : ℕ in atTop,
      168 * Real.pi ^ 2 * (6 * β * (Real.exp 1 - 1) + 72 * β ^ 2 * (Real.exp 1 - 1) ^ 2) *
        Real.exp (-(znActivityRate β N)) < β := by
    have ht := (tendsto_exp_neg_znActivityRate β).const_mul
      (168 * Real.pi ^ 2 * (6 * β * (Real.exp 1 - 1) + 72 * β ^ 2 * (Real.exp 1 - 1) ^ 2))
    rw [mul_zero] at ht
    exact ht.eventually (gt_mem_nhds hβ)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (h1.and (h2.and h3))
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  obtain ⟨hr, hD, hE⟩ := hN₀ N ((le_max_left _ _).trans hN)
  refine ⟨lt_of_lt_of_le Nat.zero_lt_one ((le_max_right _ _).trans hN),
    eleven_le_znActivityRate hr, ?_⟩
  rw [znStateError_eq]
  unfold znDisorderConstant
  linarith

/-- **FS82 (3.54) at finite `h`**, with the threshold of `exists_znDisorderThreshold`. -/
theorem finiteCenteredDisorderExpectation_perimeter {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N)
    (ha : 11 ≤ znActivityRate β N) (hErr : znStateError β N ≤ znDisorderConstant * β)
    {ξ : ℕ} (hξ : 1 ≤ ξ) {L T M : ℕ} (hL1 : 1 ≤ L) (hT1 : 1 ≤ T) (hL : L ≤ M) (hT : T ≤ M)
    (hbox : 0 < M) (h : NNReal) :
    Real.exp (-(znDisorderConstant * β * ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T))) ≤
      finiteCenteredDisorderExpectation β N ξ L T M h hL hT hbox := by
  refine le_trans (Real.exp_le_exp.mpr ?_)
    (finiteCenteredDisorderExpectation_ge hL1 hT1 hL hT hbox hN hξ hβ.le ha h)
  have hnn : 0 ≤ ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hErr hnn]

/-- **The finite-box disorder perimeter root, FS82 (3.54) on centred cubes.** -/
theorem fs82_zn_disorder_perimeter_root :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 < β → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ ξ : ℕ, 1 ≤ ξ → ξ < N → ∀ L T : ℕ, 1 ≤ L → 1 ≤ T →
        ∀ (M : ℕ) (hL : L ≤ M) (hT : T ≤ M) (hbox : 0 < M),
          (∀ h : NNReal,
            Real.exp (-(C * β * ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T))) ≤
              finiteCenteredDisorderExpectation β N ξ L T M h hL hT hbox) ∧
          Real.exp (-(C * β * ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T))) ≤
            discreteCenteredDisorderExpectation β N ξ L T M hL hT hbox := by
  refine ⟨znDisorderConstant, znDisorderConstant_pos, fun β hβ => ?_⟩
  obtain ⟨N₀, hN₀⟩ := exists_znDisorderThreshold hβ
  refine ⟨N₀, fun N hN ξ hξ _ L T hL1 hT1 M hL hT hbox => ?_⟩
  obtain ⟨hNpos, ha, hErr⟩ := hN₀ N hN
  have hfin : ∀ h : NNReal,
      Real.exp (-(znDisorderConstant * β * ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T))) ≤
        finiteCenteredDisorderExpectation β N ξ L T M h hL hT hbox := fun h =>
    finiteCenteredDisorderExpectation_perimeter hβ hNpos ha hErr hξ hL1 hT1 hL hT hbox h
  exact ⟨hfin, ge_of_tendsto' (tendsto_finiteCenteredDisorderExpectation β hNpos hL hT hbox) hfin⟩

end

end FroehlichSpencer.FS82.ZN

end
