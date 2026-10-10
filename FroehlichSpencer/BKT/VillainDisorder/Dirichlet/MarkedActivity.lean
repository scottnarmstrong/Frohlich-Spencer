/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedBranch
public import FroehlichSpencer.BKT.Generic.Rooted.LayerD
import Mathlib.Tactic

/-!
# Gaussian renormalized activities of the D1 layer

The Gaussian cost `(τ/2)u²` is a cost envelope with `κ = κ' = τ/2` at every width
(`isCostEnvelope_gaussianCost`). Its translation energy is `gffTranslationEnergy`.

* `exists_gaussianActivity_params`: for every target rate `s` there are an amplitude, a top
  scale and a threshold `τ₁` such that the hypotheses of `rootedD_gain` hold for `τ < τ₁`.
* `abs_K_mul_exp_le_of_gaussian`: for a `RootedChargeLayerD` with `Zent = 1`, as in D1's
  witness, every member's renormalized activity is at most `e^{−s A(ϱ)}`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open MeasureTheory FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic

/-! ### The Gaussian cost -/

/-- The Gaussian edge cost `c(u) = (τ/2) u²` of the GFF with parameter `τ`. -/
def gaussianCost (τ : ℝ) : ℝ → ℝ := fun u => τ / 2 * u ^ 2

theorem sq_le_exp_two_pi_mul_abs (u : ℝ) : u ^ 2 ≤ Real.exp (2 * Real.pi * |u|) := by
  have h := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * |u|)
  have hπ : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
  have hu : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  have h2 : |u| ^ 2 ≤ (2 * Real.pi * |u|) ^ 2 / 2 := by
    have : (2 * Real.pi * |u|) ^ 2 / 2 = 2 * Real.pi ^ 2 * |u| ^ 2 := by ring
    rw [this]
    have hπ2 : 1 ≤ Real.pi ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hπ2 (sq_nonneg |u|), sq_nonneg |u|]
  have h3 : 0 ≤ 1 + 2 * Real.pi * |u| := by positivity
  linarith

/-- The Gaussian cost is a cost envelope with `κ = κ' = τ/2`, at every width. -/
theorem isCostEnvelope_gaussianCost {τ : ℝ} (hτ : 0 ≤ τ) (W : ℝ) :
    IsCostEnvelope (gaussianCost τ) (τ / 2) (τ / 2) W where
  even u := by simp [gaussianCost]
  zero := by simp [gaussianCost]
  nonneg_κ := by positivity
  nonneg_κ' := by positivity
  quad u _ := le_refl _
  expo u _ _ := by
    unfold gaussianCost
    exact mul_le_mul_of_nonneg_left (sq_le_exp_two_pi_mul_abs u) (by positivity)

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

theorem translationEnergy_gaussianCost (G : Multigraph V E) (τ : ℝ) (a ρ : V → ℝ) :
    translationEnergy (gaussianCost τ) (gradLinear G) a ρ = gffTranslationEnergy G τ a ρ := by
  unfold translationEnergy gffTranslationEnergy gaussianCost Multigraph.energy
    Multigraph.pairing
  simp only [gradLinear_apply]
  rw [Finset.mul_sum]

/-! ### The amplitude and scale choices -/

/-- **Parameters for the Gaussian renormalized activities**: for every target rate `s` there are
an amplitude, a top scale and a threshold `τ₁` such that for `τ < τ₁` the hypotheses of
`rootedD_gain` hold for the Gaussian cost, and `s ≤ amp/(8D₁) − D₂`. -/
theorem exists_gaussianActivity_params {α K₀ K₁ D₁ D₂ : ℝ} (hα : 1 < α) (hK₀ : 0 < K₀)
    (hK₁ : 0 < K₁) (hD₁ : 0 < D₁) (s : ℝ) :
    ∃ (amp : ℝ) (k₀ : ℕ) (τ₁ : ℝ), 0 ≤ amp ∧ 1 ≤ k₀ ∧ 0 < τ₁ ∧
      s ≤ amp / (8 * D₁) - D₂ ∧
      amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁ ∧
      ∀ τ : ℝ, 0 < τ → τ < τ₁ →
        100 * 4 ^ k₀ * costMajorant (τ / 2) (τ / 2) (amp * K₁) ≤ amp / 2 ∧
        amp ≤ 1 / (2 * (τ / 2) * K₀) := by
  set amp : ℝ := 8 * D₁ * (|D₂| + |s| + 1) with hamp
  have hamp0 : 0 < amp := by positivity
  set γ := gradExponent α with hγ
  have hγ0 : 0 < γ := gradExponent_pos hα
  set k₀ : ℕ := ⌈Real.logb 2 (amp * K₁ + 1) / γ⌉₊ + 1 with hk₀
  have hk₀1 : 1 ≤ k₀ := by omega
  set x : ℝ := amp * K₁ with hx
  set B : ℝ := 100 * 4 ^ k₀ * (x ^ 2 + Real.exp (2 * Real.pi * x)) with hB
  have hB0 : 0 < B := by positivity
  set τ₁ : ℝ := min (amp / B) (1 / (amp * K₀)) with hτ₁
  refine ⟨amp, k₀, τ₁, hamp0.le, hk₀1, lt_min (by positivity) (by positivity), ?_, ?_, ?_⟩
  · have h1 : amp / (8 * D₁) = |D₂| + |s| + 1 := by
      rw [hamp]; field_simp
    rw [h1]
    linarith [le_abs_self s, le_abs_self D₂]
  · rw [le_div_iff₀ hK₁]
    have hlog : Real.logb 2 (amp * K₁ + 1) ≤ γ * k₀ := by
      have h1 : Real.logb 2 (amp * K₁ + 1) / γ ≤ k₀ := by
        rw [hk₀]
        push_cast
        linarith [Nat.le_ceil (Real.logb 2 (amp * K₁ + 1) / γ)]
      rw [div_le_iff₀ hγ0] at h1
      linarith
    calc amp * K₁ ≤ amp * K₁ + 1 := by linarith
      _ = (2 : ℝ) ^ Real.logb 2 (amp * K₁ + 1) :=
          (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
      _ ≤ (2 : ℝ) ^ (γ * k₀) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
  · intro τ hτ hττ₁
    have hτB : τ < amp / B := lt_of_lt_of_le hττ₁ (min_le_left _ _)
    have hτK : τ < 1 / (amp * K₀) := lt_of_lt_of_le hττ₁ (min_le_right _ _)
    refine ⟨?_, ?_⟩
    · unfold costMajorant
      have e : 100 * 4 ^ k₀ * (τ / 2 * x ^ 2 + τ / 2 * Real.exp (2 * Real.pi * x)) =
          τ / 2 * B := by rw [hB]; ring
      rw [← hx, e]
      rw [lt_div_iff₀ hB0] at hτB
      linarith
    · rw [le_div_iff₀ (by positivity)]
      rw [lt_div_iff₀ (by positivity)] at hτK
      nlinarith

/-! ### The renormalized activities of a D-form layer with unit entropy -/

/-- **Gaussian activity bound** for a `RootedChargeLayerD` with `Zent = 1`: with the parameters of
`exists_gaussianActivity_params` and `κ = τ/2`, every member's renormalized activity is at most
`e^{-s A(ϱ)}`. -/
theorem abs_K_mul_exp_le_of_gaussian {G : Multigraph V E} {root : V} {lam : V → ℝ → ℝ}
    {centerOf : (V → ℤ) → V} {A : (V → ℤ) → ℝ} {D₁ D₂ α K₀ K₁ : ℝ}
    (CL : RootedChargeLayerD G root lam centerOf A (fun _ => 1) D₁ D₂ α K₀ K₁)
    (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hD₁ : 0 < D₁) {s amp τ : ℝ} {k₀ : ℕ} (hτ : 0 < τ)
    (hamp : 0 ≤ amp) (hk₀ : 1 ≤ k₀) (hs : s ≤ amp / (8 * D₁) - D₂)
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁)
    (hexp : 100 * 4 ^ k₀ * costMajorant (τ / 2) (τ / 2) (amp * K₁) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * (τ / 2) * K₀)) (hA : ∀ ϱ, 0 ≤ A ϱ)
    (i : Fin CL.n) (ϱ : V → ℤ) (hϱ : ϱ ∈ CL.N i) :
    |CL.K i ϱ| * Real.exp (-gffTranslationEnergy G τ
        (rootedSpinWaveD CL (τ / 2) amp k₀ i ϱ) (fun j => (ϱ j : ℝ))) ≤
      Real.exp (-s * A ϱ) := by
  have hgain := rootedD_gain CL (isCostEnvelope_gaussianCost hτ.le (amp * K₁))
    (by positivity) hK₀ hK₁ hD₁ hamp le_rfl hk₀ hexp hquad₁ hquad₂ i ϱ hϱ
  rw [translationEnergy_gaussianCost] at hgain
  have hK := CL.entropy i ϱ hϱ
  simp only [mul_one] at hK
  set En := gffTranslationEnergy G τ (rootedSpinWaveD CL (τ / 2) amp k₀ i ϱ)
    (fun j => (ϱ j : ℝ))
  have hX : 0 ≤ ∑ j, |(ϱ j : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hAϱ := hA ϱ
  calc |CL.K i ϱ| * Real.exp (-En) ≤ Real.exp (D₂ * A ϱ) * Real.exp (-En) :=
        mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
    _ = Real.exp (D₂ * A ϱ - En) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-s * A ϱ) := by
        refine Real.exp_le_exp.2 ?_
        have h1 : s * A ϱ ≤ (amp / (8 * D₁) - D₂) * A ϱ := mul_le_mul_of_nonneg_right hs hAϱ
        have h2 : 0 ≤ amp / 8 * ∑ j, |(ϱ j : ℝ)| := by positivity
        nlinarith

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
