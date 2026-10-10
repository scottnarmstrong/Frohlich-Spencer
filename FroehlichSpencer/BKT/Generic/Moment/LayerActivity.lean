/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Renormalization.Assembly

/-!
# The renormalized activities of a charge layer (generic core)

Here:

* `abs_grad_layerSpinWave_le`: `|∇a_ϱ| ≤ max(λK₁, 1)`;
* `abs_layerActivity_le`: if the layer's entropy is at most exponential,
  `Z(ϱ) ≤ e^{a₁ ∑|ϱ| + a₂ A(ϱ)}`, and `A(ϱ) ≥ log₂(d(ϱ) + 1)` (KP P2.1, first half), then
  `|z_ϱ| ≤ exp(−b (∑|ϱ| + log₂(d(ϱ) + 1)))` for every `b ≤ λ/8 − a₁`,
  `b ≤ λ/(8 D₁) − D₂ − a₂`, `b ≥ 0`: the decay that the packing estimate consumes;
* `abs_layerActivity_le_eighth`: in particular `|z_ϱ| ≤ 1/8` once `b ≥ (log 8)/2`, the positivity
  needed by the per-factor Taylor step (KP , FS81 (6.26)).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open FroehlichSpencer.BKT.Generic.SpinWave

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] {G : Multigraph V E}
  {lam : V → ℝ → ℝ} {centerOf : (V → ℤ) → V} {A Zent : (V → ℤ) → ℝ} {D₁ D₂ α K₀ K₁ : ℝ}

/-- The renormalized activity `z_ϱ = K_i(ϱ) e^{−E_c(a_ϱ, ϱ)}` of the T1.6-NG assembly. -/
def layerActivity (CL : ChargeLayer G lam centerOf A Zent D₁ D₂ α K₀ K₁) (c : ℝ → ℝ)
    (κ amp : ℝ) (k₀ : ℕ) (i : Fin CL.n) (ϱ : V → ℤ) : ℝ :=
  CL.K i ϱ * Real.exp (-translationEnergy c (gradLinear G) (layerSpinWave CL κ amp k₀ i ϱ)
    fun j => (ϱ j : ℝ))

/-- The assembled waves have gradients at most `max(λK₁, 1)`. -/
theorem abs_grad_layerSpinWave_le (CL : ChargeLayer G lam centerOf A Zent D₁ D₂ α K₀ K₁)
    {κ : ℝ} (hκ : 0 < κ) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) {amp : ℝ} (hamp : 0 ≤ amp) (k₀ : ℕ)
    (i : Fin CL.n) (ϱ : V → ℤ) (hϱ : ϱ ∈ CL.R i) (e : E) :
    |G.grad (layerSpinWave CL κ amp k₀ i ϱ) e| ≤ max (amp * K₁) 1 := by
  classical
  obtain ⟨-, hK0, hK1, -⟩ := Classical.choose_spec (CL.wave i ϱ hϱ)
  simp only [layerSpinWave, dite_eq_left hϱ]
  refine (abs_grad_envelopeWave_le _ hκ (by rw [hK0]; exact hK₀) (by rw [hK1]; exact hK₁)
    hamp k₀ e).trans ?_
  rw [hK1]

/-- **Decay of the renormalized activities.** -/
theorem abs_layerActivity_le (CL : ChargeLayer G lam centerOf A Zent D₁ D₂ α K₀ K₁)
    {c : ℝ → ℝ} {κ κ' W : ℝ} (hc : IsCostEnvelope c κ κ' W) (hκ : 0 < κ) (hK₀ : 0 < K₀)
    (hK₁ : 0 < K₁) (hD₁ : 0 < D₁) {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * K₁ ≤ W)
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * K₁) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * K₀)) (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁)
    {a₁ a₂ b : ℝ} (hZ : ∀ ϱ : V → ℤ, Zent ϱ ≤ Real.exp (a₁ * ∑ j, |(ϱ j : ℝ)| + a₂ * A ϱ))
    (hb0 : 0 ≤ b) (hb₁ : b ≤ amp / 8 - a₁) (hb₂ : b ≤ amp / (8 * D₁) - D₂ - a₂)
    (i : Fin CL.n) (ϱ : V → ℤ) (hϱ : ϱ ∈ CL.R i)
    (hAlog : Real.logb 2 (G.densityDiameter ϱ + 1) ≤ A ϱ) :
    |layerActivity CL c κ amp k₀ i ϱ| ≤
      Real.exp (-b * (∑ j, |(ϱ j : ℝ)| + Real.logb 2 (G.densityDiameter ϱ + 1))) := by
  have hgain := layer_gain CL hc hκ hK₀ hK₁ hD₁ hamp hampW hk₀ hexp hquad₁ hquad₂ i ϱ hϱ
  have hK := CL.entropy i ϱ hϱ
  have hZϱ := hZ ϱ
  set X : ℝ := ∑ j, |(ϱ j : ℝ)|
  set E' := translationEnergy c (gradLinear G) (layerSpinWave CL κ amp k₀ i ϱ)
    fun j => (ϱ j : ℝ)
  have hA0 : 0 ≤ A ϱ := (Real.logb_nonneg (by norm_num) (by
    have := Nat.cast_nonneg (α := ℝ) (G.densityDiameter ϱ); linarith)).trans hAlog
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold layerActivity
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |CL.K i ϱ| * Real.exp (-E')
      ≤ (Real.exp (D₂ * A ϱ) * Real.exp (a₁ * X + a₂ * A ϱ)) * Real.exp (-E') :=
        mul_le_mul_of_nonneg_right (hK.trans (mul_le_mul_of_nonneg_left hZϱ
          (Real.exp_pos _).le)) (Real.exp_pos _).le
    _ = Real.exp (D₂ * A ϱ + (a₁ * X + a₂ * A ϱ) - E') := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-b * (X + A ϱ)) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : b * X ≤ (amp / 8 - a₁) * X := mul_le_mul_of_nonneg_right hb₁ hX0
        have h2 : b * A ϱ ≤ (amp / (8 * D₁) - D₂ - a₂) * A ϱ :=
          mul_le_mul_of_nonneg_right hb₂ hA0
        nlinarith
    _ ≤ Real.exp (-b * (X + Real.logb 2 (G.densityDiameter ϱ + 1))) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith

/-- **Small activities**: `|z_ϱ| ≤ 1/8` once the decay rate is at least `(log 8)/2`. -/
theorem abs_layerActivity_le_eighth {b : ℝ} (hb8 : Real.log 8 / 2 ≤ b) {X ℓ z : ℝ}
    (hX : 2 ≤ X) (hℓ : 0 ≤ ℓ) (hz : |z| ≤ Real.exp (-b * (X + ℓ))) : |z| ≤ 1 / 8 := by
  have hb0 : 0 ≤ b := le_trans (by positivity) hb8
  refine hz.trans ?_
  have h : -b * (X + ℓ) ≤ -Real.log 8 := by nlinarith
  calc Real.exp (-b * (X + ℓ)) ≤ Real.exp (-Real.log 8) := Real.exp_le_exp.mpr h
    _ = 1 / 8 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

end FroehlichSpencer.BKT.Generic

end
