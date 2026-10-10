/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Villain.TheoremC.GaussianWeight
public import FroehlichSpencer.BKT.Rotator.TheoremC.BesselNumbers

/-! # T1.5 parameters for the Gaussian Villain weight

The Gaussian Villain cost has the same quadratic and exponential cost envelope used in the
existing rooted T1.5 parameter selection. This file transports that selection to the Gaussian
logarithmic-derivative modulus `B⁻¹ |u|`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Villain.TheoremC

open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Rotator.TheoremC
open Filter Topology

/-- The amplitude, scale cutoff, decay rate and packing error for the Gaussian Villain weight.
Here `B` is the parameter in `gaussianVillainWeight B`; the physical Villain inverse temperature
is `B / (4π²)`. -/
theorem exists_gaussianVillainNumbers {D₁ D₂ α K₀ K₁ Kv a₁ a₂ : ℝ} (Kov : ℕ)
    (hα : 1 < α) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hD₁ : 0 < D₁) (hKv : 0 ≤ Kv) :
    ∃ (B₀ : ℝ) (amp b ε : ℝ → ℝ) (k₀ : ℝ → ℕ),
      1 ≤ B₀ ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ B : ℝ, B₀ ≤ B →
        0 ≤ amp B ∧ amp B * K₁ ≤ Real.pi * B ∧ 1 ≤ k₀ B ∧
        100 * 4 ^ k₀ B * costMajorant (B⁻¹) (B⁻¹) (amp B * K₁) ≤ amp B / 2 ∧
        amp B ≤ 1 / (2 * B⁻¹ * K₀) ∧
        amp B ≤ (2 : ℝ) ^ (gradExponent α * k₀ B) / K₁ ∧
        (∀ u : ℝ, |u| ≤ max (amp B * K₁) 1 → B⁻¹ * |u| ≤ 1) ∧
        Real.log 8 / 2 ≤ b B ∧ b B ≤ amp B / 8 - a₁ ∧
        b B ≤ amp B / (8 * D₁) - D₂ - a₂ ∧ 0 ≤ ε B ∧
        ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
          (Kov : ℝ) * (8 * (Kv + 2 * Kv ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
            Real.exp (-b B * (u + Real.logb 2 (d + 1))) ≤ ε B := by
  obtain ⟨B₀, amp, b, ε, k₀, hB₀, hε, hN⟩ :=
    exists_besselNumbers (D₁ := D₁) (D₂ := D₂) (α := α) (K₀ := K₀) (K₁ := K₁)
      (Kv := Kv) (a₁ := a₁) (a₂ := a₂) (C := 1) Kov hα hK₀ hK₁ hD₁ hKv (by norm_num)
  refine ⟨B₀, amp, b, ε, k₀, hB₀, hε, fun B hB => ?_⟩
  obtain ⟨ha, haW, hk, hcost, hquad₁, hquad₂, hmod, hb8, hb₁, hb₂, hε₀, hthr⟩ := hN B hB
  have hmod' : ∀ u : ℝ, |u| ≤ max (amp B * K₁) 1 → B⁻¹ * |u| ≤ 1 := by
    intro u hu
    have huExp : |u| ≤ Real.exp |u| := by
      nlinarith [Real.add_one_le_exp |u|]
    calc B⁻¹ * |u| ≤ B⁻¹ * Real.exp |u| :=
          mul_le_mul_of_nonneg_left huExp (inv_pos.mpr (by linarith [hB₀])).le
      _ ≤ 1 := by simpa [one_div] using hmod u hu
  refine ⟨ha, haW, hk, ?_, ?_, hquad₂, hmod', hb8, hb₁, hb₂, hε₀, hthr⟩
  · simpa [one_div] using hcost
  · simpa [one_div] using hquad₁

end FroehlichSpencer.BKT.Villain.TheoremC

end
