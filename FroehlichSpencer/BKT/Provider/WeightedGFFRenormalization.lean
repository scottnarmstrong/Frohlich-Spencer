/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import FroehlichSpencer.BKT.Surface.ChargeEnsemble
public import FroehlichSpencer.BKT.Surface.DensityCenter
public import FroehlichSpencer.BKT.Surface.DensityDomain
public import FroehlichSpencer.BKT.Surface.GFFLaw
public import FroehlichSpencer.BKT.Surface.SquareFreeConnected
public import FroehlichSpencer.BKT.Surface.SquarePeriodicConnected
public import FroehlichSpencer.BKT.Surface.SubGaussian
import FroehlichSpencer.BKT.Charges.Theorem22
import FroehlichSpencer.BKT.Reduction.P24Assembly
import FroehlichSpencer.BKT.Reduction.T16Assembly
import FroehlichSpencer.BKT.Charges.P21
import FroehlichSpencer.BKT.SpinWaves.BoundaryShellPacking

/-!
# Provider for `FroehlichSpencer.BKT.weightedGFF_renormalization`

This module contains `FroehlichSpencer.BKT.Provider.weightedGFF_renormalization`, the proof of the
statement `FroehlichSpencer.BKT.weightedGFF_renormalization` (file
`FroehlichSpencer/BKT/Surface/WeightedGFFRenormalization.lean`).

KP Theorem 1.6 from KP Theorem 2.2, Proposition 2.4 (from Lemma 4.6) and Proposition 2.1:
`Reduction.t16_of_t22_p24`, `Reduction.p24_of_l46`, `t22Statement_of_repairedBasicLemma`,
`kp_p21Statement` and `SpinWaves.BoundaryShellPacking.l46Statement_holds` (KP Lemma 4.6).
-/

@[expose] public section

open MeasureTheory

namespace FroehlichSpencer.BKT.Provider

/-- KP Theorem 1.6 from KP Theorem 2.2, Proposition 2.4 (from Lemma 4.6) and Proposition 2.1 -/
theorem weightedGFF_renormalization :
    ∀ Γ : ℝ, 0 < Γ → ∀ η θ : ℝ, 0 ≤ θ → θ < 1 / 16 →
      ∃ β₀ c₁ : ℝ, 0 < β₀ ∧ 0 < c₁ ∧ ∀ (L : ℕ) (hL : 1 < L),
      let step : ∀ {E : Type} [Fintype E] (Λ : Multigraph (Fin L × Fin L) E),
          Λ.toSimpleGraph.Connected → Prop :=
        fun Λ hΛ => ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < β₀ →
          ∀ lam : Fin L × Fin L → ℝ → ℝ, (∀ j, IsSubGaussian Γ η θ β (lam j)) →
          ∃ (n : ℕ) (N : Fin n → Finset (Fin L × Fin L → ℤ)) (c : Fin n → ℝ)
            (z : Fin n → (Fin L × Fin L → ℤ) → ℝ)
            (ϱbar : Fin n → (Fin L × Fin L → ℤ) → Fin L × Fin L → ℝ),
            (∀ i, IsChargeEnsemble (N i)) ∧ (∀ i, 0 < c i) ∧ ∑ i, c i = 1 ∧
            (∀ σ : Fin L × Fin L → ℝ,
              ∫ φ, ∏ j, lam j (φ j + σ j) ∂(gffLaw Λ hΛ β hβ v) =
                ∑ i, c i * ∫ φ, ∏ ϱ ∈ N i,
                  (1 + z i ϱ * Real.cos (∑ j, φ j * ϱbar i ϱ j + ∑ j, σ j * ϱ j))
                    ∂(gffLaw Λ hΛ β hβ v)) ∧
            ∀ i,
              (∀ ϱ ∈ N i, ∑ j, ϱ j = 0) ∧
              (∀ ϱ ∈ N i, |z i ϱ| ≤ Real.exp (-(c₁ / β) *
                (∑ j, (ϱ j : ℝ) ^ 2 + Real.logb 2 (Λ.densityDiameter ϱ + 1)))) ∧
              ∀ ϱ₁ ∈ N i, ∀ ϱ₂ ∈ N i, ϱ₁ ≠ ϱ₂ → ∀ k : ℕ, 1 ≤ k →
                Λ.densityDiameter ϱ₁ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
                Λ.densityDiameter ϱ₂ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
                ∀ j₁ j₂ : Fin L × Fin L, Λ.IsDensityCenter ϱ₁ j₁ → Λ.IsDensityCenter ϱ₂ j₂ →
                  Λ.densityDomain ϱ₁ j₁ ∩ Λ.densityDomain ϱ₂ j₂ = ∅
      step (squareFree L) (squareFree_connected L hL) ∧
        (Even L → step (squarePeriodic L) (squarePeriodic_connected L hL)) :=
  Reduction.t16_of_t22_p24
    t22Statement_of_repairedBasicLemma
    (Reduction.p24_of_l46 SpinWaves.BoundaryShellPacking.l46Statement_holds) kp_p21Statement

end FroehlichSpencer.BKT.Provider

end
