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
import FroehlichSpencer.BKT.Provider.WeightedGFFRenormalization

/-! # KP Theorem 1.6: the renormalization step -/

open MeasureTheory

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
Kharash–Peled Theorem 1.6 (pp. 6–7).

For all `Γ > 0`, `η` and `0 ≤ θ < 1/16`
there are `β₀, c₁ > 0` with the following property.

Let `Λ` be a square domain with free or
periodic boundary conditions (`L > 1`; `L` even in the periodic case), `v` a vertex,
`0 < β < β₀`, and `lam j`, `j ∈ Λ`, `(Γ, η, θ)`-sub-Gaussian at `β`.

There are a
finite family `N i`, `i < n`, of ensembles (an indexed collection: the data `c i`, `z i ϱ`,
`ϱbar i ϱ` belong to the index, and the same ensemble may occur at several indices), positive
`c i` summing to `1`, reals `z i ϱ` and functions `ϱbar i ϱ : Λ → ℝ` such that (1.13) holds for
every `σ : Λ → ℝ` and, for every `i`: (1) every `ϱ ∈ N i` is neutral; (2) (1.14)
`|z i ϱ| ≤ exp (-(c₁ / β) (‖ϱ‖₂² + log₂ (d(ϱ) + 1)))`; (3) for distinct `ϱ₁, ϱ₂ ∈ N i` with
`d(ϱ₁), d(ϱ₂) ∈ [2^k - 1, 2^(k+1) - 2]`, `k ≥ 1`, `D_{j₁}(ϱ₁) ∩ D_{j₂}(ϱ₂) = ∅` for all
admissible centers `j₁` of `ϱ₁` and `j₂` of `ϱ₂` (KP p. 5: the center is "chosen in some fixed
arbitrary way", so (3) holds whichever choice is fixed).
-/
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
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.weightedGFF_renormalization
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
