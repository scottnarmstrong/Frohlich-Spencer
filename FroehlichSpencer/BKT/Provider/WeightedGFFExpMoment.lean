/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import FroehlichSpencer.BKT.Surface.GFFLaw
public import FroehlichSpencer.BKT.Surface.LaplacianPseudoinverse
public import FroehlichSpencer.BKT.Surface.SquareFreeConnected
public import FroehlichSpencer.BKT.Surface.SquarePeriodicConnected
public import FroehlichSpencer.BKT.Surface.SubGaussian
import FroehlichSpencer.BKT.Reduction.T16ImpliesT15
import FroehlichSpencer.BKT.Surface.WeightedGFFRenormalization

/-!
# Provider for `FroehlichSpencer.BKT.weightedGFF_expMoment_lower_bound`

This module contains `FroehlichSpencer.BKT.Provider.weightedGFF_expMoment_lower_bound`, the proof of
the statement `FroehlichSpencer.BKT.weightedGFF_expMoment_lower_bound` (file
`FroehlichSpencer/BKT/Surface/WeightedGFFExpMoment.lean`).

KP Theorem 1.5 from the KP Theorem 1.6 (`Reduction.t15_of_t16Statement`, KP §3).
-/

@[expose] public section

open MeasureTheory

namespace FroehlichSpencer.BKT.Provider

/--
KP Theorem 1.5 from the KP Theorem 1.6 (`Reduction.t15_of_t16Statement`, KP §3).
-/
theorem weightedGFF_expMoment_lower_bound :
    ∀ Γ : ℝ, 0 < Γ → ∀ η θ : ℝ, 0 ≤ θ → θ < 1 / 16 → ∀ ε : ℝ, 0 < ε →
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ (L : ℕ) (hL : 1 < L),
      let bounds : ∀ {E : Type} [Fintype E] (Λ : Multigraph (Fin L × Fin L) E),
          Λ.toSimpleGraph.Connected → Prop :=
        fun Λ hΛ => ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < β₀ →
          ∀ lam : Fin L × Fin L → ℝ → ℝ, (∀ j, IsSubGaussian Γ η θ β (lam j)) →
            0 < ∫ φ, ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v) ∧
            ∀ T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ, Λ.IsLaplacianPseudoinverse T →
              ∀ f : Fin L × Fin L → ℝ, ∑ j, f j = 0 →
                Real.exp ((∑ j, f j * -(T f j)) / (2 * (1 + ε) * β)) ≤
                  (∫ φ, Real.exp (∑ j, φ j * f j) * ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v)) /
                    ∫ φ, ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v)
      bounds (squareFree L) (squareFree_connected L hL) ∧
        (Even L → bounds (squarePeriodic L) (squarePeriodic_connected L hL)) :=
  Reduction.t15_of_t16Statement FroehlichSpencer.BKT.weightedGFF_renormalization

end FroehlichSpencer.BKT.Provider

end
