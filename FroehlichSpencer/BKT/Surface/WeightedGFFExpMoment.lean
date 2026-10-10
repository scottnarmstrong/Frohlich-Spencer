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
import FroehlichSpencer.BKT.Provider.WeightedGFFExpMoment

/-! # KP Theorem 1.5: exponential moments of the field with periodic single-site weights -/

open MeasureTheory

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
Kharash–Peled Theorem 1.5 (p. 5).

For all `Γ > 0`, `η`, `0 ≤ θ < 1/16` and
`ε > 0` there is `β₀ > 0` with the following property.

Let `Λ` be a square domain with free or
periodic boundary conditions (`L > 1`; `L` even in the periodic case), `v` a vertex,
`0 < β < β₀`, and `lam j`, `j ∈ Λ`, `(Γ, η, θ)`-sub-Gaussian at `β`.

Then the normalization
`Z = ∫ ∏ j, lam j (φ j) dμ^GFF` of the signed measure (1.8) is positive (KP p. 4), and for
`T = Δ_Λ⁻¹` (KP (1.2)) and every `f` with `∑ j, f j = 0`, (1.10)
`E_{β,Λ,λ,v}[e^⟨φ,f⟩] = Z⁻¹ ∫ e^⟨φ,f⟩ ∏ j, lam j (φ j) dμ^GFF ≥ exp (⟨f, -Δ⁻¹ f⟩ / (2 (1 + ε) β))`.
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
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.weightedGFF_expMoment_lower_bound
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
