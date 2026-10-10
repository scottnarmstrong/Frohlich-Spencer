/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Mathlib
public import FroehlichSpencer.BKT.Surface.IntegerGFFDelocalization
public import FroehlichSpencer.BKT.Surface.VillainPowerLaw
public import FroehlichSpencer.BKT.Surface.WeightedGFFExpMoment
public import FroehlichSpencer.BKT.Surface.WeightedGFFRenormalization

-- Reset the auxiliary-lemma cache between copied source modules.
-- This preserves generated proof names without changing definitions or assumptions.
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.KharashPeled.integerGFF_delocalization :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ (L : ℕ) (hL : 1 < L),
      let bounds : ∀ {E : Type} [Fintype E] (Λ : Multigraph (Fin L × Fin L) E),
          Λ.toSimpleGraph.Connected → Prop :=
        fun Λ hΛ => ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < β₀ →
          (∀ T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ, Λ.IsLaplacianPseudoinverse T →
            ∀ f : Fin L × Fin L → ℝ, ∑ j, f j = 0 →
              ENNReal.ofReal (Real.exp ((∑ j, f j * -(T f j)) / (2 * (1 + ε) * β))) ≤
                  ∫⁻ m, ENNReal.ofReal (Real.exp (∑ j, (m j : ℝ) * f j))
                    ∂(integerGFFLaw Λ hΛ β hβ v) ∧
                ENNReal.ofReal ((∑ j, f j * -(T f j)) / ((1 + ε) * β)) ≤
                  ∫⁻ m, ENNReal.ofReal ((∑ j, (m j : ℝ) * f j) ^ 2)
                    ∂(integerGFFLaw Λ hΛ β hβ v)) ∧
          ∀ j k : Fin L × Fin L,
            ENNReal.ofReal (c / β * Real.log (Λ.toSimpleGraph.dist j k + 1)) ≤
              ∫⁻ m, ENNReal.ofReal (((m j : ℝ) - m k) ^ 2) ∂(integerGFFLaw Λ hΛ β hβ v)
      bounds (squareFree L) (squareFree_connected L hL) ∧
        (Even L → bounds (squarePeriodic L) (squarePeriodic_connected L hL)) :=
  by exact FroehlichSpencer.BKT.integerGFF_delocalization
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.KharashPeled.villain_powerLaw_lower_bound :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 < C ∧
      ∀ L : ℕ, 1 < L → ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
        ∀ j : Option (Fin L × Fin L),
          ((squareZero L).toSimpleGraph.dist j none + 1 : ℝ) ^ (-C / β) ≤
            ∫ θ, Real.cos (θ j) ∂(villainLaw L β hβ) :=
  by exact FroehlichSpencer.BKT.villain_powerLaw_lower_bound
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.KharashPeled.weightedGFF_expMoment_lower_bound :
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
  by exact FroehlichSpencer.BKT.weightedGFF_expMoment_lower_bound
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.KharashPeled.weightedGFF_renormalization :
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
  by exact FroehlichSpencer.BKT.weightedGFF_renormalization
end FroehlichSpencer.BKT
end
