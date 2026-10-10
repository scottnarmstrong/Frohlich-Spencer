/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import FroehlichSpencer.BKT.Surface.IntegerGFFLaw
public import FroehlichSpencer.BKT.Surface.LaplacianPseudoinverse
public import FroehlichSpencer.BKT.Surface.SquareFreeConnected
public import FroehlichSpencer.BKT.Surface.SquarePeriodicConnected
import FroehlichSpencer.BKT.Provider.IntegerGFFDelocalization

/-! # KP Theorem 1.1: delocalization of the integer-valued Gaussian free field -/

open MeasureTheory

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
Kharash–Peled Theorem 1.1 (p. 3).

There is an absolute constant `c > 0` such
that for every `ε > 0` there is `β₀ > 0` with the following property.

Let `Λ` be a square domain
with free or periodic boundary conditions (`L > 1`; `L` even in the periodic case), `v` a vertex,
`0 < β < β₀`, and `T = Δ_Λ⁻¹` (KP (1.2)).

For every `f` with `∑ j, f j = 0`, (1.6)
`E^IV[e^⟨m,f⟩] ≥ exp (⟨f, -Δ⁻¹ f⟩ / (2 (1 + ε) β))` and (1.7)
`E^IV[⟨m,f⟩²] ≥ ⟨f, -Δ⁻¹ f⟩ / ((1 + ε) β)`; and for all vertices `j, k`,
`E^IV[(m j - m k)²] ≥ (c / β) log (dist (j, k) + 1)`.
-/
theorem integerGFF_delocalization :
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
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.integerGFF_delocalization
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
