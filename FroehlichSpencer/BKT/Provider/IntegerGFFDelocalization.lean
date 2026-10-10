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
import FroehlichSpencer.BKT.Reduction.T15ImpliesT11
import FroehlichSpencer.BKT.Surface.WeightedGFFExpMoment

/-!
# Provider for `FroehlichSpencer.BKT.integerGFF_delocalization`

This module contains `FroehlichSpencer.BKT.Provider.integerGFF_delocalization`, the proof of the
statement `FroehlichSpencer.BKT.integerGFF_delocalization` (file
`FroehlichSpencer/BKT/Surface/IntegerGFFDelocalization.lean`).

KP Theorem 1.1 from the KP Theorem 1.5 (`Reduction.t11_of_t15Statement`, KP §3).
-/

@[expose] public section

open MeasureTheory

namespace FroehlichSpencer.BKT.Provider

/--
KP Theorem 1.1 from the KP Theorem 1.5 (`Reduction.t11_of_t15Statement`, KP §3).
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
  Reduction.t11_of_t15Statement FroehlichSpencer.BKT.weightedGFF_expMoment_lower_bound

end FroehlichSpencer.BKT.Provider

end
