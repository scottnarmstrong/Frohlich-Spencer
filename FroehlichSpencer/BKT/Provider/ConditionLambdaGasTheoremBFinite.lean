/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.ConditionLambdaFracCorrelation
import Mathlib.Tactic

/-!
# Provider: FS81 Theorem B for Condition-λ gases, finite volume

From the positive-vacancy gas estimate's `coulombB_conditionLambda_free_fullRange_general`, through the bridge (1.23) = the positive-vacancy gas estimate's
region correlation; `∃ hS` from the summability gate.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open Filter Topology
open FroehlichSpencer.BKT FroehlichSpencer.BKT.Coulomb
open FroehlichSpencer.BKT.Bridge.HardCoreFracCorrelation
open FroehlichSpencer.BKT.Generic.Marked (dipoleMark dipoleGap dipoleGap_pos)
open FroehlichSpencer.BKT.Bridge.ConditionLambdaGas
open FroehlichSpencer.BKT.Bridge.ConditionLambdaFracCorrelation


theorem conditionLambdaGas_fracCorrelation_upper_bound :
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∀ ε : ℝ, ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧
      ∀ C α ν : ℝ, 0 < ν → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ < β → ∃ A : ℝ,
        ∀ lam : ℤ → ℝ, IsConditionLambda C α ε β lam →
        ∀ (hlam : ∀ q, 0 ≤ lam q) (hlam0 : 0 < lam 0), ν ≤ lam 0 →
        ∃ hS : IsCoulombGasSummable β lam,
        ∀ (Λ : Finset (ℤ × ℤ)) (h0 : (0 : ℤ × ℤ) ∈ Λ) (x : ℤ × ℤ) (hx : x ∈ Λ), x ≠ 0 →
          0 ≤ conditionLambdaFracCorrelation β lam hlam hlam0 hS ξ Λ ⟨0, h0⟩ ⟨x, hx⟩ ∧
            conditionLambdaFracCorrelation β lam hlam hlam0 hS ξ Λ ⟨0, h0⟩ ⟨x, hx⟩ ≤
              A * Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) ^ (-β' β) := by
  obtain ⟨c, hc, hgen⟩ := coulombB_conditionLambda_free_fullRange_general
  intro ξ hξ0 hξ1 ε
  by_cases hε : ε < 1 / 16
  swap
  · exact ⟨id, tendsto_id, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ h => absurd h.1 hε⟩⟩⟩
  refine ⟨fun β => c * (1 / 16 - max ε 0) * dipoleGap ξ ^ 2 * β,
    tendsto_exponent_activityRange hc hξ0 hξ1 hε, fun C α ν hν => ?_⟩
  obtain ⟨κ₀, hκ₀, hF⟩ := hgen (max C 0) (max α 0) ε (le_max_right _ _) (le_max_right _ _) hε ν hν
    (dipoleGap ξ) (dipoleGap_pos hξ0 hξ1)
  obtain ⟨βg, hgate⟩ := FroehlichSpencer.BKT.conditionLambda_isCoulombGasSummable α ε
  refine ⟨max κ₀ βg, fun β hβ =>
    ⟨2 * Real.exp (1 / (64 * (1 / 16 - max ε 0)) * β), fun lam h hlam hlam0 hν0 => ?_⟩⟩
  have hS := hgate C β ((le_max_right _ _).trans_lt hβ) lam h
  refine ⟨hS, fun Λ h0 x hx hx0 => ?_⟩
  have hint : ConditionLambdaInternal (max C 0) (max α 0) ε β lam := by
    rw [max_eq_left (const_nonneg h)]; exact conditionLambdaInternal_of h
  have hb := hF β ((le_max_left _ _).trans_lt hβ) lam hint hlam hν0 Λ ξ 0 x h0 hx (Ne.symm hx0)
    hξ0 hξ1 le_rfl
  rw [fracCorrelation_eq_region Λ β lam hlam hlam0 hS (fun n => ((h.2 n).1).symm)]
  refine ⟨hb.1, hb.2.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))⟩
  have hp : 0 ≤ c * (1 / 16 - max ε 0) * dipoleGap ξ ^ 2 * β := by
    have := dipoleGap_pos hξ0 hξ1
    have hd : 0 < 1 / 16 - max ε 0 := by
      have := max_lt hε (by norm_num : (0 : ℝ) < 1 / 16); linarith
    have : 0 ≤ β := (hκ₀.trans ((le_max_left _ _).trans_lt hβ)).le
    positivity
  exact l1Profile_le_euclidPower hx0 hp

end FroehlichSpencer.BKT.Provider

end
