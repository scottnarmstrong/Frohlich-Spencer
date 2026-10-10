/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.ConditionLambdaSecondMoment
import Mathlib.Tactic

/-!
# Provider: FS81 Theorem A for Condition-λ gases, finite volume

From 's `free_conditionLambda_physical` for `λ/λ(0)` (internal Condition λ with constant
`max C 0/ν`), through the bridge (1.16) = `fullSecondMomentInternal`; `∃ hS` from the
summability gate.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open Filter Topology
open FroehlichSpencer.BKT FroehlichSpencer.BKT.Coulomb
open FroehlichSpencer.BKT.Bridge.HardCoreFracCorrelation (pairC freeChargePairing_eq)
open FroehlichSpencer.BKT.Bridge.HardCoreSecondMoment (finsupp_sum_eq_sum_region)
open FroehlichSpencer.BKT.Bridge.HardCoreSecondMomentFree (quad_eq_freeQuad)
open FroehlichSpencer.BKT.Bridge.ConditionLambdaGas
open FroehlichSpencer.BKT.Bridge.ConditionLambdaSecondMoment


theorem conditionLambdaGas_secondMoment_lower_bound :
    ∀ δ : ℝ, 0 < δ → ∀ C α ε ν : ℝ, 0 < ν → ∃ β₀ : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
      ∀ lam : ℤ → ℝ, IsConditionLambda C α ε β lam →
      ∀ (hlam : ∀ q, 0 ≤ lam q) (hlam0 : 0 < lam 0), ν ≤ lam 0 →
      ∃ hS : IsCoulombGasSummable β lam,
      ∀ (Λ : Finset (ℤ × ℤ)) (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ)
        (hg : (g.sum fun _ a => a) = 0),
        (1 - δ) * β * (g.sum fun x a => g.sum fun y b => a * b * coulombPotential (x - y)) ≤
          conditionLambdaSecondMoment β hβ lam hlam hlam0 hS Λ g hgΛ hg := by
  intro δ hδ C α ε ν hν
  by_cases hε : ε < 1 / 16
  swap
  · exact ⟨0, fun _ _ _ _ h => absurd h.1 hε⟩
  obtain ⟨κ₀, -, hF⟩ := free_conditionLambda_bound δ hδ (max C 0 / ν) α ε hε
  obtain ⟨βg, hgate⟩ := FroehlichSpencer.BKT.conditionLambda_isCoulombGasSummable α ε
  refine ⟨max κ₀ βg, fun β _ hβ lam h hlam hlam0 hν0 => ?_⟩
  have hS := hgate C β ((le_max_right _ _).trans_lt hβ) lam h
  refine ⟨hS, fun Λ g hgΛ hg => ?_⟩
  obtain ⟨-, -, hA, -⟩ := free_conditionLambda_physical hF Λ β ((le_max_left _ _).trans_lt hβ)
    _ (conditionLambdaInternal_normalize h hν hν0) (physical_normalize hlam hlam0)
    (fun v => g v) (sum_region_eq_zero Λ g hgΛ hg)
  rw [secondMoment_eq_full, ← fullSecondMoment_normalize _ _ _ hlam0.ne', quad_eq_freeQuad Λ g hgΛ]
  exact hA

end FroehlichSpencer.BKT.Provider

end
