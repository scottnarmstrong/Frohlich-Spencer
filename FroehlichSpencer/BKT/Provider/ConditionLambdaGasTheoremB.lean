/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.ConditionLambdaFracCorrelation
public import FroehlichSpencer.BKT.Surface.ConditionLambdaGasTheoremBFinite
import Mathlib.Tactic

/-!
# Provider: FS81 Theorem B for Condition-λ gases, infinite volume

Existence from a joint subsequence of boxes; every limit from the ** finite-volume statement**
`FroehlichSpencer.BKT.conditionLambdaGas_fracCorrelation_upper_bound` (a consumed predecessor).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open Filter Topology
open FroehlichSpencer.BKT FroehlichSpencer.BKT.Coulomb
open FroehlichSpencer.BKT.Bridge.HardCoreFracCorrelation (tendsto_val_regions neBot_regions)
open FroehlichSpencer.BKT.Bridge.HardCoreSecondMomentFree (subset_box)
open FroehlichSpencer.BKT.Bridge.ConditionLambdaGas
open FroehlichSpencer.BKT.Bridge.ConditionLambdaFracCorrelation


theorem conditionLambdaGas_fracCorrelationLimit_upper_bound :
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∀ ε : ℝ, ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧
      ∀ C α ν : ℝ, 0 < ν → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ < β → ∃ A : ℝ,
        ∀ lam : ℤ → ℝ, IsConditionLambda C α ε β lam →
        ∀ (hlam : ∀ q, 0 ≤ lam q) (hlam0 : 0 < lam 0), ν ≤ lam 0 →
        ∃ hS : IsCoulombGasSummable β lam,
          (∃ G : ℤ × ℤ → ℝ, IsConditionLambdaFracCorrelationLimit β lam hlam hlam0 hS ξ G) ∧
          ∀ G : ℤ × ℤ → ℝ, IsConditionLambdaFracCorrelationLimit β lam hlam hlam0 hS ξ G →
            ∀ x : ℤ × ℤ, x ≠ 0 →
              0 ≤ G x ∧ G x ≤ A * Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) ^ (-β' β) := by
  classical
  intro ξ hξ0 hξ1 ε
  obtain ⟨β', hβ', hfin⟩ := FroehlichSpencer.BKT.conditionLambdaGas_fracCorrelation_upper_bound
    ξ hξ0 hξ1 ε
  refine ⟨β', hβ', fun C α ν hν => ?_⟩
  obtain ⟨β₀, hB⟩ := hfin C α ν hν
  refine ⟨β₀, fun β hβ => ?_⟩
  obtain ⟨A, hA⟩ := hB β hβ
  refine ⟨A, fun lam h hlam hlam0 hν0 => ?_⟩
  obtain ⟨hS, hb⟩ := hA lam h hlam hlam0 hν0
  refine ⟨hS, ?_, ?_⟩
  · -- existence: a joint subsequence of the boxes `[-k, k]²`
    have hpos : ∀ x : ℤ × ℤ, x ≠ 0 →
        0 ≤ A * Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) ^ (-β' β) := fun x hx =>
      (hb {0, x} (by simp) x (by simp) hx).1.trans (hb {0, x} (by simp) x (by simp) hx).2
    set bound : ℤ × ℤ → ℝ := fun x =>
      if x = 0 then 1 else A * Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) ^ (-β' β)
    set u : ℕ → ℤ × ℤ → ℝ := fun k x =>
      if hx : x ∈ boxInternal k then
        conditionLambdaFracCorrelation β lam hlam hlam0 hS ξ (boxInternal k)
          ⟨0, zero_mem_box k⟩ ⟨x, hx⟩
      else 0
    have hu : ∀ k x, |u k x| ≤ bound x := by
      intro k x
      simp only [u, bound]
      split_ifs with hx h0
      · subst h0
        rw [fracCorrelation_self]
        simp
      · obtain ⟨h1, h2⟩ := hb (boxInternal k) (zero_mem_box k) x hx h0
        rw [abs_of_nonneg h1]; exact h2
      · subst_vars; simp
      · simp only [abs_zero]; exact hpos x ‹_›
    obtain ⟨φ, hφ, G, hG⟩ := exists_subseq_tendsto_pointwise u bound hu
    have hbox : Tendsto (fun k => boxInternal (φ k)) atTop atTop :=
      tendsto_atTop_atTop.2 fun S => ⟨S.sup fun x => max x.1.natAbs x.2.natAbs,
        fun k hk => (subset_box S).trans (box_mono (hk.trans (hφ.id_le k)))⟩
    refine ⟨G, fun k => boxInternal (φ k), hbox, fun x => ?_⟩
    have hval := tendsto_val_regions hbox x
    refine ((hG x).comp hval).congr' (Eventually.of_forall fun k => ?_)
    simp only [Function.comp_apply, u, dite_eq_left k.2.2]
  · -- every thermodynamic limit
    intro G ⟨Λs, hΛs, hconv⟩ x hx0
    have := neBot_regions hΛs x
    have hk : ∀ k : {k : ℕ // (0 : ℤ × ℤ) ∈ Λs k ∧ x ∈ Λs k},
        0 ≤ conditionLambdaFracCorrelation β lam hlam hlam0 hS ξ (Λs k) ⟨0, k.2.1⟩ ⟨x, k.2.2⟩ ∧
          conditionLambdaFracCorrelation β lam hlam hlam0 hS ξ (Λs k) ⟨0, k.2.1⟩ ⟨x, k.2.2⟩ ≤
            A * Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) ^ (-β' β) :=
      fun k => hb (Λs k) k.2.1 x k.2.2 hx0
    exact ⟨ge_of_tendsto (hconv x) (Eventually.of_forall fun k => (hk k).1),
      le_of_tendsto (hconv x) (Eventually.of_forall fun k => (hk k).2)⟩

end FroehlichSpencer.BKT.Provider

end
