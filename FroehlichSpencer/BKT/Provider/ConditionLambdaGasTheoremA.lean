/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.ConditionLambdaSecondMoment
public import FroehlichSpencer.BKT.Surface.ConditionLambdaGasTheoremAFinite
public import FroehlichSpencer.BKT.Surface.ConditionLambdaSecondMomentLimit
import Mathlib.Tactic

/-!
# Provider: FS81 Theorem A for Condition-λ gases, infinite volume

Existence: 's box limits (`lambda_thermodynamic_limit_exists`) for `λ/λ(0)`.

Every limit: the
** finite-volume statement** `FroehlichSpencer.BKT.conditionLambdaGas_secondMoment_lower_bound`
(a consumed predecessor), passed to the limit.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open Filter Topology
open FroehlichSpencer.BKT FroehlichSpencer.BKT.Coulomb
open FroehlichSpencer.BKT.Bridge.HardCoreSecondMomentFree (subset_box)
open FroehlichSpencer.BKT.Bridge.ConditionLambdaGas
open FroehlichSpencer.BKT.Bridge.ConditionLambdaSecondMoment


theorem conditionLambdaGas_secondMomentLimit_lower_bound :
    ∀ δ : ℝ, 0 < δ → ∀ C α ε ν : ℝ, 0 < ν → ∃ β₀ : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
      ∀ lam : ℤ → ℝ, IsConditionLambda C α ε β lam →
      ∀ (hlam : ∀ q, 0 ≤ lam q) (hlam0 : 0 < lam 0), ν ≤ lam 0 →
      ∃ hS : IsCoulombGasSummable β lam,
        (∃ M : (ℤ × ℤ →₀ ℝ) → ℝ, IsConditionLambdaSecondMomentLimit β hβ lam hlam hlam0 hS M) ∧
        ∀ M : (ℤ × ℤ →₀ ℝ) → ℝ, IsConditionLambdaSecondMomentLimit β hβ lam hlam hlam0 hS M →
          ∀ g : ℤ × ℤ →₀ ℝ, (g.sum fun _ a => a) = 0 →
            (1 - δ) * β * (g.sum fun x a => g.sum fun y b => a * b * coulombPotential (x - y)) ≤
              M g := by
  intro δ hδ C α ε ν hν
  by_cases hε : ε < 1 / 16
  swap
  · exact ⟨0, fun _ _ _ _ h => absurd h.1 hε⟩
  obtain ⟨β₁, hfin⟩ :=
    FroehlichSpencer.BKT.conditionLambdaGas_secondMoment_lower_bound δ hδ C α ε ν hν
  obtain ⟨κ₁, hκ₁, hF⟩ := free_conditionLambda_bound (1 / 2) (by norm_num) (max C 0 / ν) α ε hε
  refine ⟨max β₁ κ₁, fun β hβpos hβ lam h hlam hlam0 hν0 => ?_⟩
  have hβ₁ : β₁ < β := (le_max_left _ _).trans_lt hβ
  have hκβ : κ₁ < β := (le_max_right _ _).trans_lt hβ
  obtain ⟨hS, hb⟩ := hfin β hβpos hβ₁ lam h hlam hlam0 hν0
  refine ⟨hS, ?_, ?_⟩
  · -- existence: 's box limits for `λ / λ(0)`
    have hint := conditionLambdaInternal_normalize h hν hν0
    have hphys := physical_normalize hlam hlam0
    obtain ⟨φ, hφ, Γ, hΓ⟩ := lambda_thermodynamic_limit_exists hF (by norm_num) β
      (hκ₁.trans hκβ) hκβ _ hint hphys
    refine ⟨fun g => ∑ x ∈ g.support, ∑ y ∈ g.support, g x * g y * Γ x y,
      fun k => boxInternal (φ k), ?_, fun g hg => ?_⟩
    · exact tendsto_atTop_atTop.2 fun S => ⟨S.sup fun x => max x.1.natAbs x.2.natAbs,
        fun k hk => (subset_box S).trans (box_mono (hk.trans (hφ.id_le k)))⟩
    · set R := g.support.sup fun x => max x.1.natAbs x.2.natAbs
      have hsupp : SupportedInBox R g := fun x hx => by
        by_contra hne
        exact hx (subset_box g.support (Finsupp.mem_support_iff.mpr hne))
      have hsumR : ∑ x ∈ boxInternal R, g x = 0 := by
        rw [← hg, Finsupp.sum_of_support_subset g (subset_box g.support) _ fun _ _ => rfl]
      have hval : ∀ (k : ℕ) (hk : g.support ⊆ boxInternal (φ k)), R ≤ φ k →
          conditionLambdaSecondMoment β hβpos lam hlam hlam0 hS (boxInternal (φ k)) g hk hg =
            ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y *
              lambdaFieldCorrelationInternal β (fun n => (lam 0)⁻¹ * lam n) (φ k) x y := by
        intro k hk hR
        rw [secondMoment_eq_full, ← fullSecondMoment_normalize _ _ _ hlam0.ne']
        exact lambdaSecondMoment_box_eq_sum β _
          (hF (boxInternal (φ k)) β hκβ _ hint hphys.1).2.1 hR hsupp hsumR
      have hMg : (∑ x ∈ g.support, ∑ y ∈ g.support, g x * g y * Γ x y) =
          ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y * Γ x y := by
        rw [Finset.sum_subset (subset_box g.support) fun x _ hx => by
          simp [Finsupp.notMem_support_iff.mp hx]]
        refine Finset.sum_congr rfl fun x _ => ?_
        exact Finset.sum_subset (subset_box g.support) fun y _ hy => by
          simp [Finsupp.notMem_support_iff.mp hy]
      beta_reduce
      rw [hMg]
      have hlimN : Tendsto (fun k : ℕ => ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y *
          lambdaFieldCorrelationInternal β (fun n => (lam 0)⁻¹ * lam n) (φ k) x y) atTop
          (𝓝 (∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y * Γ x y)) :=
        tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun y _ => (hΓ x y).const_mul _
      have : Nonempty {k : ℕ // g.support ⊆ boxInternal (φ k)} :=
        ⟨⟨R, (subset_box g.support).trans (box_mono (hφ.id_le R))⟩⟩
      have hval' : Tendsto (Subtype.val : {k : ℕ // g.support ⊆ boxInternal (φ k)} → ℕ)
          atTop atTop :=
        tendsto_atTop_atTop.2 fun b => ⟨⟨max b R, (subset_box g.support).trans
          (box_mono ((le_max_right b R).trans (hφ.id_le _)))⟩,
          fun k hk => (le_max_left b R).trans hk⟩
      refine (hlimN.comp hval').congr' ?_
      filter_upwards [hval'.eventually (eventually_ge_atTop R)] with k hk
      exact (hval k.1 k.2 (hk.trans (hφ.id_le _))).symm
  · rintro M ⟨Λs, hΛs, hconv⟩ g hg
    have : Nonempty {k : ℕ // g.support ⊆ Λs k} := by
      obtain ⟨k, hk⟩ := (tendsto_atTop.1 hΛs g.support).exists
      exact ⟨⟨k, hk⟩⟩
    refine ge_of_tendsto (hconv g hg) (Eventually.of_forall fun k => ?_)
    exact hb (Λs k) g k.2 hg

end FroehlichSpencer.BKT.Provider

end
