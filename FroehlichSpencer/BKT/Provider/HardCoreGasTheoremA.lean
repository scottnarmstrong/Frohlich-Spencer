/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.HardCoreSecondMomentFree
public import FroehlichSpencer.BKT.Surface.CoulombPotential
public import FroehlichSpencer.BKT.Surface.HardCoreSecondMomentLimit
public import FroehlichSpencer.BKT.Surface.HardCoreGasTheoremAFinite
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.hardCoreGas_secondMomentLimit_lower_bound`

This module contains `FroehlichSpencer.BKT.Provider.hardCoreGas_secondMomentLimit_lower_bound`, the
proof of the statement `FroehlichSpencer.BKT.hardCoreGas_secondMomentLimit_lower_bound` (file
`FroehlichSpencer/BKT/Surface/HardCoreGasTheoremA.lean`).

-/

@[expose] public section

open MeasureTheory Filter Topology
open FroehlichSpencer.BKT.Coulomb
open FroehlichSpencer.BKT.Bridge.HardCoreSecondMoment
open FroehlichSpencer.BKT.Bridge.HardCoreSecondMomentFree

noncomputable section

namespace FroehlichSpencer.BKT.Provider


theorem hardCoreGas_secondMomentLimit_lower_bound :
    ∀ δ : ℝ, 0 < δ → ∀ α : ℝ, ∃ β₀ : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
      ∀ (z : ℝ) (hz : 0 ≤ z), z ≤ Real.exp (β / 17 + α) →
        (∃ M : (ℤ × ℤ →₀ ℝ) → ℝ, IsHardCoreSecondMomentLimit β hβ z hz M) ∧
        ∀ M : (ℤ × ℤ →₀ ℝ) → ℝ, IsHardCoreSecondMomentLimit β hβ z hz M →
          ∀ g : ℤ × ℤ →₀ ℝ, (g.sum fun _ a => a) = 0 →
            (1 - δ) * β * (g.sum fun x a => g.sum fun y b => a * b * coulombPotential (x - y)) ≤
              M g := by
  intro δ hδ α
  obtain ⟨β₁, hfin⟩ := FroehlichSpencer.BKT.hardCoreGas_secondMoment_lower_bound δ hδ α
  obtain ⟨κ₁, -, h₁⟩ := free_secondMoment_lower_bound (1 / 2) (by norm_num) α
  refine ⟨max β₁ κ₁, fun β hβ hβ₀ z hz hzβ => ⟨?_, ?_⟩⟩
  · -- existence: 's box limit points
    obtain ⟨φ, hφ, Γ, -, hΓ, -⟩ := free_thermodynamic_limit_exists h₁ (by norm_num) β hβ
      ((le_max_right _ _).trans_lt hβ₀) z hz hzβ
    refine ⟨fun g => ∑ x ∈ g.support, ∑ y ∈ g.support, g x * g y * Γ x y,
      fun k => boxInternal (φ k), ?_, fun g hg => ?_⟩
    · refine tendsto_atTop_atTop.2 fun S => ⟨S.sup fun x => max x.1.natAbs x.2.natAbs,
        fun k hk => (subset_box S).trans (box_mono (hk.trans (hφ.id_le k)))⟩
    · set R := g.support.sup fun x => max x.1.natAbs x.2.natAbs
      have hsupp : SupportedInBox R g := fun x hx => by
        by_contra hne
        exact hx (subset_box g.support (Finsupp.mem_support_iff.mpr hne))
      have hsumR : ∑ x ∈ boxInternal R, g x = 0 := by
        rw [← hg, Finsupp.sum_of_support_subset g (subset_box g.support) _ fun _ _ => rfl]
      have hval : ∀ (k : ℕ) (hk : g.support ⊆ boxInternal (φ k)), R ≤ φ k →
          hardCoreSecondMoment β hβ z hz (boxInternal (φ k)) g hk hg =
            ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y *
              freeFieldCorrelationInternal β z (φ k) x y := by
        intro k hk hR
        rw [hardCoreSecondMoment_eq_free]
        exact freeSecondMoment_box_eq_sum β z hR hsupp hsumR
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
          freeFieldCorrelationInternal β z (φ k) x y) atTop
          (𝓝 (∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y * Γ x y)) :=
        tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun y _ => (hΓ x y).const_mul _
      have : Nonempty {k : ℕ // g.support ⊆ boxInternal (φ k)} :=
        ⟨⟨R, (subset_box g.support).trans (box_mono (hφ.id_le R))⟩⟩
      have hval' : Tendsto (Subtype.val : {k : ℕ // g.support ⊆ boxInternal (φ k)} → ℕ)
          atTop atTop :=
        tendsto_atTop_atTop.2 fun b => ⟨⟨max b R, (subset_box g.support).trans
          (box_mono ((le_max_right b R).trans (hφ.id_le _)))⟩, fun k hk => (le_max_left b R).trans hk⟩
      refine (hlimN.comp hval').congr' ?_
      filter_upwards [hval'.eventually (eventually_ge_atTop R)] with k hk
      exact (hval k.1 k.2 (hk.trans (hφ.id_le _))).symm
  · rintro M ⟨Λs, hΛs, hconv⟩ g hg
    have : Nonempty {k : ℕ // g.support ⊆ Λs k} := by
      obtain ⟨k, hk⟩ := (tendsto_atTop.1 hΛs g.support).exists
      exact ⟨⟨k, hk⟩⟩
    refine ge_of_tendsto (hconv g hg) (Eventually.of_forall fun k => ?_)
    exact hfin β hβ ((le_max_left _ _).trans_lt hβ₀) z hz hzβ (Λs k) g k.2 hg

end FroehlichSpencer.BKT.Provider

end
