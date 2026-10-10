/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerComb
public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerRun
public import FroehlichSpencer.BKT.Generic.PinnedCharges.WiredAdapter

/-!
For the selection constants `M = 2^16`, `α = 7/4` (`chargeCoverScale`, `chargeCoverExponent`):

* `IsCombTerminal N T`: `T` is a terminal configuration reachable by the selection from the
  single-site start of some charge assignment `f : Site L → [1, N]` with the comb coefficients.
* `combBranches L N`: the global finite list of weighted comb terminals, obtained by expanding
  `∏_x dirichletComb N (φ x)` over charge assignments (`LayerComb`) and running the selection on
  each (`LayerRun`).
* `combBranches_spec`: positive weights summing to `1`, every branch a comb terminal, and
  `∏_x dirichletComb N (φ x) = ∑_b w_b ∏_{ρ ∈ F_b} (1 + K_b(ρ) cos⟨φ, ρ⟩)` for every `φ`.
* `prod_pinnedCombLam_eq_branches`: the same identity on the wired carrier, for root-pinned
  fields, with every terminal density neutralized at the wired root.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

theorem one_lt_chargeCoverScale : (1 : ℝ) < (chargeCoverScale : ℝ) := by
  norm_num [chargeCoverScale]

theorem one_le_chargeCoverExponent : (1 : ℝ) ≤ chargeCoverExponent := by
  norm_num [chargeCoverExponent]

/-- A terminal configuration of the selection run from a comb start with cutoff `N`. -/
def IsCombTerminal (N : ℕ) (T : SelConfig L) : Prop :=
  T.A = ∅ ∧ ∃ f : Site L → ℕ, (∀ x, 1 ≤ f x ∧ f x ≤ N) ∧
    SelReach (chargeCoverScale : ℝ) chargeCoverExponent
      (SelConfig.start (singleSiteEnsemble f) (combActivity N)) T

/-- Comb terminals carry the full Appendix D geometry. -/
theorem IsCombTerminal.geometry {N : ℕ} {T : SelConfig L} (h : IsCombTerminal N T) :
    AppendixDChargeGeometry (chargeCoverScale : ℝ) chargeCoverExponent T.F := by
  obtain ⟨hA, f, hf, hreach⟩ := h
  have hf1 : ∀ x, 1 ≤ f x := fun x => (hf x).1
  exact hreach.geometry one_lt_chargeCoverScale one_le_chargeCoverExponent
    (SelConfig.start_valid one_lt_chargeCoverScale one_le_chargeCoverExponent
      (singleSiteEnsemble_pinned hf1) (singleSiteEnsemble_card_support hf1) _) hA

/-- The selection runs of one charge assignment (empty off the admissible assignments). -/
def combRuns (N : ℕ) (f : Site L → ℕ) : List (ℝ × SelConfig L) :=
  if hf : ∀ x, 1 ≤ f x then
    Classical.choose (exists_runExpansion one_lt_chargeCoverScale one_le_chargeCoverExponent
      (SelConfig.start_valid one_lt_chargeCoverScale one_le_chargeCoverExponent
        (singleSiteEnsemble_pinned hf) (singleSiteEnsemble_card_support hf) (combActivity N)))
  else []

theorem combRuns_spec (N : ℕ) {f : Site L → ℕ} (hf : ∀ x, 1 ≤ f x) :
    IsRunExpansion (chargeCoverScale : ℝ) chargeCoverExponent
      (SelConfig.start (singleSiteEnsemble f) (combActivity N)) (combRuns N f) := by
  unfold combRuns
  split_ifs
  exact Classical.choose_spec (exists_runExpansion one_lt_chargeCoverScale
    one_le_chargeCoverExponent (SelConfig.start_valid one_lt_chargeCoverScale
      one_le_chargeCoverExponent (singleSiteEnsemble_pinned hf)
        (singleSiteEnsemble_card_support hf) (combActivity N)))

/-- The admissible charge assignments. -/
def combAssignments (L N : ℕ) : Finset (Site L → ℕ) :=
  Fintype.piFinset fun _ : Site L => Finset.Icc 1 N

/-- The global weighted list of comb terminals. -/
def combBranches (L N : ℕ) : List (ℝ × SelConfig L) :=
  (combAssignments L N).toList.flatMap fun f =>
    scaleRun (∏ x, combWeight N (f x)) (combRuns N f)

theorem sum_map_flatMap {β γ : Type*} (l : List β) (g : β → List γ) (h : γ → ℝ) :
    ((l.flatMap g).map h).sum = (l.map fun a => ((g a).map h).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem mem_combAssignments {N : ℕ} {f : Site L → ℕ} (hf : f ∈ combAssignments L N) (x : Site L) :
    1 ≤ f x ∧ f x ≤ N :=
  Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hf x)

/-- **The comb branches.** -/
theorem combBranches_spec {N : ℕ} (hN : 1 ≤ N) :
    (∀ b ∈ combBranches L N, 0 < b.1 ∧ IsCombTerminal N b.2) ∧
      ((combBranches L N).map fun b => b.1).sum = 1 ∧
      ∀ φ : Site L → ℝ, ∏ x, dirichletComb N (φ x) =
        ((combBranches L N).map fun b => b.1 * chargeFactorProduct b.2.F b.2.K φ).sum := by
  classical
  refine ⟨fun b hb => ?_, ?_, fun φ => ?_⟩
  · obtain ⟨f, hfmem, hb⟩ := List.mem_flatMap.mp hb
    have hf := mem_combAssignments (Finset.mem_toList.mp hfmem)
    have hf1 : ∀ x, 1 ≤ f x := fun x => (hf x).1
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
    obtain ⟨hw, hA, hreach⟩ := (combRuns_spec N hf1).1 b' hb'
    exact ⟨mul_pos (Finset.prod_pos fun x _ => combWeight_pos hN _) hw, hA, f, hf, hreach⟩
  · unfold combBranches
    rw [sum_map_flatMap]
    have : ∀ f ∈ (combAssignments L N).toList,
        ((scaleRun (∏ x, combWeight N (f x)) (combRuns N f)).map fun b => b.1).sum =
          ∏ x, combWeight N (f x) := by
      intro f hfmem
      have hf := mem_combAssignments (Finset.mem_toList.mp hfmem)
      rw [sum_scaleRun_weight, (combRuns_spec N fun x => (hf x).1).2.1, mul_one]
    rw [List.map_congr_left this, Finset.sum_map_toList]
    unfold combAssignments
    rw [← Finset.prod_univ_sum]
    exact Finset.prod_eq_one fun x _ => sum_combWeight hN
  · rw [prod_dirichletComb_eq hN]
    unfold combBranches
    rw [sum_map_flatMap]
    have : ∀ f ∈ (combAssignments L N).toList,
        ((scaleRun (∏ x, combWeight N (f x)) (combRuns N f)).map
          fun b => b.1 * chargeFactorProduct b.2.F b.2.K φ).sum =
          (∏ x, combWeight N (f x)) *
            chargeFactorProduct (singleSiteEnsemble f) (combActivity N) φ := by
      intro f hfmem
      have hf := mem_combAssignments (Finset.mem_toList.mp hfmem)
      have hspec := combRuns_spec N fun x => (hf x).1
      rw [sum_scaleRun_prod, ← hspec.2.2 φ]
      simp [SelConfig.start]
    rw [List.map_congr_left this, Finset.sum_map_toList]
    rfl

/-! ### Neutralization on the wired carrier -/

/-- The bounded-face part of a wired-carrier density. -/
def siteRestrict (ϱ : RotatorDualFace L → ℤ) : ChargeDensity L := fun x => ϱ (some x)

@[simp] theorem siteRestrict_neutralize (ρ : ChargeDensity L) :
    siteRestrict (neutralizeAtWiredRoot ρ) = ρ := by
  funext x
  rfl

theorem neutralizeAtWiredRoot_injective :
    Function.Injective (neutralizeAtWiredRoot (L := L)) := fun ρ σ h => by
  rw [← siteRestrict_neutralize ρ, ← siteRestrict_neutralize σ, h]

theorem prod_pinnedCombLam (N : ℕ) (ψ : RotatorDualFace L → ℝ) :
    ∏ k, pinnedCombLam L N k (ψ k) = ∏ x : Fin L × Fin L, dirichletComb N (ψ (some x)) := by
  rw [Fintype.prod_option]
  simp [pinnedCombLam]

/-- A charge-factor product read on the wired carrier, for a root-pinned field. -/
theorem chargeFactorProduct_eq_neutralized (F : Finset (ChargeDensity L))
    (K : ChargeDensity L → ℝ) (ψ : RotatorDualFace L → ℝ) (hψ : ψ none = 0) :
    chargeFactorProduct F K (fun x => ψ (some x)) =
      ∏ ϱ ∈ F.image neutralizeAtWiredRoot,
        (1 + K (siteRestrict ϱ) * Real.cos (∑ j, ψ j * (ϱ j : ℝ))) := by
  rw [Finset.prod_image fun ρ _ σ _ h => neutralizeAtWiredRoot_injective h]
  unfold chargeFactorProduct
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [chargeFactor, siteRestrict_neutralize, pairing_neutralizeAtWiredRoot]
  simp [chargePhase, relativeToWiredRoot, hψ]

/-- **The rooted comb expansion.** For root-pinned fields the wired comb product is the convex
combination of the neutralized terminal ensembles. -/
theorem prod_pinnedCombLam_eq_branches {N : ℕ} (hN : 1 ≤ N) (ψ : RotatorDualFace L → ℝ)
    (hψ : ψ none = 0) :
    ∏ k, pinnedCombLam L N k (ψ k) =
      ((combBranches L N).map fun b => b.1 *
        ∏ ϱ ∈ b.2.F.image neutralizeAtWiredRoot,
          (1 + b.2.K (siteRestrict ϱ) * Real.cos (∑ j, ψ j * (ϱ j : ℝ)))).sum := by
  rw [prod_pinnedCombLam, (combBranches_spec hN).2.2 (fun x => ψ (some x))]
  congr 1
  apply List.map_congr_left
  intro b _
  rw [chargeFactorProduct_eq_neutralized _ _ _ hψ]

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
