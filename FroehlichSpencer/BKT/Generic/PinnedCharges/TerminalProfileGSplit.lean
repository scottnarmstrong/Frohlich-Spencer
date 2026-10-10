/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileGInterface

/-!
# Splitting the corrected profile target into its two independent parts (TW1G)

The selected squares `P'_j(ρ)` (the terminal decomposition's choice of minimum cover, `M = 2^16`, `α = 7/4`, scales
`1 ≤ j ≤ n_Λ`) split into **good** ones (charged restriction `ρ|_s`) and **bad** ones (neutral
restriction): `layerSelectedSum = goodSelectedSum + badSelectedSum`.

`pinnedTerminalProfilesW_of_split`: (A) and (B) give `PinnedTerminalProfilesW` with `c_P = 1/3`,
hence Theorem C (`theoremC_of_split`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open Filter
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Transition
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Lattice2D

variable {L : ℕ}

/-- The selected squares of `ϱ|faces` at scale `j` (the terminal decomposition's cover, `M = 2^16`, `α = 7/4`). -/
def selectedSquares (ϱ : RotatorDualFace L → ℤ) (j : ℕ) : Finset (Finset (Site L)) :=
  pinnedPPrime (chargeCoverScale : ℝ) chargeCoverExponent j (siteRestrict ϱ)
    (boundaryEntropyMinimumCover (siteRestrict ϱ) j)

/-- Number of selected squares with charged restriction, scales `1 … n_Λ`. -/
def goodSelectedSum (ϱ : RotatorDualFace L → ℤ) : ℝ := by
  classical
  exact ∑ j ∈ Finset.Icc 1 (layerCutoff ϱ),
    (((selectedSquares ϱ j).filter fun s =>
      totalCharge (chargeRestriction (siteRestrict ϱ) s) ≠ 0).card : ℝ)

/-- Number of selected squares with neutral restriction, scales `1 … n_Λ`. -/
def badSelectedSum (ϱ : RotatorDualFace L → ℤ) : ℝ := by
  classical
  exact ∑ j ∈ Finset.Icc 1 (layerCutoff ϱ),
    (((selectedSquares ϱ j).filter fun s =>
      ¬ totalCharge (chargeRestriction (siteRestrict ϱ) s) ≠ 0).card : ℝ)

theorem layerSelectedSum_eq_good_add_bad (ϱ : RotatorDualFace L → ℤ) :
    layerSelectedSum ϱ = goodSelectedSum ϱ + badSelectedSum ϱ := by
  classical
  unfold layerSelectedSum goodSelectedSum badSelectedSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold boundaryEntropySelectedCount selectedSquares
  rw [← Nat.cast_add, Finset.card_filter_add_card_filter_not]

/-- **Part (A)**: the profile family with a third of the good squares. -/
structure TerminalProfilesG (L : ℕ) (α K₀ K₁ : ℝ) (F : Finset (ChargeDensity L))
    extends TerminalProfiles L α K₀ K₁ 0 F where
  countG : ∀ ϱ ∈ F.image neutralizeAtWiredRoot,
    goodSelectedSum ϱ ≤ 3 * (Fintype.card (ι ϱ) : ℝ)

/-- Part (A) on every comb terminal. -/
def PinnedTerminalProfilesG (α K₀ K₁ : ℝ) (L₀ : ℕ) : Prop :=
  ∀ L : ℕ, L₀ ≤ L → ∀ N : ℕ, 1 ≤ N → ∀ T : SelConfig L, IsCombTerminal N T →
    Nonempty (TerminalProfilesG L α K₀ K₁ T.F)

/-- **Part (B)**: the bad selected squares are at most `‖ϱ‖₁` on every comb terminal. -/
def BadSelectedBound : Prop :=
  ∀ (L N : ℕ) (T : SelConfig L), IsCombTerminal N T →
    ∀ ϱ ∈ T.F.image neutralizeAtWiredRoot, badSelectedSum ϱ ≤ ∑ j, |(ϱ j : ℝ)|

theorem badSelectedSum_nonneg (ϱ : RotatorDualFace L → ℤ) : 0 ≤ badSelectedSum ϱ := by
  unfold badSelectedSum
  exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- **(A) and (B) give the corrected profile hypothesis** with `c_P = 1/3`. -/
theorem pinnedTerminalProfilesW_of_split {α K₀ K₁ : ℝ} {L₀ : ℕ}
    (hA : PinnedTerminalProfilesG α K₀ K₁ L₀) (hB : BadSelectedBound) :
    PinnedTerminalProfilesW α K₀ K₁ (1 / 3) L₀ := by
  intro L hL N hN T hT
  obtain ⟨P⟩ := hA L hL N hN T hT
  refine ⟨{ P.toTerminalProfiles with countW := fun ϱ hϱ => ?_ }⟩
  have hg := P.countG ϱ hϱ
  have hb := hB L N T hT ϱ hϱ
  have hb0 := badSelectedSum_nonneg ϱ
  rw [layerSelectedSum_eq_good_add_bad]
  change 1 / 3 * (goodSelectedSum ϱ + badSelectedSum ϱ) ≤
    (Fintype.card (P.ι ϱ) : ℝ) + ∑ j, |(ϱ j : ℝ)|
  linarith

/-- **FS81 Theorem C from parts (A) and (B).** -/
theorem theoremC_of_split {α K₀ K₁ : ℝ} {L₀ : ℕ} (hα : 1 < α)
    (hA : PinnedTerminalProfilesG α K₀ K₁ L₀) (hB : BadSelectedBound) :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ), Tendsto β' atTop atTop ∧
      ∀ β (hβ : 0 ≤ β), β₀ ≤ β → 1 / (4 * Real.pi) < β' β ∧
        ∀ (ξ : ℤ) (u v : ℤ × ℤ),
          Real.exp (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) *
              ((l1Norm (u - v) : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) ≤
            freeTwoPointLimit β hβ ξ u v :=
  theoremC_of_pinnedTerminalProfilesW hα (by norm_num) (pinnedTerminalProfilesW_of_split hA hB)

/-- **The Kosterlitz–Thouless transition from parts (A) and (B).** -/
theorem exists_transition_of_split {α K₀ K₁ : ℝ} {L₀ : ℕ} (hα : 1 < α)
    (hA : PinnedTerminalProfilesG α K₀ K₁ L₀) (hB : BadSelectedBound) :
    ∃ βc : ℝ, 1 / 2 ≤ βc ∧ (∀ β (hβ : 0 ≤ β), β < βc → HasExpDecay β hβ) ∧
      (∀ β (hβ : 0 ≤ β), βc < β → ¬ HasExpDecay β hβ ∧ HasNoLongRangeOrder β hβ) :=
  exists_transition_of_pinnedTerminalProfilesW hα (by norm_num)
    (pinnedTerminalProfilesW_of_split hA hB)

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
