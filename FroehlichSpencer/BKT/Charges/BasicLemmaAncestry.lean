/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.BasicLemmaIdentity

/-! # Merge histories for the Basic Lemma

The tree records the actual selected conflict at each merge. A kept factor
retains its tree; a sum or difference branch joins the two parent trees.
Substitution composes a later expansion's history through a one-step branch. -/

@[expose] public section

namespace FroehlichSpencer.BKT

/--
A factor's binary ancestry in a pair-rewrite branch.

Leaves are factors
of the original ensemble.
-/
inductive ChargeMergeHistory {L : ℕ} (boundary : SquareBoundary) (k : ℕ)
    (E : ChargeEnsemble L) : ChargeDensity L → Type where
  | leaf (ρ : ChargeDensity L) (hρ : ρ ∈ E) : ChargeMergeHistory boundary k E ρ
  | add {ρ σ : ChargeDensity L} (hρ : ChargeMergeHistory boundary k E ρ)
      (hσ : ChargeMergeHistory boundary k E σ)
      (hconflict : densityDistance boundary L ρ σ ≤ 2 ^ k) :
      ChargeMergeHistory boundary k E (ρ + σ)
  | sub {ρ σ : ChargeDensity L} (hρ : ChargeMergeHistory boundary k E ρ)
      (hσ : ChargeMergeHistory boundary k E σ)
      (hconflict : densityDistance boundary L ρ σ ≤ 2 ^ k) :
      ChargeMergeHistory boundary k E (ρ - σ)
  | keepLeft {ρ σ : ChargeDensity L}
      (hρ : ChargeMergeHistory boundary k E ρ)
      (hσ : ChargeMergeHistory boundary k E σ)
      (hconflict : densityDistance boundary L ρ σ ≤ 2 ^ k) :
      ChargeMergeHistory boundary k E ρ
  | keepRight {ρ σ : ChargeDensity L}
      (hρ : ChargeMergeHistory boundary k E ρ)
      (hσ : ChargeMergeHistory boundary k E σ)
      (hconflict : densityDistance boundary L ρ σ ≤ 2 ^ k) :
      ChargeMergeHistory boundary k E σ

/-- The original input factors at the leaves of a merge-history tree. -/
def ChargeMergeHistory.leaves {L : ℕ} {boundary : SquareBoundary} {k : ℕ}
    {E : ChargeEnsemble L} {ρ : ChargeDensity L}
    (h : ChargeMergeHistory boundary k E ρ) : ChargeEnsemble L :=
  match h with
  | .leaf ρ _ => {ρ}
  | .add hρ hσ _ => hρ.leaves ∪ hσ.leaves
  | .sub hρ hσ _ => hρ.leaves ∪ hσ.leaves
  | .keepLeft hρ _ _ => hρ.leaves
  | .keepRight _ hσ _ => hσ.leaves

/-- The number of factors of three contributed along one factor's history.
Merge branches add the two inherited counts and one; keep branches inherit
only the kept coefficient and add one. -/
def ChargeMergeHistory.multiplierCount {L : ℕ} {boundary : SquareBoundary}
    {k : ℕ} {E : ChargeEnsemble L} {ρ : ChargeDensity L}
    (h : ChargeMergeHistory boundary k E ρ) : ℕ :=
  match h with
  | .leaf _ _ => 0
  | .add hρ hσ _ => hρ.multiplierCount + hσ.multiplierCount + 1
  | .sub hρ hσ _ => hρ.multiplierCount + hσ.multiplierCount + 1
  | .keepLeft hρ _ _ => hρ.multiplierCount + 1
  | .keepRight _ hσ _ => hσ.multiplierCount + 1

/-- Number of actual merge nodes in a factor's recorded history. -/
def ChargeMergeHistory.mergeCount {L : ℕ} {boundary : SquareBoundary}
    {k : ℕ} {E : ChargeEnsemble L} {ρ : ChargeDensity L}
    (h : ChargeMergeHistory boundary k E ρ) : ℕ :=
  match h with
  | .leaf _ _ => 0
  | .add hρ hσ _ => hρ.mergeCount + hσ.mergeCount + 1
  | .sub hρ hσ _ => hρ.mergeCount + hσ.mergeCount + 1
  | .keepLeft hρ _ _ => hρ.mergeCount
  | .keepRight _ hσ _ => hσ.mergeCount

/-- Number of keep steps on the kept factor's coefficient lineage. -/
def ChargeMergeHistory.keepCount {L : ℕ} {boundary : SquareBoundary}
    {k : ℕ} {E : ChargeEnsemble L} {ρ : ChargeDensity L}
    (h : ChargeMergeHistory boundary k E ρ) : ℕ :=
  match h with
  | .leaf _ _ => 0
  | .add hρ hσ _ => hρ.keepCount + hσ.keepCount
  | .sub hρ hσ _ => hρ.keepCount + hσ.keepCount
  | .keepLeft hρ _ _ => hρ.keepCount + 1
  | .keepRight _ hσ _ => hσ.keepCount + 1

/-- Every factor-of-three multiplier is either contributed by a merge or a
keep event in the recorded history. -/
theorem ChargeMergeHistory.multiplierCount_eq_merge_add_keep {L : ℕ}
    {boundary : SquareBoundary} {k : ℕ} {E : ChargeEnsemble L}
    {ρ : ChargeDensity L} (h : ChargeMergeHistory boundary k E ρ) :
    h.multiplierCount = h.mergeCount + h.keepCount := by
  induction h with
  | leaf ρ hρ => rfl
  | add hρ hσ hconflict ihρ ihσ => simp [multiplierCount, mergeCount, keepCount, ihρ, ihσ]; omega
  | sub hρ hσ hconflict ihρ ihσ => simp [multiplierCount, mergeCount, keepCount, ihρ, ihσ]; omega
  | keepLeft hρ hσ hconflict ihρ ihσ => simp [multiplierCount, mergeCount, keepCount, ihρ]; omega
  | keepRight hρ hσ hconflict ihρ ihσ => simp [multiplierCount, mergeCount, keepCount, ihσ]; omega

/-- Every merge-history leaf belongs to its original input ensemble. -/
theorem ChargeMergeHistory.leaves_subset {L : ℕ} {boundary : SquareBoundary}
    {k : ℕ} {E : ChargeEnsemble L} {ρ : ChargeDensity L}
    (h : ChargeMergeHistory boundary k E ρ) : h.leaves ⊆ E := by
  induction h with
  | leaf ρ hρ => simpa [ChargeMergeHistory.leaves] using hρ
  | add hρ hσ hconflict ihρ ihσ =>
      exact Finset.union_subset ihρ ihσ
  | sub hρ hσ hconflict ihρ ihσ =>
      exact Finset.union_subset ihρ ihσ
  | keepLeft hρ hσ hconflict ihρ ihσ => exact ihρ
  | keepRight hρ hσ hconflict ihρ ihσ => exact ihσ

/-- Merge-history trees always have at least one original input leaf. -/
theorem ChargeMergeHistory.leaves_nonempty {L : ℕ}
    {boundary : SquareBoundary} {k : ℕ} {E : ChargeEnsemble L}
    {ρ : ChargeDensity L} (h : ChargeMergeHistory boundary k E ρ) :
    h.leaves.Nonempty := by
  induction h with
  | leaf ρ _ => simp [ChargeMergeHistory.leaves]
  | add hρ hσ hconflict ihρ ihσ =>
      obtain ⟨a, ha⟩ := ihρ
      exact ⟨a, Finset.mem_union_left _ ha⟩
  | sub hρ hσ hconflict ihρ ihσ =>
      obtain ⟨a, ha⟩ := ihρ
      exact ⟨a, Finset.mem_union_left _ ha⟩
  | keepLeft hρ hσ hconflict ihρ ihσ => exact ihρ
  | keepRight hρ hσ hconflict ihρ ihσ => exact ihσ

/-- Replace the leaves of a branch history by histories over an earlier
ensemble. This is the ancestry composition used by the recursive expansion. -/
def ChargeMergeHistory.substitute {L : ℕ} {boundary : SquareBoundary}
    {k : ℕ} {E F : ChargeEnsemble L}
    (replace : ∀ ρ ∈ F, ChargeMergeHistory boundary k E ρ)
    {ρ : ChargeDensity L} (h : ChargeMergeHistory boundary k F ρ) :
    ChargeMergeHistory boundary k E ρ :=
  match h with
  | .leaf ρ hρ => replace ρ hρ
  | .add hρ hσ hconflict =>
      .add (ChargeMergeHistory.substitute replace hρ)
        (ChargeMergeHistory.substitute replace hσ) hconflict
  | .sub hρ hσ hconflict =>
      .sub (ChargeMergeHistory.substitute replace hρ)
        (ChargeMergeHistory.substitute replace hσ) hconflict
  | .keepLeft hρ hσ hconflict =>
      .keepLeft (ChargeMergeHistory.substitute replace hρ)
        (ChargeMergeHistory.substitute replace hσ) hconflict
  | .keepRight hρ hσ hconflict =>
      .keepRight (ChargeMergeHistory.substitute replace hρ)
        (ChargeMergeHistory.substitute replace hσ) hconflict

end FroehlichSpencer.BKT

end
