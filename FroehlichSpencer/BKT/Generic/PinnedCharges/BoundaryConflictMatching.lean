/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Finite maximum conflict matchings

The Appendix D entropy recurrence groups nearby fine squares in pairs. This
module isolates the finite matching fact used by that grouping: a maximum
matching leaves no conflicting pair of unmatched vertices, and its edge
count is at most half the number of vertices.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

/-- A two-vertex edge in a finite conflict graph. -/
def IsBoundaryConflictEdge {α : Type*} [DecidableEq α]
    (V : Finset α) (conflict : α → α → Prop) (e : Finset α) : Prop :=
  e ⊆ V ∧ e.card = 2 ∧
    ∀ x ∈ e, ∀ y ∈ e, x ≠ y → conflict x y

/-- A pairwise disjoint family of conflict edges. -/
def IsBoundaryConflictMatching {α : Type*} [DecidableEq α]
    (V : Finset α) (conflict : α → α → Prop) (M : Finset (Finset α)) : Prop :=
  (∀ e ∈ M, IsBoundaryConflictEdge V conflict e) ∧
    ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

/-- Vertices incident to an edge in a finite matching. -/
def boundaryConflictMatchedVertices {α : Type*} [DecidableEq α]
    (M : Finset (Finset α)) : Finset α := M.biUnion id

/-- A maximum matching of a finite conflict graph leaves no adjacent unmatched
vertices and has at most half as many edges as vertices. -/
theorem exists_maximumBoundaryConflictMatching {α : Type*} [Fintype α]
    [DecidableEq α] (V : Finset α) (conflict : α → α → Prop)
    [DecidableRel conflict]
    (hsymm : ∀ x y, conflict x y → conflict y x) :
    ∃ M : Finset (Finset α),
      IsBoundaryConflictMatching V conflict M ∧
      (∀ x ∈ V, x ∉ boundaryConflictMatchedVertices M →
        ∀ y ∈ V, y ∉ boundaryConflictMatchedVertices M → x ≠ y → ¬ conflict x y) ∧
      2 * M.card ≤ V.card := by
  classical
  let edges := V.powerset.filter fun e => IsBoundaryConflictEdge V conflict e
  let candidates := edges.powerset.filter fun M => IsBoundaryConflictMatching V conflict M
  have hCandidates : candidates.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by simp), ?_⟩⟩
    simp [IsBoundaryConflictMatching]
  let cardValues := candidates.image Finset.card
  have hCardValues : cardValues.Nonempty := Finset.image_nonempty.mpr hCandidates
  let maxCard := cardValues.max' hCardValues
  obtain ⟨M, hMmem, hMcard⟩ := Finset.mem_image.mp
    (Finset.max'_mem cardValues hCardValues)
  have hMmatch : IsBoundaryConflictMatching V conflict M :=
    (Finset.mem_filter.mp hMmem).2
  have hMsubsetEdges : M ⊆ edges :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hMmem).1
  have hmaxCard : ∀ M' : Finset (Finset α),
      IsBoundaryConflictMatching V conflict M' → M' ⊆ edges → M'.card ≤ M.card := by
    intro M' hM'match hM'sub
    have hM'cand : M' ∈ candidates :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hM'sub, hM'match⟩
    have hM'card : M'.card ∈ cardValues :=
      Finset.mem_image.mpr ⟨M', hM'cand, rfl⟩
    have hle := Finset.le_max' cardValues M'.card hM'card
    rw [← hMcard] at hle
    exact hle
  have hnoUnmatchedEdge : ∀ x ∈ V,
      x ∉ boundaryConflictMatchedVertices M →
      ∀ y ∈ V, y ∉ boundaryConflictMatchedVertices M → x ≠ y → ¬ conflict x y := by
    intro x hx hxUnmatched y hy hyUnmatched hxy hxyConflict
    let e : Finset α := {x, y}
    have heSub : e ⊆ V := by
      intro z hz
      simp [e] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    have heCard : e.card = 2 := by simp [e, hxy]
    have heConflict : ∀ a ∈ e, ∀ b ∈ e, a ≠ b → conflict a b := by
      intro a ha b hb hab
      simp only [e, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with ha | ha
      · subst a
        rcases hb with hb | hb
        · subst b
          exact (hab rfl).elim
        · subst b
          exact hxyConflict
      · subst a
        rcases hb with hb | hb
        · subst b
          exact hsymm x y hxyConflict
        · subst b
          exact (hab rfl).elim
    have heEdge : IsBoundaryConflictEdge V conflict e := ⟨heSub, heCard, heConflict⟩
    have heNotM : e ∉ M := by
      intro he
      apply hxUnmatched
      exact Finset.mem_biUnion.mpr ⟨e, he, by simp [e]⟩
    have heDisjoint : ∀ f ∈ M, Disjoint e f := by
      intro f hf
      rw [Finset.disjoint_left]
      intro z hze hzf
      have hzx : z = x ∨ z = y := by simpa [e] using hze
      rcases hzx with rfl | rfl
      · exact hxUnmatched (Finset.mem_biUnion.mpr ⟨f, hf, hzf⟩)
      · exact hyUnmatched (Finset.mem_biUnion.mpr ⟨f, hf, hzf⟩)
    have hAugMatch : IsBoundaryConflictMatching V conflict (insert e M) := by
      refine ⟨?_, ?_⟩
      · intro f hf
        rcases Finset.mem_insert.mp hf with hfe | hfM
        · subst f
          exact heEdge
        · exact hMmatch.1 f hfM
      · intro f hf g hg hne
        rcases Finset.mem_insert.mp hf with rfl | hfM
        · rcases Finset.mem_insert.mp hg with rfl | hgM
          · exact (hne rfl).elim
          · exact heDisjoint g hgM
        · rcases Finset.mem_insert.mp hg with rfl | hgM
          · exact (heDisjoint f hfM).symm
          · exact hMmatch.2 f hfM g hgM hne
    have hAugSubset : insert e M ⊆ edges := by
      intro f hf
      rcases Finset.mem_insert.mp hf with hfe | hfM
      · subst f
        exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr heSub, heEdge⟩
      · exact hMsubsetEdges hfM
    have hAugCand : insert e M ∈ candidates :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hAugSubset, hAugMatch⟩
    have hAugCard : (insert e M).card = M.card + 1 := Finset.card_insert_of_notMem heNotM
    have hAugValue : (insert e M).card ∈ cardValues :=
      Finset.mem_image.mpr ⟨insert e M, hAugCand, rfl⟩
    have hAugLe := Finset.le_max' cardValues (insert e M).card hAugValue
    rw [← hMcard] at hAugLe
    omega
  have hMedgeDisjoint : (M : Set (Finset α)).PairwiseDisjoint id := by
    intro e he f hf hne
    exact hMmatch.2 e he f hf hne
  have hUnionCard : (M.biUnion id).card = ∑ e ∈ M, e.card :=
    Finset.card_biUnion hMedgeDisjoint
  have hSumCard : (∑ e ∈ M, e.card) = 2 * M.card := by
    calc
      (∑ e ∈ M, e.card) = ∑ e ∈ M, 2 := by
        apply Finset.sum_congr rfl
        intro e he
        exact (hMmatch.1 e he).2.1
      _ = 2 * M.card := by simp [Nat.mul_comm]
  have hUnionSubset : M.biUnion id ⊆ V := by
    intro x hx
    obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hx
    exact (hMmatch.1 e he).1 hxe
  have hUnionLe := Finset.card_le_card hUnionSubset
  refine ⟨M, hMmatch, hnoUnmatchedEdge, ?_⟩
  calc
    2 * M.card = ∑ e ∈ M, e.card := hSumCard.symm
    _ = (M.biUnion id).card := hUnionCard.symm
    _ ≤ V.card := hUnionLe

/-- If every vertex outside a core has a conflict neighbor, a maximum matching
on the non-core vertices sends each unmatched vertex to either the core or a
matched vertex. -/
theorem unmatchedBoundaryConflictNeighbor_mem_core_or_matched
    {α : Type*} [Fintype α] [DecidableEq α]
    (C Q V : Finset α) (conflict : α → α → Prop) [DecidableRel conflict]
    (hCV : C = Q ∪ V)
    (M : Finset (Finset α))
    (hnoUnmatched : ∀ x ∈ V,
      x ∉ boundaryConflictMatchedVertices M →
      ∀ y ∈ V, y ∉ boundaryConflictMatchedVertices M → x ≠ y → ¬ conflict x y)
    (hneighbor : ∀ x ∈ V, ∃ y ∈ C, y ≠ x ∧ conflict x y)
    {x : α} (hx : x ∈ V) (hxUnmatched : x ∉ boundaryConflictMatchedVertices M) :
    ∃ y ∈ Q ∪ boundaryConflictMatchedVertices M, conflict x y := by
  obtain ⟨y, hyC, hyne, hxy⟩ := hneighbor x hx
  have hyQV : y ∈ Q ∨ y ∈ V := by
    rw [hCV] at hyC
    simpa using hyC
  rcases hyQV with hyQ | hyV
  · exact ⟨y, Finset.mem_union.mpr (Or.inl hyQ), hxy⟩
  · by_cases hyMatched : y ∈ boundaryConflictMatchedVertices M
    · exact ⟨y, Finset.mem_union.mpr (Or.inr hyMatched), hxy⟩
    · exact (hnoUnmatched x hx hxUnmatched y hyV hyMatched (Ne.symm hyne) hxy).elim

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
