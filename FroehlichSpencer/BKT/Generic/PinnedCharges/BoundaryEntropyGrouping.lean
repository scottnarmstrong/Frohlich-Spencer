/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryConflictMatching
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEntropyGeometry

/-! # Matching groups for the boundary entropy count

Core vertices and matching edges index groups. Every unmatched vertex is
assigned to the group containing one of its conflicting core or matched
neighbors.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

/-- A pair of cover squares conflicts when their Euclidean set-distance is
below the matching radius, in either orientation. -/
def IsBoundarySquareConflict {L : ℕ} (R : ℝ)
    (s t : Finset (Site L)) : Prop :=
  euclideanSetDistance s t < R ∨ euclideanSetDistance t s < R

/-- The symmetric conflict relation used to build the maximum matching. -/
theorem boundarySquareConflict_symmetric {L : ℕ} (R : ℝ)
    (s t : Finset (Site L)) :
    IsBoundarySquareConflict R s t → IsBoundarySquareConflict R t s := by
  rintro (h | h)
  · exact Or.inr h
  · exact Or.inl h

/-- The index type for groups based at a core vertex or matching edge. -/
abbrev BoundaryGroupIndex {α : Type*} (Q : Finset α)
    (M : Finset (Finset α)) := {q // q ∈ Q} ⊕ {e // e ∈ M}

/-- Vertices of V not covered by a matching edge. -/
def boundaryUnmatchedVertices {α : Type*} [DecidableEq α]
    (V : Finset α) (M : Finset (Finset α)) : Finset α :=
  V \ boundaryConflictMatchedVertices M

/-- The base of a group: one core vertex or the endpoints of a matching edge. -/
def boundaryGroupBase {α : Type*} [DecidableEq α]
    (Q : Finset α) (M : Finset (Finset α)) :
    BoundaryGroupIndex Q M → Finset α
  | .inl q => {q.1}
  | .inr e => e.1

/-- Finite set of valid core-vertex and matching-edge group indices. -/
def boundaryGroupIndices {α : Type*} [DecidableEq α]
    (Q : Finset α) (M : Finset (Finset α)) :
    Finset (BoundaryGroupIndex Q M) := by
  classical
  exact Q.attach.image Sum.inl ∪ M.attach.image Sum.inr

/-- A chosen core or matched conflict neighbor, together with its valid group
index. The witness retains the incidence fact used in the diameter estimate. -/
noncomputable def boundaryGroupOwnerWitness {α : Type*} [Fintype α]
    [DecidableEq α] (Q V : Finset α) (M : Finset (Finset α))
    (conflict : α → α → Prop)
    (hneighbor : ∀ x ∈ boundaryUnmatchedVertices V M,
      ∃ y ∈ Q ∪ boundaryConflictMatchedVertices M, conflict x y)
    (x : {x // x ∈ boundaryUnmatchedVertices V M}) :
    Σ i : {i : BoundaryGroupIndex Q M // i ∈ boundaryGroupIndices Q M},
      {y : α // y ∈ boundaryGroupBase Q M i.1 ∧ conflict x.1 y} := by
  classical
  let y := Classical.choose (hneighbor x.1 x.2)
  have hy := Classical.choose_spec (hneighbor x.1 x.2)
  by_cases hyQ : y ∈ Q
  · let i : BoundaryGroupIndex Q M := .inl ⟨y, hyQ⟩
    have hi : i ∈ boundaryGroupIndices Q M := by
      unfold boundaryGroupIndices
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      exact ⟨⟨y, hyQ⟩, Finset.mem_attach _ _, rfl⟩
    refine ⟨⟨i, hi⟩, ⟨y, ?_, hy.2⟩⟩
    simp [boundaryGroupBase, i]
  · have hyMatched : y ∈ boundaryConflictMatchedVertices M := by
      rcases Finset.mem_union.mp hy.1 with h | h
      · exact (hyQ h).elim
      · exact h
    have hEdge : ∃ e ∈ M, y ∈ e := Finset.mem_biUnion.mp hyMatched
    let e := Classical.choose hEdge
    have he := Classical.choose_spec hEdge
    let i : BoundaryGroupIndex Q M := .inr ⟨e, he.1⟩
    have hi : i ∈ boundaryGroupIndices Q M := by
      unfold boundaryGroupIndices
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      exact ⟨⟨e, he.1⟩, Finset.mem_attach _ _, rfl⟩
    refine ⟨⟨i, hi⟩, ⟨y, ?_, hy.2⟩⟩
    simpa [boundaryGroupBase, i] using he.2

/-- Assign every unmatched vertex to the group containing its chosen neighbor. -/
noncomputable def boundaryGroupOwner {α : Type*} [Fintype α] [DecidableEq α]
    (Q V : Finset α) (M : Finset (Finset α)) (conflict : α → α → Prop)
    (hneighbor : ∀ x ∈ boundaryUnmatchedVertices V M,
      ∃ y ∈ Q ∪ boundaryConflictMatchedVertices M, conflict x y) :
    {x // x ∈ boundaryUnmatchedVertices V M} → BoundaryGroupIndex Q M :=
  fun x => (boundaryGroupOwnerWitness Q V M conflict hneighbor x).1.1

/-- The constructed owner is a valid group index. -/
theorem boundaryGroupOwner_mem_indices {α : Type*} [Fintype α] [DecidableEq α]
    (Q V : Finset α) (M : Finset (Finset α)) (conflict : α → α → Prop)
    (hneighbor : ∀ x ∈ boundaryUnmatchedVertices V M,
      ∃ y ∈ Q ∪ boundaryConflictMatchedVertices M, conflict x y)
    (x : {x // x ∈ boundaryUnmatchedVertices V M}) :
    boundaryGroupOwner Q V M conflict hneighbor x ∈ boundaryGroupIndices Q M :=
  (boundaryGroupOwnerWitness Q V M conflict hneighbor x).1.2

/-- Each unmatched vertex conflicts with a vertex in its assigned base group. -/
theorem boundaryGroupOwner_neighbor {α : Type*} [Fintype α] [DecidableEq α]
    (Q V : Finset α) (M : Finset (Finset α)) (conflict : α → α → Prop)
    (hneighbor : ∀ x ∈ boundaryUnmatchedVertices V M,
      ∃ y ∈ Q ∪ boundaryConflictMatchedVertices M, conflict x y)
    (x : {x // x ∈ boundaryUnmatchedVertices V M}) :
    ∃ y ∈ boundaryGroupBase Q M (boundaryGroupOwner Q V M conflict hneighbor x),
      conflict x.1 y := by
  exact ⟨(boundaryGroupOwnerWitness Q V M conflict hneighbor x).2.1,
    (boundaryGroupOwnerWitness Q V M conflict hneighbor x).2.2.1,
    (boundaryGroupOwnerWitness Q V M conflict hneighbor x).2.2.2⟩

/-- Unmatched vertices assigned to one group. -/
def boundaryGroupAssigned {α : Type*} [Fintype α] [DecidableEq α]
    (Q V : Finset α) (M : Finset (Finset α))
    (owner : {x // x ∈ boundaryUnmatchedVertices V M} → BoundaryGroupIndex Q M)
    (i : BoundaryGroupIndex Q M) : Finset α :=
  ((Finset.univ.filter fun x : {x // x ∈ boundaryUnmatchedVertices V M} =>
      owner x = i).image Subtype.val)

/-- Full group based at a core vertex or matching edge. -/
def boundaryGroup {α : Type*} [Fintype α] [DecidableEq α]
    (Q V : Finset α) (M : Finset (Finset α))
    (owner : {x // x ∈ boundaryUnmatchedVertices V M} → BoundaryGroupIndex Q M)
    (i : BoundaryGroupIndex Q M) : Finset α :=
  boundaryGroupBase Q M i ∪ boundaryGroupAssigned Q V M owner i

/-- Finite family of matching groups. -/
def boundaryGroupFamily {α : Type*} [Fintype α] [DecidableEq α]
    (Q V : Finset α) (M : Finset (Finset α))
    (owner : {x // x ∈ boundaryUnmatchedVertices V M} → BoundaryGroupIndex Q M) :
    Finset (Finset α) := by
  classical
  exact (boundaryGroupIndices Q M).image (boundaryGroup Q V M owner)

/-- The number of groups is at most the number of core vertices plus matching
edges. -/
theorem boundaryGroupFamily_card_le {α : Type*} [Fintype α] [DecidableEq α]
    (Q V : Finset α) (M : Finset (Finset α))
    (owner : {x // x ∈ boundaryUnmatchedVertices V M} → BoundaryGroupIndex Q M) :
    (boundaryGroupFamily Q V M owner).card ≤ Q.card + M.card := by
  classical
  calc
    (boundaryGroupFamily Q V M owner).card ≤ (boundaryGroupIndices Q M).card :=
      Finset.card_image_le
    _ ≤ (Q.attach.image Sum.inl).card + (M.attach.image Sum.inr).card :=
      Finset.card_union_le _ _
    _ ≤ Q.card + M.card := by
      exact Nat.add_le_add
        (Finset.card_image_le.trans_eq Finset.card_attach)
        (Finset.card_image_le.trans_eq Finset.card_attach)

/-- A group family covers its core and non-core vertices if every owner is a
valid core or matching-edge index. -/
theorem boundaryGroupFamily_covers_of_partition
    {α : Type*} [Fintype α] [DecidableEq α]
    (C Q V : Finset α) (M : Finset (Finset α)) (hCV : C = Q ∪ V)
    (owner : {x // x ∈ boundaryUnmatchedVertices V M} → BoundaryGroupIndex Q M)
    (howner : ∀ x (hx : x ∈ boundaryUnmatchedVertices V M),
      owner ⟨x, hx⟩ ∈ boundaryGroupIndices Q M) :
    ∀ x ∈ C, ∃ G ∈ boundaryGroupFamily Q V M owner, x ∈ G := by
  classical
  intro x hx
  have hxQV : x ∈ Q ∨ x ∈ V := by
    rw [hCV] at hx
    exact Finset.mem_union.mp hx
  rcases hxQV with hxQ | hxV
  · let i : BoundaryGroupIndex Q M := .inl ⟨x, hxQ⟩
    refine ⟨boundaryGroup Q V M owner i, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨i,
        Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
          ⟨⟨x, hxQ⟩, Finset.mem_attach _ _, rfl⟩)), rfl⟩
    · exact Finset.mem_union.mpr (Or.inl (by simp [boundaryGroupBase, i]))
  · by_cases hxM : x ∈ boundaryConflictMatchedVertices M
    · obtain ⟨e, heM, hxe⟩ := Finset.mem_biUnion.mp hxM
      let i : BoundaryGroupIndex Q M := .inr ⟨e, heM⟩
      refine ⟨boundaryGroup Q V M owner i, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨i,
          Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
            ⟨⟨e, heM⟩, Finset.mem_attach _ _, rfl⟩)), rfl⟩
      · exact Finset.mem_union.mpr (Or.inl (by simpa [boundaryGroupBase, i] using hxe))
    · have hxU : x ∈ boundaryUnmatchedVertices V M :=
        Finset.mem_sdiff.mpr ⟨hxV, hxM⟩
      let i := owner ⟨x, hxU⟩
      refine ⟨boundaryGroup Q V M owner i, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨i, howner x hxU, rfl⟩
      · apply Finset.mem_union.mpr
        right
        apply Finset.mem_image.mpr
        refine ⟨⟨x, hxU⟩, ?_, rfl⟩
        simp [i]

/-- Every square in a matching group either belongs to its base or conflicts
with one of the base squares. -/
theorem boundaryGroup_member_link_to_base {α : Type*} [Fintype α] [DecidableEq α]
    (Q V : Finset α) (M : Finset (Finset α)) (conflict : α → α → Prop)
    (hneighbor : ∀ x ∈ boundaryUnmatchedVertices V M,
      ∃ y ∈ Q ∪ boundaryConflictMatchedVertices M, conflict x y)
    (owner : {x // x ∈ boundaryUnmatchedVertices V M} → BoundaryGroupIndex Q M)
    (hownerDef : ∀ x, owner x = boundaryGroupOwner Q V M conflict hneighbor x)
    (i : BoundaryGroupIndex Q M) {s : α} (hs : s ∈ boundaryGroup Q V M owner i) :
    ∃ t ∈ boundaryGroupBase Q M i, s = t ∨ conflict s t := by
  classical
  rcases Finset.mem_union.mp hs with hsBase | hsAssigned
  · exact ⟨s, hsBase, Or.inl rfl⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hsAssigned
    have howner : owner x = i := (Finset.mem_filter.mp hx).2
    have howner' := hownerDef x
    rw [howner'] at howner
    obtain ⟨t, ht, hconflict⟩ :=
      boundaryGroupOwner_neighbor Q V M conflict hneighbor x
    rw [howner] at ht
    exact ⟨t, ht, Or.inr hconflict⟩

/-- The base of a group contains at most two squares, and its two members
conflict when the base is a matching edge. -/
theorem boundaryGroupBase_pair_eq_or_conflict {α : Type*} [Fintype α]
    [DecidableEq α] {conflict : α → α → Prop} [DecidableRel conflict]
    (Q V : Finset α) (M : Finset (Finset α))
    (hmatch : IsBoundaryConflictMatching V conflict M)
    (i : BoundaryGroupIndex Q M) {s t : α}
    (hs : s ∈ boundaryGroupBase Q M i) (ht : t ∈ boundaryGroupBase Q M i) :
    s = t ∨ conflict s t := by
  cases i with
  | inl q =>
      simp only [boundaryGroupBase, Finset.mem_singleton] at hs ht
      subst s
      subst t
      exact Or.inl rfl
  | inr e =>
      have hsE : s ∈ e.1 := by simpa [boundaryGroupBase] using hs
      have htE : t ∈ e.1 := by simpa [boundaryGroupBase] using ht
      by_cases hst : s = t
      · exact Or.inl hst
      · exact Or.inr ((hmatch.1 e.1 e.2).2.2 s hsE t htE hst)

/-- Every square in a matching group is in the original cover when the core
and non-core families partition it and matching edges are subsets of the
non-core family. -/
theorem boundaryGroup_subset_of_partition {α : Type*} [Fintype α] [DecidableEq α]
    {conflict : α → α → Prop} [DecidableRel conflict]
    (C Q V : Finset α) (M : Finset (Finset α))
    (hQ : Q ⊆ C) (hV : V ⊆ C)
    (hmatch : IsBoundaryConflictMatching V conflict M)
    (owner : {x // x ∈ boundaryUnmatchedVertices V M} → BoundaryGroupIndex Q M)
    (i : BoundaryGroupIndex Q M) : boundaryGroup Q V M owner i ⊆ C := by
  intro s hs
  rcases Finset.mem_union.mp hs with hsBase | hsAssigned
  · cases i with
    | inl q =>
        simp only [boundaryGroupBase, Finset.mem_singleton] at hsBase
        subst s
        exact hQ q.2
    | inr e =>
        have hsE : s ∈ e.1 := by simpa [boundaryGroupBase] using hsBase
        exact hV ((hmatch.1 e.1 e.2).1 hsE)
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hsAssigned
    exact hV (Finset.mem_sdiff.mp x.2).1

/-- Every valid group index has a nonempty base, hence the full group is
nonempty. -/
theorem boundaryGroup_nonempty_of_validIndex {α : Type*} [Fintype α]
    [DecidableEq α] {conflict : α → α → Prop} [DecidableRel conflict]
    (Q V : Finset α) (M : Finset (Finset α))
    (hmatch : IsBoundaryConflictMatching V conflict M)
    (owner : {x // x ∈ boundaryUnmatchedVertices V M} → BoundaryGroupIndex Q M)
    {i : BoundaryGroupIndex Q M} (hi : i ∈ boundaryGroupIndices Q M) :
    (boundaryGroup Q V M owner i).Nonempty := by
  classical
  have hbase : (boundaryGroupBase Q M i).Nonempty := by
    cases i with
    | inl q => exact ⟨q.1, by simp [boundaryGroupBase]⟩
    | inr e =>
        have he := hmatch.1 e.1 e.2
        have hepos : 0 < e.1.card := by rw [he.2.1]; decide
        obtain ⟨x, hx⟩ := Finset.card_pos.mp hepos
        exact ⟨x, by simpa [boundaryGroupBase] using hx⟩
  obtain ⟨s, hs⟩ := hbase
  exact ⟨s, Finset.mem_union.mpr (Or.inl hs)⟩

/-- A genuine matching has at most half as many edges as vertices. -/
theorem boundaryMatching_edgeCard_le_half {α : Type*} [Fintype α] [DecidableEq α]
    {conflict : α → α → Prop} [DecidableRel conflict]
    (V : Finset α) (M : Finset (Finset α))
    (hmatch : IsBoundaryConflictMatching V conflict M) :
    M.card ≤ V.card / 2 := by
  have hdisj : (M : Set (Finset α)).PairwiseDisjoint id := by
    intro e he f hf hne
    exact hmatch.2 e he f hf hne
  have hbi : (M.biUnion id).card = ∑ e ∈ M, e.card := Finset.card_biUnion hdisj
  have hsum : (∑ e ∈ M, e.card) = 2 * M.card := by
    calc
      (∑ e ∈ M, e.card) = ∑ e ∈ M, 2 := by
        apply Finset.sum_congr rfl
        intro e he
        exact (hmatch.1 e he).2.1
      _ = 2 * M.card := by simp [Nat.mul_comm]
  have hsub : M.biUnion id ⊆ V := by
    intro x hx
    obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hx
    exact (hmatch.1 e he).1 hxe
  have hcard : 2 * M.card ≤ V.card := by
    calc
      2 * M.card = (M.biUnion id).card := by rw [hbi, hsum]
      _ ≤ V.card := Finset.card_le_card hsub
  omega

/-- The matching-group cardinal bound. -/
theorem boundaryGroupFamily_card_le_half {α : Type*} [Fintype α] [DecidableEq α]
    {conflict : α → α → Prop} [DecidableRel conflict]
    (Q V : Finset α) (M : Finset (Finset α))
    (hmatch : IsBoundaryConflictMatching V conflict M)
    (owner : {x // x ∈ boundaryUnmatchedVertices V M} → BoundaryGroupIndex Q M) :
    (boundaryGroupFamily Q V M owner).card ≤ Q.card + V.card / 2 := by
  have hcard := boundaryGroupFamily_card_le Q V M owner
  have hM := boundaryMatching_edgeCard_le_half V M hmatch
  omega

/-- The Appendix D selected family is an independent core. Isolation gives a
close neighbor for every rejected square, and a maximum matching plus the
owner construction groups all cover squares with at most
`|P'_j| + |V_j|/2` groups. -/
theorem exists_boundaryPPrime_matching_groups {L j : ℕ}
    (M α : ℝ) (hM : 0 < M) (hα : 0 < α)
    (ρ : ChargeDensity L) (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation M α N) (hρ : ρ ∈ N)
    (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C) (hcard : C.card ≠ 1) :
    let Q := pinnedPPrime M α j ρ C
    let V := C \ Q
    ∃ (matching : Finset (Finset (Finset (Site L))))
      (owner : {x // x ∈ boundaryUnmatchedVertices V matching} →
        BoundaryGroupIndex Q matching),
      IsBoundaryConflictMatching V (IsBoundarySquareConflict
        (2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α)) matching ∧
      (∃ hneighbor : ∀ x ∈ boundaryUnmatchedVertices V matching,
          ∃ y ∈ Q ∪ boundaryConflictMatchedVertices matching,
            IsBoundarySquareConflict
              (2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α) x y,
        owner = boundaryGroupOwner Q V matching
          (IsBoundarySquareConflict
            (2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α)) hneighbor ∧
        (∀ x ∈ C, ∃ G ∈ boundaryGroupFamily Q V matching owner, x ∈ G) ∧
        (boundaryGroupFamily Q V matching owner).card ≤ Q.card + V.card / 2) := by
  classical
  dsimp
  let Q := pinnedPPrime M α j ρ C
  let V := C \ Q
  let R := 2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α
  have hQsub : Q ⊆ C := pinnedPPrime_subset_cover M α j ρ C
  have hCV : C = Q ∪ V := by
    ext x
    simp only [V, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hx
      by_cases hq : x ∈ Q
      · exact Or.inl hq
      · exact Or.inr ⟨hx, hq⟩
    · rintro (hq | ⟨hc, _⟩)
      · exact hQsub hq
      · exact hc
  let conflict : Finset (Site L) → Finset (Site L) → Prop :=
    IsBoundarySquareConflict R
  have hsymm : ∀ x y, conflict x y → conflict y x := by
    intro x y hxy
    exact boundarySquareConflict_symmetric R x y hxy
  have hclose : ∀ s ∈ V, ∃ t ∈ C, t ≠ s ∧ conflict s t := by
    intro s hs
    have hsC : s ∈ C := (Finset.mem_sdiff.mp hs).1
    have hsQ : s ∉ Q := (Finset.mem_sdiff.mp hs).2
    obtain ⟨t, ht, hts, hdist⟩ :=
      boundaryPPrime_complement_has_close_neighbor M α hM hα ρ N hN hρ C hC hcard hsC hsQ
    exact ⟨t, ht, hts, Or.inl hdist⟩
  obtain ⟨matching, hmatching, hmax, _hmatchingCard⟩ :=
    exists_maximumBoundaryConflictMatching V conflict hsymm
  have hneighbor : ∀ x ∈ boundaryUnmatchedVertices V matching,
      ∃ y ∈ Q ∪ boundaryConflictMatchedVertices matching, conflict x y := by
    intro x hx
    have hxV : x ∈ V := (Finset.mem_sdiff.mp hx).1
    have hxUnmatched : x ∉ boundaryConflictMatchedVertices matching :=
      (Finset.mem_sdiff.mp hx).2
    obtain ⟨y, hy, hxy⟩ :=
      unmatchedBoundaryConflictNeighbor_mem_core_or_matched C Q V conflict hCV
        matching hmax hclose (x := x) hxV hxUnmatched
    exact ⟨y, hy, hxy⟩
  let owner := boundaryGroupOwner Q V matching conflict hneighbor
  have howner : ∀ x (hx : x ∈ boundaryUnmatchedVertices V matching),
      owner ⟨x, hx⟩ ∈ boundaryGroupIndices Q matching := by
    intro x hx
    exact boundaryGroupOwner_mem_indices Q V matching conflict hneighbor ⟨x, hx⟩
  have hcover := boundaryGroupFamily_covers_of_partition C Q V matching hCV owner howner
  have hgroups := boundaryGroupFamily_card_le_half Q V matching hmatching owner
  exact ⟨matching, owner, hmatching, hneighbor, rfl, hcover, hgroups⟩

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
