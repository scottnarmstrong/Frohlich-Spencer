/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Lattice2D.SquareFree
public import FroehlichSpencer.Infra.Combinatorics.Animals
public import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

/-! # Plaquette adjacency for edges of the free square -/

@[expose] public section

namespace FroehlichSpencer.BKT.Clock.Peierls

open FroehlichSpencer.BKT.Lattice2D

/-- The positive horizontal edge at the natural coordinate `(i,j)`. -/
def clockPeierlsHorizontalEdgeAt {L : ℕ} (i j : ℕ)
    (hi : i + 1 < L) (hj : j < L) : SquareFreeEdge L :=
  Sum.inl ⟨⟨⟨i, by omega⟩, hi⟩, ⟨j, hj⟩⟩

/-- The positive vertical edge at the natural coordinate `(i,j)`. -/
def clockPeierlsVerticalEdgeAt {L : ℕ} (i j : ℕ)
    (hi : i < L) (hj : j + 1 < L) : SquareFreeEdge L :=
  Sum.inr ⟨⟨i, hi⟩, ⟨⟨j, by omega⟩, hj⟩⟩

/-- The four oriented edges bounding the unit square with lower-left corner `(i,j)`. -/
def clockPeierlsPlaquetteEdges {L : ℕ} (i j : Fin L)
    (hi : i.val + 1 < L) (hj : j.val + 1 < L) : Finset (SquareFreeEdge L) :=
  { clockPeierlsHorizontalEdgeAt i.val j.val hi j.isLt,
    clockPeierlsVerticalEdgeAt (i.val + 1) j.val (by omega) hj,
    clockPeierlsHorizontalEdgeAt i.val (j.val + 1) hi (by omega),
    clockPeierlsVerticalEdgeAt i.val j.val i.isLt hj }

/-- Two free-square edges share a unit plaquette. -/
def clockPeierlsSharesPlaquette {L : ℕ} (e f : SquareFreeEdge L) : Prop :=
  ∃ (i j : Fin L) (hi : i.val + 1 < L) (hj : j.val + 1 < L),
    e ∈ clockPeierlsPlaquetteEdges i j hi hj ∧
      f ∈ clockPeierlsPlaquetteEdges i j hi hj

/-- Six explicitly listed edge positions that include every edge sharing a plaquette
with the given edge. Invalid positions are filled by the edge itself. -/
def clockPeierlsCandidate {L : ℕ} (e : SquareFreeEdge L) (k : Fin 6) :
    SquareFreeEdge L := by
  rcases e with h | v
  · let i := h.1.1.val
    let j := h.2.val
    let hi := h.1.2
    let edge : SquareFreeEdge L := Sum.inl h
    exact if hk : k.val = 0 then
        if hj : j + 1 < L then clockPeierlsHorizontalEdgeAt i (j + 1) hi (by omega)
        else edge
      else if hk : k.val = 1 then
        if hj : 0 < j then clockPeierlsHorizontalEdgeAt i (j - 1) hi (by omega)
        else edge
      else if hk : k.val = 2 then
        if hj : j + 1 < L then clockPeierlsVerticalEdgeAt i j (by omega) hj
        else edge
      else if hk : k.val = 3 then
        if hxy : i + 1 < L ∧ j + 1 < L then
          clockPeierlsVerticalEdgeAt (i + 1) j (by omega) hxy.2
        else edge
      else if hk : k.val = 4 then
        if hj : 0 < j then clockPeierlsVerticalEdgeAt i (j - 1) (by omega) (by omega)
        else edge
      else if hk : k.val = 5 then
        if hxy : i + 1 < L ∧ 0 < j then
          clockPeierlsVerticalEdgeAt (i + 1) (j - 1) (by omega) (by omega)
        else edge
      else edge
  · let i := v.1.val
    let j := v.2.1.val
    let hj := v.2.2
    let edge : SquareFreeEdge L := Sum.inr v
    exact if hk : k.val = 0 then
        if hi : i + 1 < L then clockPeierlsHorizontalEdgeAt i j hi (by omega)
        else edge
      else if hk : k.val = 1 then
        if hxy : i + 1 < L ∧ j + 1 < L then
          clockPeierlsHorizontalEdgeAt i (j + 1) hxy.1 (by omega)
        else edge
      else if hk : k.val = 2 then
        if hi : i + 1 < L then clockPeierlsVerticalEdgeAt (i + 1) j (by omega) hj
        else edge
      else if hk : k.val = 3 then
        if hi : 0 < i then clockPeierlsHorizontalEdgeAt (i - 1) j (by omega) (by omega)
        else edge
      else if hk : k.val = 4 then
        if hxy : 0 < i ∧ j + 1 < L then
          clockPeierlsHorizontalEdgeAt (i - 1) (j + 1) (by omega) (by omega)
        else edge
      else if hk : k.val = 5 then
        if hi : 0 < i then clockPeierlsVerticalEdgeAt (i - 1) j (by omega) hj
        else edge
      else edge

/-- The finite set of candidate neighbors of an edge. -/
def clockPeierlsCandidateSet {L : ℕ} (e : SquareFreeEdge L) : Finset (SquareFreeEdge L) :=
  Finset.univ.image (clockPeierlsCandidate e)

/-- The lower-left coordinate of an edge, using its positive orientation. -/
def clockPeierlsEdgeAnchor {L : ℕ} (e : SquareFreeEdge L) : ℕ × ℕ :=
  match e with
  | .inl h => (h.1.1.val, h.2.val)
  | .inr v => (v.1.val, v.2.1.val)

/-- Each of the six candidate positions changes either statement coordinate by at most one. -/
private theorem clockPeierlsCandidate_anchor_bounds {L : ℕ} (e : SquareFreeEdge L)
    (k : Fin 6) :
    (clockPeierlsEdgeAnchor e).1 ≤
        (clockPeierlsEdgeAnchor (clockPeierlsCandidate e k)).1 + 1 ∧
      (clockPeierlsEdgeAnchor (clockPeierlsCandidate e k)).1 ≤
        (clockPeierlsEdgeAnchor e).1 + 1 ∧
      (clockPeierlsEdgeAnchor e).2 ≤
        (clockPeierlsEdgeAnchor (clockPeierlsCandidate e k)).2 + 1 ∧
      (clockPeierlsEdgeAnchor (clockPeierlsCandidate e k)).2 ≤
        (clockPeierlsEdgeAnchor e).2 + 1 := by
  cases e with
  | inl e =>
    rcases e with ⟨⟨i, hi⟩, j⟩
    fin_cases k
    all_goals
      simp [clockPeierlsCandidate, clockPeierlsHorizontalEdgeAt,
        clockPeierlsVerticalEdgeAt, clockPeierlsEdgeAnchor]
      split_ifs
      all_goals
        simp
        all_goals omega
  | inr e =>
    rcases e with ⟨i, ⟨j, hj⟩⟩
    fin_cases k
    all_goals
      simp [clockPeierlsCandidate, clockPeierlsHorizontalEdgeAt,
        clockPeierlsVerticalEdgeAt, clockPeierlsEdgeAnchor]
      split_ifs
      all_goals
        simp
        all_goals omega

theorem clockPeierlsCandidateSet_card_le {L : ℕ} (e : SquareFreeEdge L) :
    (clockPeierlsCandidateSet e).card ≤ 6 := by
  unfold clockPeierlsCandidateSet
  calc
    _ ≤ (Finset.univ : Finset (Fin 6)).card := Finset.card_image_le
    _ = 6 := Fintype.card_fin 6

/-- The plaquette-adjacency graph: distinct edges are adjacent exactly when they occur on
the boundary of a common unit square. -/
def clockPeierlsAdjacencyGraph (L : ℕ) : SimpleGraph (SquareFreeEdge L) where
  Adj e f := e ≠ f ∧ clockPeierlsSharesPlaquette e f
  symm := by
    constructor
    intro e f h
    exact ⟨h.1.symm, by
      rcases h.2 with ⟨i, j, hi, hj, he, hf⟩
      exact ⟨i, j, hi, hj, hf, he⟩⟩
  loopless := ⟨fun e h => h.1 rfl⟩

theorem clockPeierlsAdjacencyGraph_adj_iff {L : ℕ} (e f : SquareFreeEdge L) :
    (clockPeierlsAdjacencyGraph L).Adj e f ↔
      e ≠ f ∧ clockPeierlsSharesPlaquette e f := Iff.rfl

/-- An edge on a plaquette is among the six local candidate positions relative to any
other distinct edge on that plaquette. -/
private theorem clockPeierlsCandidateSet_mem_of_sharesPlaquette
    {L : ℕ} {e f : SquareFreeEdge L} (hne : e ≠ f)
    (hshare : clockPeierlsSharesPlaquette e f) : f ∈ clockPeierlsCandidateSet e := by
  classical
  rcases hshare with ⟨i, j, hi, hj, he, hf⟩
  have useCandidate (k : Fin 6) (hEq : clockPeierlsCandidate e k = f) :
      f ∈ clockPeierlsCandidateSet e := by
    rw [clockPeierlsCandidateSet, Finset.mem_image]
    exact ⟨k, Finset.mem_univ _, hEq⟩
  cases e with
  | inl e =>
    simp [clockPeierlsPlaquetteEdges, clockPeierlsHorizontalEdgeAt,
      clockPeierlsVerticalEdgeAt] at he hf
    rcases he with he | he
    · subst e
      rcases hf with hf | hf | hf | hf
      · subst f
        exact False.elim (hne rfl)
      · subst f
        apply useCandidate ⟨3, by omega⟩
        simp [clockPeierlsCandidate, clockPeierlsVerticalEdgeAt, hi, hj]
      · subst f
        apply useCandidate ⟨0, by omega⟩
        simp [clockPeierlsCandidate, clockPeierlsHorizontalEdgeAt, hj]
      · subst f
        apply useCandidate ⟨2, by omega⟩
        simp [clockPeierlsCandidate, clockPeierlsVerticalEdgeAt, hj]
    · subst e
      rcases hf with hf | hf | hf | hf
      · subst f
        apply useCandidate ⟨1, by omega⟩
        simp [clockPeierlsCandidate, clockPeierlsHorizontalEdgeAt]
      · subst f
        apply useCandidate ⟨5, by omega⟩
        simp [clockPeierlsCandidate, clockPeierlsVerticalEdgeAt, hi]
      · subst f
        exact False.elim (hne rfl)
      · subst f
        apply useCandidate ⟨4, by omega⟩
        simp [clockPeierlsCandidate, clockPeierlsVerticalEdgeAt]
  | inr e =>
    simp [clockPeierlsPlaquetteEdges, clockPeierlsHorizontalEdgeAt,
      clockPeierlsVerticalEdgeAt] at he hf
    rcases he with he | he
    · subst e
      rcases hf with hf | hf | hf | hf
      · subst f
        apply useCandidate ⟨3, by omega⟩
        simp [clockPeierlsCandidate, clockPeierlsHorizontalEdgeAt]
      · subst f
        exact False.elim (hne rfl)
      · subst f
        apply useCandidate ⟨4, by omega⟩
        simp [clockPeierlsCandidate, clockPeierlsHorizontalEdgeAt, hj]
      · subst f
        apply useCandidate ⟨5, by omega⟩
        simp [clockPeierlsCandidate, clockPeierlsVerticalEdgeAt]
    · subst e
      rcases hf with hf | hf | hf | hf
      · subst f
        apply useCandidate ⟨0, by omega⟩
        simp [clockPeierlsCandidate, clockPeierlsHorizontalEdgeAt, hi]
      · subst f
        apply useCandidate ⟨2, by omega⟩
        simp [clockPeierlsCandidate, clockPeierlsVerticalEdgeAt, hi]
      · subst f
        apply useCandidate ⟨1, by omega⟩
        simp [clockPeierlsCandidate, clockPeierlsHorizontalEdgeAt, hi, hj]
      · subst f
        exact False.elim (hne rfl)

noncomputable instance clockPeierlsAdjacencyGraph_locallyFinite (L : ℕ) :
    (clockPeierlsAdjacencyGraph L).LocallyFinite := by
  classical
  intro e
  exact Fintype.ofFinite _

theorem clockPeierlsAdjacencyGraph_degree_le (L : ℕ) (e : SquareFreeEdge L) :
    (clockPeierlsAdjacencyGraph L).degree e ≤ 6 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  calc
    _ ≤ (clockPeierlsCandidateSet e).card := by
      apply Finset.card_le_card
      intro f hf
      have hadj : (clockPeierlsAdjacencyGraph L).Adj e f :=
        (SimpleGraph.mem_neighborFinset (clockPeierlsAdjacencyGraph L) e f).1 hf
      exact clockPeierlsCandidateSet_mem_of_sharesPlaquette hadj.1 hadj.2
    _ ≤ 6 := clockPeierlsCandidateSet_card_le e

/-- Adjacent edges have statement coordinates differing by at most one. -/
theorem clockPeierlsAdjacencyGraph_anchor_step {L : ℕ} {e f : SquareFreeEdge L}
    (h : (clockPeierlsAdjacencyGraph L).Adj e f) :
    (clockPeierlsEdgeAnchor e).1 ≤ (clockPeierlsEdgeAnchor f).1 + 1 ∧
      (clockPeierlsEdgeAnchor f).1 ≤ (clockPeierlsEdgeAnchor e).1 + 1 ∧
      (clockPeierlsEdgeAnchor e).2 ≤ (clockPeierlsEdgeAnchor f).2 + 1 ∧
      (clockPeierlsEdgeAnchor f).2 ≤ (clockPeierlsEdgeAnchor e).2 + 1 := by
  have hcand := clockPeierlsCandidateSet_mem_of_sharesPlaquette h.1 h.2
  rcases Finset.mem_image.mp hcand with ⟨k, -, hEq⟩
  subst f
  exact clockPeierlsCandidate_anchor_bounds e k

/-- A graph walk of length `d` changes each oriented edge-statement coordinate by at most `d`. -/
theorem clockPeierlsAdjacencyGraph_walk_anchor_bounds {L : ℕ} {e f : SquareFreeEdge L}
    (p : (clockPeierlsAdjacencyGraph L).Walk e f) :
    (clockPeierlsEdgeAnchor e).1 ≤ (clockPeierlsEdgeAnchor f).1 + p.length ∧
      (clockPeierlsEdgeAnchor f).1 ≤ (clockPeierlsEdgeAnchor e).1 + p.length ∧
      (clockPeierlsEdgeAnchor e).2 ≤ (clockPeierlsEdgeAnchor f).2 + p.length ∧
      (clockPeierlsEdgeAnchor f).2 ≤ (clockPeierlsEdgeAnchor e).2 + p.length := by
  induction p with
  | nil => simp
  | @cons a b c hab q ih =>
      have hstep := clockPeierlsAdjacencyGraph_anchor_step hab
      rcases hstep with ⟨hxab, hxba, hyab, hyba⟩
      rcases ih with ⟨hxbc, hxcb, hybc, hycb⟩
      simp only [SimpleGraph.Walk.length_cons]
      refine ⟨?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · omega

/-- The ℓ∞ distance between edge statement is bounded by the length of every connecting walk. -/
def clockPeierlsAnchorLInfDistance {L : ℕ} (e f : SquareFreeEdge L) : ℕ :=
  max (max ((clockPeierlsEdgeAnchor e).1 - (clockPeierlsEdgeAnchor f).1)
        ((clockPeierlsEdgeAnchor f).1 - (clockPeierlsEdgeAnchor e).1))
      (max ((clockPeierlsEdgeAnchor e).2 - (clockPeierlsEdgeAnchor f).2)
        ((clockPeierlsEdgeAnchor f).2 - (clockPeierlsEdgeAnchor e).2))

theorem clockPeierlsAdjacencyGraph_walk_anchor_linf_le {L : ℕ} {e f : SquareFreeEdge L}
    (p : (clockPeierlsAdjacencyGraph L).Walk e f) :
    clockPeierlsAnchorLInfDistance e f ≤ p.length := by
  rcases clockPeierlsAdjacencyGraph_walk_anchor_bounds p with
    ⟨hx1, hx2, hy1, hy2⟩
  unfold clockPeierlsAnchorLInfDistance
  refine max_le ?_ ?_
  · exact max_le (by omega) (by omega)
  · exact max_le (by omega) (by omega)

/-- The connected edge animals for plaquette adjacency obey the generic degree-six bound. -/
theorem clockPeierlsAdjacencyGraph_card_animals_le (L : ℕ)
    (e : SquareFreeEdge L) (n : ℕ) :
    (FroehlichSpencer.Infra.animals (clockPeierlsAdjacencyGraph L) e n).card ≤
      6 ^ (2 * (n - 1)) := by
  exact FroehlichSpencer.Infra.card_animals_le (clockPeierlsAdjacencyGraph L)
    (clockPeierlsAdjacencyGraph_degree_le L) e n

end FroehlichSpencer.BKT.Clock.Peierls

end
