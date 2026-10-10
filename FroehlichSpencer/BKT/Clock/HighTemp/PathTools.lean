/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.HighTemp.FiniteBox
public import FroehlichSpencer.BKT.Lattice2D.SquareFree
import Mathlib.Combinatorics.SimpleGraph.Trails

/-!
# Selected-path bond bookkeeping

Simple paths in a selected-bond graph determine a distinct set of square
bonds, with one bond for every path step.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.HighTemp

open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Lattice2D

@[instance_reducible] noncomputable instance selectedBondGraphLocallyFinite (L : ℕ)
    (A : Finset (RotatorInternalBond L)) :
    SimpleGraph.LocallyFinite (selectedBondGraph L A) := by
  classical
  exact fun _ => Fintype.ofFinite _

noncomputable instance selectedBondGraphDecidableAdj (L : ℕ)
    (A : Finset (RotatorInternalBond L)) :
    DecidableRel (selectedBondGraph L A).Adj := Classical.decRel _

/-- Bonds whose endpoint pairs occur among the edges of a walk. -/
def selectedPathBondFinset {L : ℕ} {G : SimpleGraph (RotatorSpinSite L)}
    (s : Finset (RotatorInternalBond L)) {u v : RotatorSpinSite L} (p : G.Walk u v) :
    Finset (RotatorInternalBond L) :=
  s.filter fun e => rotatorBondSym2Embedding e ∈ p.edges.toFinset

theorem selectedPathBondFinset_card {L : ℕ} {G : SimpleGraph (RotatorSpinSite L)}
    {s : Finset (RotatorInternalBond L)} {u v : RotatorSpinSite L} (p : G.Walk u v)
    (hp : p.IsPath)
    (hcover : ∀ e ∈ p.edges, ∃ b, b ∈ s ∧ rotatorBondSym2Embedding b = e) :
    (selectedPathBondFinset s p).card = p.length := by
  classical
  have hmap : (selectedPathBondFinset s p).map rotatorBondSym2Embedding = p.edges.toFinset := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_map.mp he with ⟨b, hb, hbe⟩
      have hb' := (Finset.mem_filter.mp hb).2
      simpa [hbe] using hb'
    · intro he
      have he' : e ∈ p.edges := List.mem_toFinset.mp he
      rcases hcover e he' with ⟨b, hbs, hbe⟩
      apply Finset.mem_map.mpr
      refine ⟨b, Finset.mem_filter.mpr ⟨hbs, ?_⟩, hbe⟩
      simpa [hbe] using he
  calc
    (selectedPathBondFinset s p).card =
        ((selectedPathBondFinset s p).map rotatorBondSym2Embedding).card := by simp
    _ = p.edges.toFinset.card := congrArg Finset.card hmap
    _ = p.length := by
      rw [List.toFinset_card_of_nodup hp.isTrail.edges_nodup, SimpleGraph.Walk.length_edges]

theorem selectedBondGraph_le_univ {L : ℕ} (s : Finset (RotatorInternalBond L)) :
    selectedBondGraph L s ≤ selectedBondGraph L (Finset.univ : Finset (RotatorInternalBond L)) := by
  change SimpleGraph.fromEdgeSet
      (rotatorBondSym2 (L := L) '' (s : Set (RotatorInternalBond L))) ≤
    SimpleGraph.fromEdgeSet
      (rotatorBondSym2 (L := L) '' ((Finset.univ : Finset (RotatorInternalBond L)) : Set _))
  rw [SimpleGraph.le_fromEdgeSet_iff, SimpleGraph.edgeSet_fromEdgeSet]
  intro x hx
  simp only [Set.mem_sdiff] at hx
  rcases hx.1 with ⟨e, he, rfl⟩
  exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr (Finset.mem_univ e))

private theorem rotatorBondPair_mem_iff (L : ℕ) (x y : RotatorSpinSite L) :
    s(x, y) ∈ rotatorBondSym2 (L := L) ''
        (Finset.univ : Finset (RotatorInternalBond L)) ↔
      ∃ e, ((rotatorFreeGraph L).src e = x ∧ (rotatorFreeGraph L).tgt e = y) ∨
        ((rotatorFreeGraph L).src e = y ∧ (rotatorFreeGraph L).tgt e = x) := by
  constructor
  · intro h
    rcases (Set.mem_image _ _ _).mp h with ⟨e, he, hpair⟩
    rcases Sym2.eq_iff.mp hpair with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact ⟨e, Or.inl ⟨hs, ht⟩⟩
    · exact ⟨e, Or.inr ⟨hs, ht⟩⟩
  · rintro ⟨e, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩
    · apply (Set.mem_image _ _ _).2
      exact ⟨e, Finset.mem_coe.mpr (Finset.mem_univ e),
        Sym2.eq_iff.mpr (Or.inl ⟨hs, ht⟩)⟩
    · apply (Set.mem_image _ _ _).2
      exact ⟨e, Finset.mem_coe.mpr (Finset.mem_univ e),
        Sym2.eq_iff.mpr (Or.inr ⟨hs, ht⟩)⟩

/-- The graph containing every encoded bond is the simple graph underlying the
free square multigraph. -/
theorem selectedBondGraph_univ_eq_toSimpleGraph (L : ℕ) :
    selectedBondGraph L (Finset.univ : Finset (RotatorInternalBond L)) =
      (rotatorFreeGraph L).toSimpleGraph := by
  ext x y
  rw [selectedBondGraph, SimpleGraph.fromEdgeSet_adj, Multigraph.toSimpleGraph,
    SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hpair, hxy⟩
    exact ⟨hxy, Or.inl (rotatorBondPair_mem_iff L x y |>.mp hpair)⟩
  · rintro ⟨hxy, hrel⟩
    refine ⟨?_, hxy⟩
    rcases hrel with h | h
    · rcases h with ⟨e, h | h⟩
      · exact rotatorBondPair_mem_iff L x y |>.mpr ⟨e, Or.inl h⟩
      · exact rotatorBondPair_mem_iff L x y |>.mpr ⟨e, Or.inr h⟩
    · rcases h with ⟨e, h | h⟩
      · exact rotatorBondPair_mem_iff L x y |>.mpr ⟨e, Or.inr h⟩
      · exact rotatorBondPair_mem_iff L x y |>.mpr ⟨e, Or.inl h⟩

/-- Degree bound for the full selected-bond graph on the free square. -/
theorem fullSelectedBondGraph_degree_le_four (L : ℕ) (x : RotatorSpinSite L) :
    (selectedBondGraph L (Finset.univ : Finset (RotatorInternalBond L))).degree x ≤ 4 := by
  classical
  let G := selectedBondGraph L (Finset.univ : Finset (RotatorInternalBond L))
  let B := SimpleGraph.pathGraph (L + 1) □ SimpleGraph.pathGraph (L + 1)
  have hgraph : G = B := by
    dsimp [G, B]
    rw [selectedBondGraph_univ_eq_toSimpleGraph, rotatorFreeGraph,
      squareFreeGraph_toSimpleGraph]
  have hadj (y : RotatorSpinSite L) : G.Adj x y ↔ B.Adj x y := by rw [hgraph]
  let e : G.neighborSet x ≃ B.neighborSet x :=
    { toFun := fun y => ⟨y.1, (hadj y.1).mp y.2⟩
      invFun := fun y => ⟨y.1, (hadj y.1).mpr y.2⟩
      left_inv := by intro y; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  calc
    G.degree x = Fintype.card (G.neighborSet x) :=
      (SimpleGraph.card_neighborSet_eq_degree G x).symm
    _ = Fintype.card (B.neighborSet x) := Fintype.card_congr e
    _ = B.degree x := SimpleGraph.card_neighborSet_eq_degree B x
    _ ≤ 4 := squareBox_degree_le_four (L + 1) x

theorem selectedWalk_edgeLabel_cover {L : ℕ} {s : Finset (RotatorInternalBond L)}
    {u v : RotatorSpinSite L} (p : (selectedBondGraph L s).Walk u v) :
    ∀ e ∈ p.edges, ∃ b, b ∈ s ∧ rotatorBondSym2Embedding b = e := by
  intro e he
  have he' : e ∈ (selectedBondGraph L s).edgeSet := p.edges_subset_edgeSet he
  rw [selectedBondGraph, SimpleGraph.edgeSet_fromEdgeSet] at he'
  simp only [Set.mem_sdiff] at he'
  rcases he'.1 with ⟨b, hb, hbe⟩
  exact ⟨b, Finset.mem_coe.mp hb, hbe⟩

theorem allSelectedWalk_labels_subset {L : ℕ} {s : Finset (RotatorInternalBond L)}
    {u v : RotatorSpinSite L} (p : (selectedBondGraph L s).Walk u v) :
    selectedPathBondFinset (Finset.univ : Finset (RotatorInternalBond L)) p ⊆ s := by
  classical
  intro e he
  have hePath : rotatorBondSym2Embedding e ∈ p.edges :=
    List.mem_toFinset.mp (Finset.mem_filter.mp he).2
  rcases selectedWalk_edgeLabel_cover p (rotatorBondSym2Embedding e) hePath with
    ⟨b, hb, hbe⟩
  have hEq : b = e := rotatorBondSym2Embedding.injective hbe
  subst e
  exact hb

/-- A connected selected-bond set contains the distinct bond labels of a simple
path in the full square graph. -/
theorem reachable_path_full_with_bondFinset {L : ℕ} {s : Finset (RotatorInternalBond L)}
    {u v : RotatorSpinSite L} (hReach : (selectedBondGraph L s).Reachable u v) :
    ∃ q : (selectedBondGraph L (Finset.univ : Finset (RotatorInternalBond L))).Walk u v,
      q.IsPath ∧
        selectedPathBondFinset (Finset.univ : Finset (RotatorInternalBond L)) q ⊆ s ∧
        (selectedPathBondFinset (Finset.univ : Finset (RotatorInternalBond L)) q).card = q.length := by
  classical
  obtain ⟨p, hp⟩ := hReach.exists_isPath
  have hle := selectedBondGraph_le_univ s
  let q := p.mapLe hle
  have hq : q.IsPath := (SimpleGraph.Walk.isPath_mapLe hle).2 hp
  have hEdges : q.edges = p.edges := p.edges_mapLe_eq_edges hle
  have hLabels : selectedPathBondFinset (Finset.univ : Finset (RotatorInternalBond L)) q =
      selectedPathBondFinset (Finset.univ : Finset (RotatorInternalBond L)) p := by
    simp [selectedPathBondFinset, q, hEdges]
  refine ⟨q, hq, ?_, ?_⟩
  · rw [hLabels]
    exact allSelectedWalk_labels_subset p
  · rw [hLabels, SimpleGraph.Walk.length_mapLe]
    apply selectedPathBondFinset_card p hp
    intro e he
    rcases selectedWalk_edgeLabel_cover p e he with ⟨b, hb, hbe⟩
    exact ⟨b, Finset.mem_univ b, hbe⟩

end FroehlichSpencer.BKT.Clock.HighTemp

end
