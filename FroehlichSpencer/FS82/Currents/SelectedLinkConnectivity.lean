/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Relation

/-!
# Connectivity after deleting plaquette-independent links

This is the path-replacement core of the square-detour argument. Once each
deleted edge is replaced by a path around one plaquette, every path in the
full link graph lifts to a path avoiding the deleted set.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.Currents.SelectedLinkConnectivity

/-- Undirected adjacency witnessed by one oriented edge. -/
def linkAdjacency {V E : Type*} (source target : E → V) (a b : V) : Prop :=
  ∃ e, (source e = a ∧ target e = b) ∨ (source e = b ∧ target e = a)

/-- Adjacency witnessed by an edge outside the selected set. -/
def linkAdjacencyAvoiding {V E : Type*} [DecidableEq E]
    (source target : E → V) (selected : Finset E) (a b : V) : Prop :=
  ∃ e, e ∉ selected ∧
    ((source e = a ∧ target e = b) ∨ (source e = b ∧ target e = a))

private theorem linkAdjacencyAvoiding_symmetric {V E : Type*} [DecidableEq E]
    (source target : E → V) (selected : Finset E) {a b : V}
    (h : linkAdjacencyAvoiding source target selected a b) :
    linkAdjacencyAvoiding source target selected b a := by
  rcases h with ⟨e, he, hab | hba⟩
  · exact ⟨e, he, Or.inr ⟨hab.1, hab.2⟩⟩
  · exact ⟨e, he, Or.inl ⟨hba.1, hba.2⟩⟩

private theorem transGen_symmetric {V : Type*} {R : V → V → Prop}
    (hR : ∀ ⦃a b⦄, R a b → R b a) {a b : V}
    (h : Relation.TransGen R a b) : Relation.TransGen R b a := by
  induction h using Relation.TransGen.trans_induction_on with
  | single hab => exact Relation.TransGen.single (hR hab)
  | trans hab hbc ihab ihbc => exact Relation.TransGen.trans ihbc ihab

/-- Full-graph connectivity survives edge deletion whenever each selected edge
has a detour path through unselected edges. For square-lattice applications,
the detour is the other three links of an incident plaquette. -/
theorem connected_after_deleting_of_edge_detours {V E : Type*} [DecidableEq E]
    (source target : E → V) (selected : Finset E)
    {a b : V}
    (hconn : Relation.TransGen (linkAdjacency source target) a b)
    (hdetour : ∀ e ∈ selected,
      Relation.TransGen (linkAdjacencyAvoiding source target selected)
        (source e) (target e)) :
    Relation.TransGen (linkAdjacencyAvoiding source target selected) a b := by
  let R := linkAdjacency source target
  let G := linkAdjacencyAvoiding source target selected
  have hGsymm : ∀ ⦃u v⦄, G u v → G v u := by
    intro u v huv
    exact linkAdjacencyAvoiding_symmetric source target selected huv
  have hstep : ∀ ⦃u v⦄, R u v → Relation.TransGen G u v := by
    intro u v huv
    rcases huv with ⟨e, he | he⟩
    · by_cases hsel : e ∈ selected
      · rw [← he.1, ← he.2]
        have hpath := hdetour e hsel
        change Relation.TransGen G (source e) (target e) at hpath
        exact hpath
      · exact Relation.TransGen.single ⟨e, hsel, Or.inl he⟩
    · by_cases hsel : e ∈ selected
      · rw [← he.1, ← he.2]
        have hpath := hdetour e hsel
        change Relation.TransGen G (source e) (target e) at hpath
        exact transGen_symmetric hGsymm hpath
      · exact Relation.TransGen.single ⟨e, hsel, Or.inr he⟩
  change Relation.TransGen R a b at hconn
  induction hconn using Relation.TransGen.trans_induction_on with
  | single hab => exact hstep hab
  | trans huv hvw ihuv ihvw => exact Relation.TransGen.trans ihuv ihvw


end FroehlichSpencer.FS82.Currents.SelectedLinkConnectivity

end
