/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Peierls.ContourField
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

/-! # Generic connected contour components

For a finite edge type and a finite family of plaquette boundaries, this module defines
plaquette adjacency, components of the nonzero edges of a field, and proves their saturation
on every plaquette. A closed field therefore splits into closed fields on a contour component
and its complement.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Clock.Peierls

/-- Edges are adjacent when they are distinct and belong to a common plaquette boundary. -/
def genericPlaquetteAdjacencyGraph {E P : Type*}
    (boundary : P → Finset E) : SimpleGraph E where
  Adj e f := e ≠ f ∧ ∃ p, e ∈ boundary p ∧ f ∈ boundary p
  symm := by
    constructor
    intro e f h
    exact ⟨h.1.symm, by
      rcases h.2 with ⟨p, hep, hfp⟩
      exact ⟨p, hfp, hep⟩⟩
  loopless := by
    constructor
    intro e h
    exact h.1 rfl

/-- The graph induced by the edges where the field is nonzero. -/
def genericBadEdgeGraph {E P G : Type*} [Zero G]
    (boundary : P → Finset E) (η : E → G) :
    SimpleGraph {e : E // η e ≠ 0} :=
  (genericPlaquetteAdjacencyGraph boundary).induce {e : E | η e ≠ 0}

/-- The plaquette-connected component of a chosen nonzero edge, represented as a finite set of
edges. Connectivity is taken in the graph induced by the nonzero edges. -/
noncomputable def genericContourComponent {E P G : Type*} [Fintype E] [Zero G]
    (boundary : P → Finset E) (η : E → G) (root : E) (hroot : η root ≠ 0) : Finset E := by
  classical
  exact Finset.univ.filter fun e =>
    ∃ he : η e ≠ 0,
      (genericBadEdgeGraph boundary η).Reachable ⟨root, hroot⟩ ⟨e, he⟩

/-- Membership in the chosen contour means being a nonzero edge reachable from the root through
nonzero edges and plaquette adjacencies. -/
theorem mem_genericContourComponent_iff {E P G : Type*} [Fintype E] [Zero G]
    (boundary : P → Finset E) (η : E → G) (root : E) (hroot : η root ≠ 0) (e : E) :
    e ∈ genericContourComponent boundary η root hroot ↔
      ∃ he : η e ≠ 0,
        (genericBadEdgeGraph boundary η).Reachable ⟨root, hroot⟩ ⟨e, he⟩ := by
  classical
  simp [genericContourComponent]

/-- The distinguished nonzero edge belongs to its own contour. -/
theorem root_mem_genericContourComponent {E P G : Type*} [Fintype E] [Zero G]
    (boundary : P → Finset E) (η : E → G) (root : E) (hroot : η root ≠ 0) :
    root ∈ genericContourComponent boundary η root hroot := by
  rw [mem_genericContourComponent_iff]
  exact ⟨hroot, SimpleGraph.Reachable.rfl⟩

/-- Every edge of a contour component is nonzero. -/
theorem genericContourComponent_nonzero {E P G : Type*} [Fintype E] [Zero G]
    (boundary : P → Finset E) (η : E → G) (root : E) (hroot : η root ≠ 0)
    {e : E} (he : e ∈ genericContourComponent boundary η root hroot) : η e ≠ 0 := by
  rw [mem_genericContourComponent_iff] at he
  exact he.choose

/-- Saturation: if a plaquette meets a contour, all of its nonzero edges belong to that contour. -/
theorem genericContourComponent_saturated {E P G : Type*} [Fintype E] [Zero G]
    (boundary : P → Finset E) (η : E → G) (root : E) (hroot : η root ≠ 0)
    {p : P} {e f : E}
    (he : e ∈ genericContourComponent boundary η root hroot)
    (hep : e ∈ boundary p) (hfp : f ∈ boundary p) (hf : η f ≠ 0) :
    f ∈ genericContourComponent boundary η root hroot := by
  rw [mem_genericContourComponent_iff] at he ⊢
  rcases he with ⟨heBad, hreach⟩
  refine ⟨hf, ?_⟩
  by_cases hef : e = f
  · subst f
    exact hreach
  · have hadj : (genericPlaquetteAdjacencyGraph boundary).Adj e f :=
      ⟨hef, p, hep, hfp⟩
    exact hreach.trans (SimpleGraph.induce_adj.mpr hadj).reachable

/-- A closed field splits into closed fields on the contour component and its complement. -/
theorem genericContourComponent_restrict_split {E P G : Type*} [Fintype E]
    [DecidableEq E] [AddCommGroup G] [DecidableEq G]
    (boundary : P → Finset E) (η : E → G) (root : E) (hroot : η root ≠ 0)
    (hclosed : edgeFieldClosedOn boundary η) :
    edgeFieldClosedOn boundary
        (restrictEdgeField (genericContourComponent boundary η root hroot) η) ∧
      edgeFieldClosedOn boundary
        (restrictEdgeFieldOutside (genericContourComponent boundary η root hroot) η) := by
  apply edgeFieldClosedOn_restrict_split boundary η
    (genericContourComponent boundary η root hroot) hclosed
  intro p hmeet e hep he
  rcases hmeet with ⟨f, hfp, hfComponent⟩
  exact genericContourComponent_saturated boundary η root hroot hfComponent hfp hep he

end FroehlichSpencer.BKT.Clock.Peierls

end
