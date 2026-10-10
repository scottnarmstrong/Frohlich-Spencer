/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Peierls.ComponentFlux
public import FroehlichSpencer.BKT.Clock.Peierls.ConfigurationField
public import FroehlichSpencer.BKT.Clock.Peierls.EdgeAdjacency
public import FroehlichSpencer.BKT.Clock.Peierls.FieldSplittingSquare
public import FroehlichSpencer.BKT.Clock.Peierls.GenericContours
public import FroehlichSpencer.Infra.Combinatorics.Animals
import Mathlib.Tactic

/-! # Geometry of bad-edge components in a finite clock box -/

@[expose] public section

namespace FroehlichSpencer.BKT.Clock.Peierls

open FroehlichSpencer.BKT.Lattice2D

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {A : Type*} [AddCommGroup A] [DecidableEq A]

omit [DecidableEq E] in
/-- The support of a connected component of the induced graph on the nonzero edges is connected
in the full edge graph. -/
theorem clockPeierlsComponentSupport_connected (G : SimpleGraph E)
    (η : E → A) (c : (clockPeierlsBadGraph G η).ConnectedComponent) :
    (G.induce (clockPeierlsComponentSupport G η c : Set E)).Connected := by
  classical
  let H := clockPeierlsBadGraph G η
  let f : c.toSimpleGraph →g G.induce (clockPeierlsComponentSupport G η c : Set E) :=
    { toFun := fun x => ⟨x.1.1, by
        apply (mem_clockPeierlsComponentSupport_iff G η c x.1.1).2
        exact ⟨x.1.2, (SimpleGraph.ConnectedComponent.mem_supp_iff c x.1).mp x.2⟩
      ⟩
      map_rel' := by
        intro x y hxy
        exact hxy }
  have hsurj : Function.Surjective f := by
    intro y
    rcases (mem_clockPeierlsComponentSupport_iff G η c y.1).mp y.2 with
      ⟨hy, hc⟩
    refine ⟨⟨⟨y.1, hy⟩, hc⟩, ?_⟩
    apply Subtype.ext
    rfl
  exact SimpleGraph.Connected.map f hsurj c.connected_toSimpleGraph

omit [DecidableEq E] in
/-- A component support containing its root edge is one of the full-graph lattice animals of
its cardinality. -/
theorem clockPeierlsComponentSupport_mem_animals (G : SimpleGraph E)
    [G.LocallyFinite] (η : E → A)
    (c : (clockPeierlsBadGraph G η).ConnectedComponent) {root : E}
    (hroot : root ∈ clockPeierlsComponentSupport G η c) :
    clockPeierlsComponentSupport G η c ∈
      FroehlichSpencer.Infra.animals G root
        (clockPeierlsComponentSupport G η c).card := by
  classical
  rw [FroehlichSpencer.Infra.mem_animals]
  exact ⟨hroot, rfl, clockPeierlsComponentSupport_connected G η c⟩

private theorem genericPlaquetteEdges_mem_clockPlaquetteEdges {L : ℕ}
    [DecidableEq (Lattice2D.SquareFreeEdge L)]
    (i j : ℕ) (hi : i + 1 < L) (hj : j + 1 < L)
    {e : Lattice2D.SquareFreeEdge L}
    (he : e ∈ GenericGradient.squareFreePlaquetteEdges (L := L) i j hi hj) :
    e ∈ clockPeierlsPlaquetteEdges (L := L) ⟨i, by omega⟩ ⟨j, by omega⟩
      (by omega) (by omega) := by
  simp [GenericGradient.squareFreePlaquetteEdges, clockPeierlsPlaquetteEdges,
    GenericGradient.squareFreeHorizontalEdgeAt, clockPeierlsHorizontalEdgeAt,
    GenericGradient.squareFreeVerticalEdgeAt, clockPeierlsVerticalEdgeAt] at he ⊢
  aesop

/-- A connected component of nonzero edges is saturated on every plaquette. -/
theorem clockPeierlsComponentSupport_squareSaturated {L n : ℕ} [NeZero n]
    [DecidableEq (Lattice2D.SquareFreeEdge L)]
    (σ : Lattice2D.SquareFreeVertex L → Fin n)
    (c : (clockPeierlsBadGraph (clockPeierlsAdjacencyGraph L)
      (clockConfigurationField σ)).ConnectedComponent) :
    GenericGradient.squareFreePlaquetteSaturated (clockConfigurationField σ)
      (clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph L)
        (clockConfigurationField σ) c) := by
  intro i j hi hj hmeet f hf
  rcases hmeet with ⟨e, hep, heS⟩
  by_cases hzero : clockConfigurationField σ f = 0
  · exact Or.inl hzero
  · have ⟨heBad, heComp⟩ :=
      (mem_clockPeierlsComponentSupport_iff (clockPeierlsAdjacencyGraph L)
        (clockConfigurationField σ) c e).mp heS
    have he' := genericPlaquetteEdges_mem_clockPlaquetteEdges i j hi hj hep
    have hf' := genericPlaquetteEdges_mem_clockPlaquetteEdges i j hi hj hf
    have hshare : clockPeierlsSharesPlaquette e f :=
      ⟨⟨i, by omega⟩, ⟨j, by omega⟩, by omega, by omega, he', hf'⟩
    by_cases hef : e = f
    · subst f
      exact Or.inr heS
    · have hadj : (clockPeierlsAdjacencyGraph L).Adj e f := ⟨hef, hshare⟩
      have hbadAdj :
          (clockPeierlsBadGraph (clockPeierlsAdjacencyGraph L)
            (clockConfigurationField σ)).Adj ⟨e, heBad⟩ ⟨f, hzero⟩ :=
        SimpleGraph.induce_adj.mpr hadj
      have hfComp :=
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hbadAdj).symm.trans heComp
      exact Or.inr ((mem_clockPeierlsComponentSupport_iff
        (clockPeierlsAdjacencyGraph L) (clockConfigurationField σ) c f).2
          ⟨hzero, hfComp⟩)

end FroehlichSpencer.BKT.Clock.Peierls

end
