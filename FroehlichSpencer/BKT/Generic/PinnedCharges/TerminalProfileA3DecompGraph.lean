/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileA3Terminal
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-! # Graphs for actual zero-cost components of the collapsed family -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-- The graph on a finite charge family, with an edge when the expanded neighborhoods overlap. -/
def profileA3OverlapGraph (F : Finset (ChargeDensity L)) :
    SimpleGraph {σ : ChargeDensity L // σ ∈ F} where
  Adj σ τ := σ.val ≠ τ.val ∧
    (profileA3NeutralNeighborhood σ.val ∩ profileA3NeutralNeighborhood τ.val).Nonempty
  symm := ⟨by
    intro σ τ h
    exact ⟨h.1.symm, by simpa [Finset.inter_comm] using h.2⟩⟩
  loopless := ⟨by
    intro σ h
    exact h.1 rfl⟩

/-- The overlap graph with all vertices of scale at least `D/10` removed from its edges. -/
def profileA3LowOverlapGraph (F : Finset (ChargeDensity L)) (D : ℝ) :
    SimpleGraph {σ : ChargeDensity L // σ ∈ F} where
  Adj σ τ :=
    (profileA3OverlapGraph F).Adj σ τ ∧
      boundaryAdjustedSize σ.val < D / 10 ∧ boundaryAdjustedSize τ.val < D / 10
  symm := ⟨by
    intro σ τ h
    rcases h with ⟨hadj, hσ, hτ⟩
    exact ⟨hadj.symm, hτ, hσ⟩⟩
  loopless := ⟨by
    intro σ h
    exact (profileA3OverlapGraph F).loopless.irrefl σ h.1⟩

/-- The free-step graph of the actual collapsed metric. -/
def profileA3ZeroCostGraph (𝓔 : Finset (Finset (Site L))) : SimpleGraph (Site L) where
  Adj x y := l1 x y = 1 ∧ IsCollapsedStep 𝓔 x y
  symm := ⟨by
    intro x y h
    rcases h with ⟨hxy, hc⟩
    refine ⟨by rw [l1_comm]; exact hxy, ?_⟩
    rcases hc with ⟨E, hE, hx, hy⟩
    exact ⟨E, hE, hy, hx⟩⟩
  loopless := ⟨by
    intro x h
    have hxy : l1 x x = 1 := h.1
    rw [l1_self] at hxy
    norm_num at hxy⟩

/-- The finite site set underlying a zero-cost connected component. -/
def profileA3ZeroComponent (𝓔 : Finset (Finset (Site L))) (x : Site L) : Finset (Site L) := by
  classical
  exact ((profileA3ZeroCostGraph 𝓔).connectedComponentMk x).supp.toFinset

/-- The set of all sites in the expanded neighborhoods labelled by a finite family. -/
def profileA3FamilyUnion (F : Finset (ChargeDensity L)) : Finset (Site L) := by
  classical
  exact F.biUnion profileA3NeutralNeighborhood

/-- The finite type of members of a charge family. -/
@[instance_reducible] noncomputable def profileA3FamilyFintype (F : Finset (ChargeDensity L)) :
    Fintype {σ : ChargeDensity L // σ ∈ F} :=
  Fintype.ofFinset F (by intro σ; rfl)

/-- The finite set of family labels in one overlap-graph component. -/
noncomputable def profileA3OverlapComponentMembers (F : Finset (ChargeDensity L))
    (c : (profileA3OverlapGraph F).ConnectedComponent) : Finset (ChargeDensity L) := by
  classical
  haveI : Fintype {σ : ChargeDensity L // σ ∈ F} := profileA3FamilyFintype F
  exact (c.supp.toFinset.image Subtype.val)

/-- The finite set of vertices in a finite simple-graph component. -/
noncomputable def profileA3GraphComponentVertices {V : Type*} [Fintype V]
    {G : SimpleGraph V} (c : G.ConnectedComponent) : Finset V := by
  classical
  exact c.supp.toFinset

@[simp] theorem mem_profileA3GraphComponentVertices {V : Type*} [Fintype V]
    {G : SimpleGraph V} (c : G.ConnectedComponent) (v : V) :
    v ∈ profileA3GraphComponentVertices c ↔ G.connectedComponentMk v = c := by
  classical
  simp [profileA3GraphComponentVertices, SimpleGraph.ConnectedComponent.mem_supp_iff]

set_option linter.style.haveILetI false in
theorem profileA3_mem_overlapComponentMembers {F : Finset (ChargeDensity L)}
    (c : (profileA3OverlapGraph F).ConnectedComponent) {σ : ChargeDensity L} :
    σ ∈ profileA3OverlapComponentMembers F c ↔
      ∃ hσ : σ ∈ F, (profileA3OverlapGraph F).connectedComponentMk ⟨σ, hσ⟩ = c := by
  classical
  haveI : Fintype {σ : ChargeDensity L // σ ∈ F} := profileA3FamilyFintype F
  simp [profileA3OverlapComponentMembers, SimpleGraph.ConnectedComponent.mem_supp_iff]

theorem profileA3_overlapComponentMembers_nonempty
    (F : Finset (ChargeDensity L)) (σ : ChargeDensity L) (hσ : σ ∈ F) :
    (profileA3OverlapComponentMembers F
      ((profileA3OverlapGraph F).connectedComponentMk ⟨σ, hσ⟩)).Nonempty := by
  classical
  refine ⟨σ, (profileA3_mem_overlapComponentMembers _).2 ⟨hσ, rfl⟩⟩

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
