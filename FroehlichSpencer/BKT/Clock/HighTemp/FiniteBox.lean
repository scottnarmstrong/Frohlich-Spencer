/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.HighTemp.BondSplit
public import FroehlichSpencer.BKT.Clock.HighTemp.ClockRotation
public import FroehlichSpencer.BKT.Clock.HighTemp.SubsetFactor
public import FroehlichSpencer.BKT.Clock.HighTemp.WalkBounds
public import FroehlichSpencer.BKT.SpinWaves.ShellPacking
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

/-!
# Finite-box high-temperature expansion

Selected bond sets define finite subgraphs. Their disconnected marked terms
cancel by a finite clock rotation.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.HighTemp

open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Clock.Compact

/-- The positive orientation used by the square carrier makes every bond
determined by its ordered endpoints. -/
theorem rotatorBond_ext {L : ℕ} {e f : RotatorInternalBond L}
    (hs : (rotatorFreeGraph L).src e = (rotatorFreeGraph L).src f)
    (ht : (rotatorFreeGraph L).tgt e = (rotatorFreeGraph L).tgt f) : e = f := by
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      simp only [rotatorFreeGraph, squareFreeGraph, Prod.mk.injEq, Fin.ext_iff] at hs ht
      apply congrArg Sum.inl
      apply Prod.ext
      · apply Subtype.ext
        apply Fin.ext
        exact hs.1
      · apply Fin.ext
        exact hs.2
    | inr f =>
      simp only [rotatorFreeGraph, squareFreeGraph, Prod.mk.injEq, Fin.ext_iff] at hs ht
      omega
  | inr e =>
    cases f with
    | inl f =>
      simp only [rotatorFreeGraph, squareFreeGraph, Prod.mk.injEq, Fin.ext_iff] at hs ht
      omega
    | inr f =>
      simp only [rotatorFreeGraph, squareFreeGraph, Prod.mk.injEq, Fin.ext_iff] at hs ht
      apply congrArg Sum.inr
      apply Prod.ext
      · apply Fin.ext
        exact hs.1
      · apply Subtype.ext
        apply Fin.ext
        exact hs.2

/-- Equal unoriented endpoint pairs identify the unique represented square bond. -/
theorem rotatorBond_ext_symm {L : ℕ} {e f : RotatorInternalBond L}
    (h : ((rotatorFreeGraph L).src e = (rotatorFreeGraph L).src f ∧
          (rotatorFreeGraph L).tgt e = (rotatorFreeGraph L).tgt f) ∨
         ((rotatorFreeGraph L).src e = (rotatorFreeGraph L).tgt f ∧
          (rotatorFreeGraph L).tgt e = (rotatorFreeGraph L).src f)) : e = f := by
  rcases h with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact rotatorBond_ext hs ht
  · exfalso
    cases e with
    | inl e =>
      cases f with
      | inl f =>
        simp only [rotatorFreeGraph, squareFreeGraph, Prod.mk.injEq, Fin.ext_iff] at hs ht
        omega
      | inr f =>
        simp only [rotatorFreeGraph, squareFreeGraph, Prod.mk.injEq, Fin.ext_iff] at hs ht
        omega
    | inr e =>
      cases f with
      | inl f =>
        simp only [rotatorFreeGraph, squareFreeGraph, Prod.mk.injEq, Fin.ext_iff] at hs ht
        omega
      | inr f =>
        simp only [rotatorFreeGraph, squareFreeGraph, Prod.mk.injEq, Fin.ext_iff] at hs ht
        omega

/-- An unoriented square-lattice bond as its endpoint pair. -/
def rotatorBondSym2 {L : ℕ} (e : RotatorInternalBond L) : Sym2 (RotatorSpinSite L) :=
  s((rotatorFreeGraph L).src e, (rotatorFreeGraph L).tgt e)

/-- The free square has no parallel bonds. -/
theorem rotatorBondSym2_injective {L : ℕ} : Function.Injective (rotatorBondSym2 (L := L)) := by
  intro e f h
  apply rotatorBond_ext_symm
  exact Sym2.eq_iff.mp h

/-- The endpoint-pair map packaged as an embedding for path edge bookkeeping. -/
def rotatorBondSym2Embedding {L : ℕ} : RotatorInternalBond L ↪ Sym2 (RotatorSpinSite L) :=
  ⟨rotatorBondSym2, rotatorBondSym2_injective⟩

/-- The subgraph containing precisely the selected bonds. -/
def selectedBondGraph (L : ℕ) (A : Finset (RotatorInternalBond L)) :
    SimpleGraph (RotatorSpinSite L) :=
  SimpleGraph.fromEdgeSet (rotatorBondSym2 (L := L) '' (A : Set (RotatorInternalBond L)))

/-- A selected multigraph bond gives adjacency in its selected-bond graph. -/
theorem selectedBondGraph_src_adj_tgt (L : ℕ) (A : Finset (RotatorInternalBond L))
    (e : RotatorInternalBond L) (he : e ∈ A) :
    (selectedBondGraph L A).Adj ((rotatorFreeGraph L).src e)
      ((rotatorFreeGraph L).tgt e) := by
  rw [selectedBondGraph, SimpleGraph.fromEdgeSet_adj]
  refine ⟨?_, (rotatorFreeGraph L).src_ne_tgt e⟩
  exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr he)

/-- If the two marked vertices are disconnected by `A`, its marked subset-expansion term is zero.
-/
theorem clockSubsetTerm_eq_zero_of_not_reachable (N L : ℕ) (hN : 2 ≤ N) (β : ℝ)
    (A : Finset (RotatorInternalBond L)) (u v : RotatorSpinSite L)
    (hdisj : ¬ (selectedBondGraph L A).Reachable u v) :
    ∑ k : RotatorSpinSite L → Fin N,
      Real.cos (clockAngles N k u - clockAngles N k v) *
        ∏ e ∈ A, bondDefect β
          (clockAngles N k ((rotatorFreeGraph L).src e) -
            clockAngles N k ((rotatorFreeGraph L).tgt e)) = 0 := by
  classical
  let H := selectedBondGraph L A
  let C : Set (RotatorSpinSite L) := (H.connectedComponentMk u).supp
  have hu : u ∈ C := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hv : v ∉ C := by
    intro hv
    have hcomp : H.connectedComponentMk v = H.connectedComponentMk u := by
      change H.connectedComponentMk v = H.connectedComponentMk u at hv
      exact hv
    exact hdisj (SimpleGraph.ConnectedComponent.eq.mp hcomp).symm
  have hcut (e : RotatorInternalBond L) (he : e ∈ A) :
      (rotatorFreeGraph L).src e ∈ C ↔ (rotatorFreeGraph L).tgt e ∈ C := by
    exact (SimpleGraph.ConnectedComponent.mem_supp_congr_adj (H.connectedComponentMk u))
      (selectedBondGraph_src_adj_tgt L A e he)
  exact @clockMarkedBondTerm_eq_zero_of_cut (RotatorSpinSite L) (RotatorInternalBond L)
    inferInstance inferInstance inferInstance inferInstance (rotatorFreeGraph L) N ⟨by omega⟩
    hN C u v hu hv β A hcut

end FroehlichSpencer.BKT.Clock.HighTemp

end
