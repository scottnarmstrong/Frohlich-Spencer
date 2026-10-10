/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.FiniteGraph.Green
public import FroehlichSpencer.BKT.Potential.Variational
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Prod

/-!
# Internal free square graph

The vertices are `{0, …, L-1}²`; horizontal and vertical edges are each
represented once, oriented in the positive coordinate direction. This
internal carrier is intentionally independent of the public interface carriers.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Lattice2D

/-- Vertices of the free square of side length `L`, the KP p. 2 domain
`{0, …, L - 1}²`. -/
abbrev SquareFreeVertex (L : ℕ) := Fin L × Fin L

/-- Horizontal nearest-neighbour edges in the KP p. 2 free square, each listed
once and oriented in the positive coordinate direction. -/
abbrev SquareFreeHorizontalEdge (L : ℕ) :=
  {i : Fin L // i.val + 1 < L} × Fin L

/-- Vertical nearest-neighbour edges in the KP p. 2 free square, each listed
once and oriented in the positive coordinate direction. -/
abbrev SquareFreeVerticalEdge (L : ℕ) :=
  Fin L × {j : Fin L // j.val + 1 < L}

/-- Edge carrier for the internal KP p. 2 free square, with each unoriented
nearest-neighbour edge represented once. -/
abbrev SquareFreeEdge (L : ℕ) :=
  Sum (SquareFreeHorizontalEdge L) (SquareFreeVerticalEdge L)

/-- The nearest-neighbour free square multigraph from KP p. 2, represented with
positive-coordinate orientations and each edge counted once. -/
def squareFreeGraph (L : ℕ) : Multigraph (SquareFreeVertex L) (SquareFreeEdge L) where
  src
    | .inl e => (e.1.1, e.2)
    | .inr e => (e.1, e.2.1)
  tgt
    | .inl e => (⟨e.1.1.val + 1, e.1.2⟩, e.2)
    | .inr e => (e.1, ⟨e.2.1.val + 1, e.2.2⟩)
  src_ne_tgt := by
    intro e h
    cases e with
    | inl e =>
        have hx := congrArg Prod.fst h
        have hv : e.1.1.val = e.1.1.val + 1 := congrArg Fin.val hx
        omega
    | inr e =>
        have hy := congrArg Prod.snd h
        have hv : e.2.1.val = e.2.1.val + 1 := congrArg Fin.val hy
        omega

/-- Multigraph adjacency in the free square is coordinatewise path
adjacency. -/
theorem squareFreeGraph_adj_iff {L : ℕ} (p q : SquareFreeVertex L) :
    (squareFreeGraph L).Adj p q ↔
      ((SimpleGraph.pathGraph L).Adj p.1 q.1 ∧ p.2 = q.2) ∨
        ((SimpleGraph.pathGraph L).Adj p.2 q.2 ∧ p.1 = q.1) := by
  constructor
  · rintro ⟨e, h | h⟩
    · cases e with
      | inl e =>
          rcases h with ⟨hs, ht⟩
          have hsi := congrArg Prod.fst hs
          have hsj := congrArg Prod.snd hs
          have hti := congrArg Prod.fst ht
          have htj := congrArg Prod.snd ht
          simp only [squareFreeGraph] at hsi hsj hti htj
          left
          refine ⟨SimpleGraph.pathGraph_adj.mpr (Or.inl ?_), hsj.symm.trans htj⟩
          have hval : e.1.1.val + 1 = q.1.val := by
            simpa only [Fin.val_mk] using congrArg Fin.val hti
          have hsval : e.1.1.val = p.1.val := congrArg Fin.val hsi
          calc
            p.1.val + 1 = e.1.1.val + 1 := by rw [hsval.symm]
            _ = q.1.val := hval
      | inr e =>
          rcases h with ⟨hs, ht⟩
          have hsi := congrArg Prod.fst hs
          have hsj := congrArg Prod.snd hs
          have hti := congrArg Prod.fst ht
          have htj := congrArg Prod.snd ht
          simp only [squareFreeGraph] at hsi hsj hti htj
          right
          refine ⟨SimpleGraph.pathGraph_adj.mpr (Or.inl ?_), hsi.symm.trans hti⟩
          have hval : e.2.1.val + 1 = q.2.val := by
            simpa only [Fin.val_mk] using congrArg Fin.val htj
          have hsval : e.2.1.val = p.2.val := congrArg Fin.val hsj
          calc
            p.2.val + 1 = e.2.1.val + 1 := by rw [hsval.symm]
            _ = q.2.val := hval
    · cases e with
      | inl e =>
          rcases h with ⟨hs, ht⟩
          have hsi := congrArg Prod.fst hs
          have hsj := congrArg Prod.snd hs
          have hti := congrArg Prod.fst ht
          have htj := congrArg Prod.snd ht
          simp only [squareFreeGraph] at hsi hsj hti htj
          left
          refine ⟨SimpleGraph.pathGraph_adj.mpr (Or.inr ?_), htj.symm.trans hsj⟩
          have hval : e.1.1.val + 1 = p.1.val := by
            simpa only [Fin.val_mk] using congrArg Fin.val hti
          have hsval : e.1.1.val = q.1.val := congrArg Fin.val hsi
          calc
            q.1.val + 1 = e.1.1.val + 1 := by rw [hsval.symm]
            _ = p.1.val := hval
      | inr e =>
          rcases h with ⟨hs, ht⟩
          have hsi := congrArg Prod.fst hs
          have hsj := congrArg Prod.snd hs
          have hti := congrArg Prod.fst ht
          have htj := congrArg Prod.snd ht
          simp only [squareFreeGraph] at hsi hsj hti htj
          right
          refine ⟨SimpleGraph.pathGraph_adj.mpr (Or.inr ?_), hti.symm.trans hsi⟩
          have hval : e.2.1.val + 1 = p.2.val := by
            simpa only [Fin.val_mk] using congrArg Fin.val htj
          have hsval : e.2.1.val = q.2.val := congrArg Fin.val hsj
          calc
            q.2.val + 1 = e.2.1.val + 1 := by rw [hsval.symm]
            _ = p.2.val := hval
  · rintro (⟨h, hy⟩ | ⟨h, hx⟩)
    · have h := SimpleGraph.pathGraph_adj.mp h
      rcases h with h | h
      · refine ⟨Sum.inl (⟨p.1, by have := q.1.isLt; omega⟩, p.2), Or.inl ⟨rfl, ?_⟩⟩
        simp only [squareFreeGraph]
        apply Prod.ext
        · apply Fin.ext
          exact h
        · exact hy
      · refine ⟨Sum.inl (⟨q.1, by have := p.1.isLt; omega⟩, q.2), Or.inr ⟨rfl, ?_⟩⟩
        simp only [squareFreeGraph]
        apply Prod.ext
        · apply Fin.ext
          exact h
        · exact hy.symm
    · have h := SimpleGraph.pathGraph_adj.mp h
      rcases h with h | h
      · refine ⟨Sum.inr (p.1, ⟨p.2, by have := q.2.isLt; omega⟩), Or.inl ⟨rfl, ?_⟩⟩
        simp only [squareFreeGraph]
        apply Prod.ext
        · exact hx
        · apply Fin.ext
          exact h
      · refine ⟨Sum.inr (q.1, ⟨q.2, by have := p.2.isLt; omega⟩), Or.inr ⟨rfl, ?_⟩⟩
        simp only [squareFreeGraph]
        apply Prod.ext
        · exact hx.symm
        · apply Fin.ext
          exact h

/-- The simple graph underlying the internal free square is the box product
of two path graphs. -/
theorem squareFreeGraph_toSimpleGraph (L : ℕ) :
    (squareFreeGraph L).toSimpleGraph =
      SimpleGraph.pathGraph L □ SimpleGraph.pathGraph L := by
  ext p q
  rw [SimpleGraph.boxProd_adj]
  change (p ≠ q ∧
    ((squareFreeGraph L).Adj p q ∨ (squareFreeGraph L).Adj q p)) ↔ _
  constructor
  · rintro ⟨_, h | h⟩
    · exact (squareFreeGraph_adj_iff p q).mp h
    · rcases (squareFreeGraph_adj_iff q p).mp h with h | h
      · exact Or.inl ⟨h.1.symm, h.2.symm⟩
      · exact Or.inr ⟨h.1.symm, h.2.symm⟩
  · intro h
    have hne : p ≠ q := by
      intro hpq
      subst q
      rcases h with ⟨ha, _⟩ | ⟨ha, _⟩
      · rcases SimpleGraph.pathGraph_adj.mp ha with ha | ha <;> omega
      · rcases SimpleGraph.pathGraph_adj.mp ha with ha | ha <;> omega
    exact ⟨hne, Or.inl ((squareFreeGraph_adj_iff p q).2 h)⟩

/-- The internal free square graph is connected whenever its side is
positive. -/
theorem squareFreeGraph_connected {L : ℕ} (hL : 0 < L) :
    (squareFreeGraph L).Connected := by
  change ((squareFreeGraph L).toSimpleGraph).Connected
  rw [squareFreeGraph_toSimpleGraph]
  have hpath : (SimpleGraph.pathGraph L).Connected := by
    have hsum : L - 1 + 1 = L := Nat.sub_add_cancel (by omega)
    rw [← hsum]
    exact SimpleGraph.pathGraph_connected (L - 1)
  apply SimpleGraph.Connected.boxProd
  · exact hpath
  · exact hpath

end FroehlichSpencer.BKT.Lattice2D

end
