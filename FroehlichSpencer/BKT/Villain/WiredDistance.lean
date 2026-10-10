/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Villain.SquareSymmetry
public import FroehlichSpencer.BKT.Surface.MultigraphSimpleGraph
public import FroehlichSpencer.BKT.FiniteGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.NormNum

/-! # Wired-square distance -/

@[expose] public section

namespace FroehlichSpencer.BKT

private noncomputable def squareFreeEdgeOfShape {L : ℕ} (p q : Fin L × Fin L)
    (hpq : p ≠ q)
    (hshape : ({|((p.1 : ℕ) : ℤ) - (q.1 : ℕ)|,
      |((p.2 : ℕ) : ℤ) - (q.2 : ℕ)|} : Finset ℤ) = {0, 1}) : SquareFreeEdge L := by
  classical
  by_cases hlex : toLex p < toLex q
  · exact ⟨(p, q), hlex, hshape⟩
  · have hne : toLex q ≠ toLex p := by
      intro he
      apply hpq
      exact (toLex_inj.mp he).symm
    have hrev : toLex q < toLex p := lt_of_le_of_ne (le_of_not_gt hlex) hne
    refine ⟨(q, p), hrev, ?_⟩
    simpa only [abs_sub_comm] using hshape

private theorem squareFreeShape_of_horizontal {L : ℕ} (p q : Fin L × Fin L)
    (hrow : p.2 = q.2) (hstep : p.1.val + 1 = q.1.val) :
    ({|((p.1 : ℕ) : ℤ) - (q.1 : ℕ)|,
      |((p.2 : ℕ) : ℤ) - (q.2 : ℕ)|} : Finset ℤ) = {0, 1} := by
  have hx : (q.1.val : ℤ) = (p.1.val : ℤ) + 1 := by exact_mod_cast hstep.symm
  have hy : (p.2.val : ℤ) = (q.2.val : ℤ) := by
    exact_mod_cast congrArg Fin.val hrow
  have hdx : (p.1.val : ℤ) - (q.1.val : ℤ) = -1 := by omega
  have hdy : (p.2.val : ℤ) - (q.2.val : ℤ) = 0 := by omega
  rw [hdx, hdy]
  exact Finset.pair_comm 1 0

private theorem squareFreeShape_of_vertical {L : ℕ} (p q : Fin L × Fin L)
    (hcol : p.1 = q.1) (hstep : p.2.val + 1 = q.2.val) :
    ({|((p.1 : ℕ) : ℤ) - (q.1 : ℕ)|,
      |((p.2 : ℕ) : ℤ) - (q.2 : ℕ)|} : Finset ℤ) = {0, 1} := by
  have hx : (p.1.val : ℤ) = (q.1.val : ℤ) := by
    exact_mod_cast congrArg Fin.val hcol
  have hy : (q.2.val : ℤ) = (p.2.val : ℤ) + 1 := by exact_mod_cast hstep.symm
  have hdx : (p.1.val : ℤ) - (q.1.val : ℤ) = 0 := by omega
  have hdy : (p.2.val : ℤ) - (q.2.val : ℤ) = -1 := by omega
  rw [hdx, hdy]
  norm_num

private theorem squareFree_adj_of_horizontal {L : ℕ} (p q : Fin L × Fin L)
    (hrow : p.2 = q.2) (hstep : p.1.val + 1 = q.1.val) :
    Multigraph.Adj (squareFree L) p q := by
  have hpq : p ≠ q := by
    intro h
    have hv := congrArg (fun v : Fin L × Fin L => v.1.val) h
    omega
  let e := squareFreeEdgeOfShape p q hpq (squareFreeShape_of_horizontal p q hrow hstep)
  by_cases hlex : toLex p < toLex q
  · refine ⟨e, Or.inl ?_⟩
    simp [e, squareFree, squareFreeEdgeOfShape, hlex]
  · refine ⟨e, Or.inr ?_⟩
    simp [e, squareFree, squareFreeEdgeOfShape, hlex]

private theorem squareFree_adj_of_vertical {L : ℕ} (p q : Fin L × Fin L)
    (hcol : p.1 = q.1) (hstep : p.2.val + 1 = q.2.val) :
    Multigraph.Adj (squareFree L) p q := by
  have hpq : p ≠ q := by
    intro h
    have hv := congrArg (fun v : Fin L × Fin L => v.2.val) h
    omega
  let e := squareFreeEdgeOfShape p q hpq (squareFreeShape_of_vertical p q hcol hstep)
  by_cases hlex : toLex p < toLex q
  · refine ⟨e, Or.inl ?_⟩
    simp [e, squareFree, squareFreeEdgeOfShape, hlex]
  · refine ⟨e, Or.inr ?_⟩
    simp [e, squareFree, squareFreeEdgeOfShape, hlex]

/--
A horizontal nearest-neighbour step in the free square is an edge of the wired
simple graph.
-/
theorem squareZero_adj_of_horizontal_step {L : ℕ} (p q : Fin L × Fin L)
    (hrow : p.2 = q.2) (hstep : p.1.val + 1 = q.1.val) :
    (squareZero L).toSimpleGraph.Adj (some p) (some q) := by
  have hpq : p ≠ q := by
    intro h
    have hv := congrArg (fun v : Fin L × Fin L => v.1.val) h
    omega
  have hfree := squareFree_adj_of_horizontal p q hrow hstep
  have hwire : Multigraph.Adj (squareZero L) (some p) (some q) := by
    rcases hfree with ⟨e, h | h⟩
    · exact ⟨Sum.inl e, Or.inl (by simpa [squareZero] using h)⟩
    · exact ⟨Sum.inl e, Or.inr (by simpa [squareZero] using h)⟩
  change some p ≠ some q ∧
    (Multigraph.Adj (squareZero L) (some p) (some q) ∨
      Multigraph.Adj (squareZero L) (some q) (some p))
  exact ⟨by simpa using hpq, Or.inl hwire⟩

/--
A vertical nearest-neighbour step in the free square is an edge of the wired
simple graph.
-/
theorem squareZero_adj_of_vertical_step {L : ℕ} (p q : Fin L × Fin L)
    (hcol : p.1 = q.1) (hstep : p.2.val + 1 = q.2.val) :
    (squareZero L).toSimpleGraph.Adj (some p) (some q) := by
  have hpq : p ≠ q := by
    intro h
    have hv := congrArg (fun v : Fin L × Fin L => v.2.val) h
    omega
  have hfree := squareFree_adj_of_vertical p q hcol hstep
  have hwire : Multigraph.Adj (squareZero L) (some p) (some q) := by
    rcases hfree with ⟨e, h | h⟩
    · exact ⟨Sum.inl e, Or.inl (by simpa [squareZero] using h)⟩
    · exact ⟨Sum.inl e, Or.inr (by simpa [squareZero] using h)⟩
  change some p ≠ some q ∧
    (Multigraph.Adj (squareZero L) (some p) (some q) ∨
      Multigraph.Adj (squareZero L) (some q) (some p))
  exact ⟨by simpa using hpq, Or.inl hwire⟩

end FroehlichSpencer.BKT

end
