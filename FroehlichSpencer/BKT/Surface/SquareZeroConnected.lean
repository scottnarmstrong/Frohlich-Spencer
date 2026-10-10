/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import FroehlichSpencer.BKT.Surface.MultigraphSimpleGraph
public import FroehlichSpencer.BKT.Surface.SquareZero
import FroehlichSpencer.BKT.Surface.SquareFreeConnected
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Common

/-! # Connectedness of the wired square domain -/

public section

namespace FroehlichSpencer.BKT

/-- `Λ_L^zero` is connected (KP p. 2 treats square domains as finite connected graphs; the graph
distance `dist (j, z)` of KP Theorem 1.3 is that of a connected graph). -/
theorem squareZero_connected (L : ℕ) (hL : 1 < L) : (squareZero L).toSimpleGraph.Connected := by
  -- the corner `(0, 0)` and its free degree
  set o : Fin L × Fin L := (⟨0, by omega⟩, ⟨0, by omega⟩) with ho
  have hdeg : (Finset.univ.filter fun e : SquareFreeEdge L =>
      (squareFree L).src e = o ∨ (squareFree L).tgt e = o).card < 4 := by
    let e₁ : SquareFreeEdge L := ⟨(o, (⟨0, by omega⟩, ⟨1, hL⟩)),
      Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, by simp [o, Fin.lt_def]⟩), by simp [o]⟩
    let e₂ : SquareFreeEdge L := ⟨(o, (⟨1, hL⟩, ⟨0, by omega⟩)),
      Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by simp [o, Fin.lt_def])),
      by simp [o, Finset.pair_comm]⟩
    have hsub : (Finset.univ.filter fun e : SquareFreeEdge L =>
        (squareFree L).src e = o ∨ (squareFree L).tgt e = o) ⊆ {e₁, e₂} := by
      intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      obtain ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, hlt, hadj⟩ := e
      simp only [squareFree] at he
      rcases he with h | h
      · -- the edge starts at the corner
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
        have h0 : (0 : ℤ) ∈ ({|((o.1 : ℕ) : ℤ) - (c : ℕ)|, |((o.2 : ℕ) : ℤ) - (d : ℕ)|} :
            Finset ℤ) := by rw [hadj]; simp
        have h1 : (1 : ℤ) ∈ ({|((o.1 : ℕ) : ℤ) - (c : ℕ)|, |((o.2 : ℕ) : ℤ) - (d : ℕ)|} :
            Finset ℤ) := by rw [hadj]; simp
        have hc : |((o.1 : ℕ) : ℤ) - (c : ℕ)| ∈ ({0, 1} : Finset ℤ) := by
          rw [← hadj]; simp
        have hd : |((o.2 : ℕ) : ℤ) - (d : ℕ)| ∈ ({0, 1} : Finset ℤ) := by
          rw [← hadj]; simp
        simp only [o, Finset.mem_insert, Finset.mem_singleton, Nat.cast_zero, zero_sub,
          abs_neg, Nat.abs_cast] at h0 h1 hc hd
        have hcd : ((c : ℕ) = 0 ∧ (d : ℕ) = 1) ∨ ((c : ℕ) = 1 ∧ (d : ℕ) = 0) := by omega
        rcases hcd with ⟨hc0, hd1⟩ | ⟨hc1, hd0⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          left
          apply Subtype.ext
          simp [e₁, o, Prod.ext_iff, Fin.ext_iff, hc0, hd1]
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          right
          apply Subtype.ext
          simp [e₂, o, Prod.ext_iff, Fin.ext_iff, hc1, hd0]
      · -- no edge ends at the corner: its source would be lexicographically below `(0, 0)`
        exfalso
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
        rcases Prod.Lex.toLex_lt_toLex.mp hlt with h' | ⟨_, h'⟩ <;>
          simp [o, Fin.lt_def] at h'
    calc _ ≤ ({e₁, e₂} : Finset (SquareFreeEdge L)).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
      _ < 4 := by omega
  -- the inclusion of the free box is a graph homomorphism
  let φ : (squareFree L).toSimpleGraph →g (squareZero L).toSimpleGraph :=
    { toFun := some
      map_rel' := by
        rintro x y ⟨hne, ⟨e, he⟩ | ⟨e, he⟩⟩
        · exact ⟨fun h => hne (Option.some_injective _ h), Or.inl ⟨Sum.inl e, by
            simpa [squareZero] using he⟩⟩
        · exact ⟨fun h => hne (Option.some_injective _ h), Or.inr ⟨Sum.inl e, by
            simpa [squareZero] using he⟩⟩ }
  -- the wired vertex is adjacent to the corner
  have hz : (squareZero L).toSimpleGraph.Adj (some o) none :=
    ⟨Option.some_ne_none _, Or.inl ⟨Sum.inr ⟨o, ⟨0, by omega⟩⟩, Or.inl ⟨rfl, rfl⟩⟩⟩
  have hfree := squareFree_connected L hL
  refine SimpleGraph.connected_iff_exists_forall_reachable _ |>.mpr ⟨some o, ?_⟩
  rintro (_ | x)
  · exact hz.reachable
  · exact (hfree.preconnected o x).map φ

end FroehlichSpencer.BKT

end
