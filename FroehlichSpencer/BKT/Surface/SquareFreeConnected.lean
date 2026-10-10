/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import FroehlichSpencer.BKT.Surface.MultigraphSimpleGraph
public import FroehlichSpencer.BKT.Surface.SquareFree
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Common

/-! # Connectedness of the free square domain -/

public section

namespace FroehlichSpencer.BKT

/-- `Λ_L^free` is connected (KP p. 2 treats square domains as finite connected graphs). -/
theorem squareFree_connected (L : ℕ) (hL : 1 < L) : (squareFree L).toSimpleGraph.Connected := by
  have hstep : ∀ x y : Fin L × Fin L, toLex x < toLex y →
      ({|((x.1 : ℕ) : ℤ) - (y.1 : ℕ)|, |((x.2 : ℕ) : ℤ) - (y.2 : ℕ)|} : Finset ℤ) = {0, 1} →
      (squareFree L).toSimpleGraph.Reachable x y := by
    intro x y hlt hxy
    refine SimpleGraph.Adj.reachable ⟨?_, Or.inl ⟨⟨(x, y), hlt, hxy⟩, Or.inl ⟨rfl, rfl⟩⟩⟩
    rintro rfl
    exact lt_irrefl _ hlt
  have h0 : ∀ x : Fin L × Fin L,
      (squareFree L).toSimpleGraph.Reachable (⟨0, by omega⟩, ⟨0, by omega⟩) x := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have h1 : ∀ (a : ℕ) (ha : a < L),
        (squareFree L).toSimpleGraph.Reachable (⟨0, by omega⟩, ⟨0, by omega⟩)
          (⟨a, ha⟩, ⟨0, by omega⟩) := by
      intro a
      induction a with
      | zero => intro _; rfl
      | succ n ih =>
        intro ha
        refine (ih (by omega)).trans (hstep _ _ ?_ ?_)
        · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by simp [Fin.lt_def]))
        · simp [Finset.pair_comm, abs_one]
    have h2 : ∀ (b : ℕ) (hb : b < L),
        (squareFree L).toSimpleGraph.Reachable (⟨0, by omega⟩, ⟨0, by omega⟩)
          (⟨a, ha⟩, ⟨b, hb⟩) := by
      intro b
      induction b with
      | zero => intro _; exact h1 a ha
      | succ n ih =>
        intro hb
        refine (ih (by omega)).trans (hstep _ _ ?_ ?_)
        · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, by simp [Fin.lt_def]⟩)
        · simp [abs_one]
    exact h2 b hb
  exact SimpleGraph.connected_iff_exists_forall_reachable _ |>.mpr ⟨_, h0⟩

end FroehlichSpencer.BKT

end
