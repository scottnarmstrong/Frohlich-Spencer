/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import FroehlichSpencer.BKT.Surface.MultigraphSimpleGraph
public import FroehlichSpencer.BKT.Surface.SquarePeriodic
import Mathlib.Tactic.Common

/-! # Connectedness of the periodic square domain -/

public section

namespace FroehlichSpencer.BKT

/-- `Λ_L^per` is connected (KP p. 2 treats square domains as finite connected graphs). -/
theorem squarePeriodic_connected (L : ℕ) (hL : 1 < L) :
    (squarePeriodic L).toSimpleGraph.Connected := by
  have hstep : ∀ x y : Fin L × Fin L, toLex x < toLex y →
      ((x.1 = y.1 ∧ (((x.2 : ℕ) : ℤ) ≡ (y.2 : ℕ) + 1 [ZMOD L] ∨
          ((y.2 : ℕ) : ℤ) ≡ (x.2 : ℕ) + 1 [ZMOD L])) ∨
        (x.2 = y.2 ∧ (((x.1 : ℕ) : ℤ) ≡ (y.1 : ℕ) + 1 [ZMOD L] ∨
          ((y.1 : ℕ) : ℤ) ≡ (x.1 : ℕ) + 1 [ZMOD L]))) →
      (squarePeriodic L).toSimpleGraph.Reachable x y := by
    intro x y hlt hxy
    refine SimpleGraph.Adj.reachable ⟨?_, Or.inl ⟨⟨(x, y), hlt, hxy⟩, Or.inl ⟨rfl, rfl⟩⟩⟩
    rintro rfl
    exact lt_irrefl _ hlt
  have h0 : ∀ x : Fin L × Fin L,
      (squarePeriodic L).toSimpleGraph.Reachable (⟨0, by omega⟩, ⟨0, by omega⟩) x := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have h1 : ∀ (a : ℕ) (ha : a < L),
        (squarePeriodic L).toSimpleGraph.Reachable (⟨0, by omega⟩, ⟨0, by omega⟩)
          (⟨a, ha⟩, ⟨0, by omega⟩) := by
      intro a
      induction a with
      | zero => intro _; rfl
      | succ n ih =>
        intro ha
        refine (ih (by omega)).trans (hstep _ _ ?_ (Or.inr ⟨rfl, Or.inr ?_⟩))
        · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by simp [Fin.lt_def]))
        · simp only
          push_cast
          exact Int.ModEq.refl _
    have h2 : ∀ (b : ℕ) (hb : b < L),
        (squarePeriodic L).toSimpleGraph.Reachable (⟨0, by omega⟩, ⟨0, by omega⟩)
          (⟨a, ha⟩, ⟨b, hb⟩) := by
      intro b
      induction b with
      | zero => intro _; exact h1 a ha
      | succ n ih =>
        intro hb
        refine (ih (by omega)).trans (hstep _ _ ?_ (Or.inl ⟨rfl, Or.inr ?_⟩))
        · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, by simp [Fin.lt_def]⟩)
        · simp only
          push_cast
          exact Int.ModEq.refl _
    exact h2 b hb
  exact SimpleGraph.connected_iff_exists_forall_reachable _ |>.mpr ⟨_, h0⟩

end FroehlichSpencer.BKT

end
