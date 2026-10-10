/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.MarkedCurrentSelection
public import FroehlichSpencer.BKT.Villain.CurrentExpansion
import Mathlib.Tactic

/-!
# A one-edge obstruction to importing integer-current neutrality

Finite clock spin sums require divergence to vanish modulo `N`, not as an integer.

On a single
oriented edge with `N = 2`, the Gaussian alias frequency `2` has nonzero integer divergence at
both endpoints but is neutral modulo two.

Thus continuous Villain-current neutrality cannot be
reused as an integer equality after passing to the clock alias classes.
-/

@[expose] public section

open FroehlichSpencer.BKT

namespace FroehlichSpencer.BKT.Clock.VillainClock

/-- The minimal graph: one oriented edge from vertex zero to vertex one. -/
def oneEdgeGraph : Multigraph (Fin 2) Unit where
  src := fun _ => 0
  tgt := fun _ => 1
  src_ne_tgt := by decide

/-- The integer alias current with frequency two on the single edge. -/
def oneEdgeAliasCurrent : Unit → ℤ := fun _ => 2

theorem oneEdgeAliasCurrent_source_divergence :
    Villain.currentDivergence oneEdgeGraph oneEdgeAliasCurrent 0 = 2 := by
  simp [Villain.currentDivergence, oneEdgeGraph, oneEdgeAliasCurrent]

theorem oneEdgeAliasCurrent_target_divergence :
    Villain.currentDivergence oneEdgeGraph oneEdgeAliasCurrent 1 = -2 := by
  simp [Villain.currentDivergence, oneEdgeGraph, oneEdgeAliasCurrent]

/-- The frequency-two integer alias belongs to residue class zero for the two-clock model. -/
theorem frequency_two_in_zero_alias_class :
    (2 : ℤ) ∈ {p : ℤ | (2 : ℤ) ∣ p - 0} := by
  exact ⟨1, by norm_num⟩

/-- The corresponding Gaussian Fourier mode has strictly positive real weight. -/
theorem gaussianMode_two_ne_zero {β : ℝ} : gaussianMode β 2 ≠ 0 := by
  simp only [gaussianMode]
  exact_mod_cast (Real.exp_ne_zero _)

/-- Exact failure of integer neutrality: the one-edge alias current is neutral modulo two at
both vertices, although its integer divergence is nonzero at both vertices. -/
theorem oneEdge_alias_is_modularlyNeutral_not_integerNeutral :
    (∀ v : Fin 2, (2 : ℤ) ∣ Villain.currentDivergence oneEdgeGraph oneEdgeAliasCurrent v) ∧
      ¬ (∀ v : Fin 2, Villain.currentDivergence oneEdgeGraph oneEdgeAliasCurrent v = 0) := by
  constructor
  · intro v
    fin_cases v
    · simp [oneEdgeAliasCurrent_source_divergence]
    · simp [oneEdgeAliasCurrent_target_divergence]
  · intro h
    have := h 0
    rw [oneEdgeAliasCurrent_source_divergence] at this
    norm_num at this

end FroehlichSpencer.BKT.Clock.VillainClock

end
