/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Lattice2D.SquareFree
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Tactic

/-!
# Uniform square-lattice walk bounds

The full free-box graph has at most four choices for each step of a walk.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Clock.HighTemp

open FroehlichSpencer.BKT.Lattice2D

private theorem pathGraph_degree_le_two (L : ℕ) (x : Fin L)
    [Fintype ((SimpleGraph.pathGraph L).neighborSet x)] :
    (SimpleGraph.pathGraph L).degree x ≤ 2 := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  let code : (SimpleGraph.pathGraph L).neighborSet x → Fin 2 := fun y =>
    if y.1.val + 1 = x.val then 0 else 1
  have hinj : Function.Injective code := by
    intro y z h
    by_cases hy : y.1.val + 1 = x.val
    · have hz : z.1.val + 1 = x.val := by
        simpa [code, hy] using h
      apply Subtype.ext
      apply Fin.ext
      omega
    · have hz : z.1.val + 1 ≠ x.val := by
        intro hz
        have hyCode : code y = 1 := by simp [code, hy]
        have hzCode : code z = 0 := by simp [code, hz]
        rw [hyCode, hzCode] at h
        exact Fin.zero_ne_one h.symm
      have hy' := SimpleGraph.pathGraph_adj.mp y.2
      have hz' := SimpleGraph.pathGraph_adj.mp z.2
      apply Subtype.ext
      apply Fin.ext
      rcases hy' with hys | hys
      · rcases hz' with hzs | hzs
        · omega
        · omega
      · omega
  have hcard := Fintype.card_le_of_injective code hinj
  simpa using hcard

/-- Every vertex in a finite square lattice has degree at most four. -/
theorem squareBox_degree_le_four (L : ℕ) (x : Fin L × Fin L)
    [Fintype ((SimpleGraph.pathGraph L).neighborSet x.1)]
    [Fintype ((SimpleGraph.pathGraph L).neighborSet x.2)]
    [Fintype ((SimpleGraph.pathGraph L □ SimpleGraph.pathGraph L).neighborSet x)] :
    (SimpleGraph.pathGraph L □ SimpleGraph.pathGraph L).degree x ≤ 4 := by
  classical
  rw [SimpleGraph.degree_boxProd]
  have h₁ := pathGraph_degree_le_two L x.1
  have h₂ := pathGraph_degree_le_two L x.2
  omega

/-- A graph of maximum degree four has at most `4^n` walks of length `n` between fixed vertices.
-/
theorem card_finsetWalkLength_le_four_pow {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [SimpleGraph.LocallyFinite G]
    (hdeg : ∀ x, G.degree x ≤ 4) (n : ℕ) (u v : V) :
    (G.finsetWalkLength n u v).card ≤ 4 ^ n := by
  classical
  induction n generalizing u with
  | zero =>
      rw [SimpleGraph.finsetWalkLength]
      split_ifs with h
      · subst v
        simp
      · simp
  | succ n ih =>
      rw [SimpleGraph.finsetWalkLength]
      calc
        (Finset.univ.biUnion fun w : G.neighborSet u =>
            (G.finsetWalkLength n w.1 v).map
              ⟨fun p => SimpleGraph.Walk.cons w.2 p, fun _ _ h => by
                cases h; rfl⟩).card
          ≤ ∑ w ∈ (Finset.univ : Finset (G.neighborSet u)),
              ((G.finsetWalkLength n w.1 v).map
                ⟨fun p => SimpleGraph.Walk.cons w.2 p, fun _ _ h => by
                  cases h; rfl⟩).card :=
                Finset.card_biUnion_le
        _ ≤ ∑ _w ∈ (Finset.univ : Finset (G.neighborSet u)), 4 ^ n := by
              apply Finset.sum_le_sum
              intro w hw
              rw [Finset.card_map]
              exact ih w.1
        _ = Fintype.card (G.neighborSet u) * 4 ^ n := by simp
        _ = G.degree u * 4 ^ n := by rw [SimpleGraph.card_neighborSet_eq_degree]
        _ ≤ 4 * 4 ^ n := Nat.mul_le_mul_right _ (hdeg u)
        _ = 4 ^ (n + 1) := by rw [pow_succ]; ring

/-- The finite path graph on an interval has finite neighbor sets. -/
@[instance_reducible] noncomputable instance pathGraphLocallyFinite (L : ℕ) :
    SimpleGraph.LocallyFinite (SimpleGraph.pathGraph L) := by
  classical
  exact fun _ => Fintype.ofFinite _

/-- The square lattice graph on a finite box has finite neighbor sets. -/
@[instance_reducible] noncomputable instance squareBoxLocallyFinite (L : ℕ) :
    SimpleGraph.LocallyFinite
      (SimpleGraph.pathGraph L □ SimpleGraph.pathGraph L) := by
  classical
  exact fun _ => Fintype.ofFinite _

/-- Uniform walk-count bound specialized to a finite square lattice. -/
theorem squareBox_walkCount_le_four_pow (L n : ℕ) (u v : Fin L × Fin L) :
    ((SimpleGraph.pathGraph L □ SimpleGraph.pathGraph L).finsetWalkLength n u v).card ≤
      4 ^ n := by
  classical
  have hdeg : ∀ x, (SimpleGraph.pathGraph L □ SimpleGraph.pathGraph L).degree x ≤ 4 := by
    intro x
    exact squareBox_degree_le_four L x
  exact card_finsetWalkLength_le_four_pow
    (G := SimpleGraph.pathGraph L □ SimpleGraph.pathGraph L) hdeg n u v

end FroehlichSpencer.BKT.Clock.HighTemp

end
