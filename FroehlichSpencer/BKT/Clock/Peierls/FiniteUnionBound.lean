/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! # Finite weighted union bound -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace FroehlichSpencer.BKT.Clock.Peierls

/-- If a finite family of events covers a target event, its total weight is bounded by the sum of
all event weights. Overlap only increases the right hand side. -/
theorem weightedFinset_union_bound
    {X I : Type*} [Fintype X] [Fintype I] [DecidableEq X]
    (A : Finset X) (events : I → Finset X) (W : X → ℝ)
    (hcover : ∀ x ∈ A, ∃ i, x ∈ events i)
    (hW : ∀ x, 0 ≤ W x) :
    (∑ x ∈ A, W x) ≤ ∑ i, ∑ x ∈ events i, W x := by
  classical
  have hpoint (x : X) (hx : x ∈ A) :
      W x ≤ ∑ i : I, if x ∈ events i then W x else 0 := by
    obtain ⟨i, hi⟩ := hcover x hx
    have hnonneg (j : I) : 0 ≤ if x ∈ events j then W x else 0 := by
      by_cases hj : x ∈ events j
      · simp [hj, hW]
      · simp [hj]
    have hsingle := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
    simpa [hi] using hsingle
  calc
    (∑ x ∈ A, W x) ≤ ∑ x ∈ A, ∑ i : I, if x ∈ events i then W x else 0 := by
      apply Finset.sum_le_sum
      intro x hx
      exact hpoint x hx
    _ = ∑ i : I, ∑ x ∈ A, if x ∈ events i then W x else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ i : I, ∑ x ∈ events i, W x := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        (∑ x ∈ A, if x ∈ events i then W x else 0) =
            ∑ x ∈ A.filter (fun x => x ∈ events i), W x := by
              rw [Finset.sum_filter]
        _ ≤ ∑ x ∈ events i, W x := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
                (show A.filter (fun x => x ∈ events i) ⊆ events i from by
                  intro x hx
                  exact (Finset.mem_filter.mp hx).2)
              intro x hxA hxNot
              exact hW x

end FroehlichSpencer.BKT.Clock.Peierls

end
