/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Factorization of the bond-subset expansion

Summing all bond subsets that contain a specified path factors into the path
weight and the unrestricted product on the remaining bonds.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Clock.HighTemp

variable {E : Type*} [DecidableEq E] [Fintype E]

/-- Sum the product weights of every edge subset containing `P`. -/
theorem sum_prod_supersets_eq {R : Type*} [CommSemiring R] (g : E → R)
    (P : Finset E) (hP : P ⊆ Finset.univ) :
    (∑ A ∈ (Finset.univ : Finset E).powerset,
        if P ⊆ A then ∏ e ∈ A, g e else 0) =
      (∏ e ∈ P, g e) * ∏ e ∈ Finset.univ \ P, (1 + g e) := by
  classical
  let S := ((Finset.univ : Finset E).powerset.filter fun A => P ⊆ A)
  have hsum : (∑ A ∈ (Finset.univ : Finset E).powerset,
      if P ⊆ A then ∏ e ∈ A, g e else 0) = ∑ A ∈ S, ∏ e ∈ A, g e := by
    simp [S, Finset.sum_filter]
  rw [hsum]
  calc
    (∑ A ∈ S, ∏ e ∈ A, g e) =
        ∑ B ∈ (Finset.univ \ P).powerset,
          (∏ e ∈ P, g e) * ∏ e ∈ B, g e := by
      apply Finset.sum_bij (fun A hA => A \ P)
      · intro A hA
        have hA' := (Finset.mem_filter.mp hA).1
        simp only [Finset.mem_powerset] at hA'
        simp only [Finset.mem_powerset]
        exact Finset.sdiff_subset_sdiff_left P hA'
      · intro A hA A' hA' hEq
        have hPA : P ⊆ A := (Finset.mem_filter.mp hA).2
        have hPA' : P ⊆ A' := (Finset.mem_filter.mp hA').2
        have h₁ : P ∪ (A \ P) = A := Finset.union_sdiff_of_subset hPA
        have h₂ : P ∪ (A' \ P) = A' := Finset.union_sdiff_of_subset hPA'
        rw [← h₁, ← h₂, hEq]
      · intro B hB
        simp only [Finset.mem_powerset] at hB
        refine ⟨P ∪ B, ?_, ?_⟩
        · simp only [S, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨Finset.union_subset hP (hB.trans Finset.sdiff_subset),
            Finset.subset_union_left⟩
        · have hdisj : Disjoint P B := Finset.disjoint_left.mpr fun e heP heB =>
            (Finset.mem_sdiff.mp (hB heB)).2 heP
          rw [Finset.union_sdiff_cancel_left hdisj]
      · intro A hA
        have hPA : P ⊆ A := (Finset.mem_filter.mp hA).2
        have hsplit : A = P ∪ (A \ P) := (Finset.union_sdiff_of_subset hPA).symm
        rw [hsplit, Finset.prod_union]
        · rw [Finset.union_sdiff_cancel_left Finset.disjoint_sdiff]
        · exact Finset.disjoint_sdiff
    _ = (∏ e ∈ P, g e) * ∏ e ∈ Finset.univ \ P, (1 + g e) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.prod_one_add]

end FroehlichSpencer.BKT.Clock.HighTemp

end
