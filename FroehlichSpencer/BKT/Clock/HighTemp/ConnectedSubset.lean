/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.HighTemp.SubsetFactor
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

/-!
# Connected-subset union bound

The marked subset sum is bounded by summing over every path witness contained
in a connected selected-bond set, then factoring each path's supersets.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Clock.HighTemp

/-- Indexed paths may have the same edge set; summing over all of them is a
finite union bound for the connected selected-subset sum. -/
theorem connectedSubsetSum_le_indexedPathFactorization
    {E ι : Type*} [DecidableEq E] [Fintype E] [DecidableEq ι]
    (g : E → ℝ) (hg : ∀ e, 0 ≤ g e)
    (connected : Finset E → Prop) [DecidablePred connected]
    (paths : Finset ι) (pathEdges : ι → Finset E)
    (hcover : ∀ A ∈ (Finset.univ : Finset E).powerset, connected A →
      ∃ p ∈ paths, pathEdges p ⊆ A) :
    (∑ A ∈ (Finset.univ : Finset E).powerset,
      if connected A then ∏ e ∈ A, g e else 0) ≤
    ∑ p ∈ paths,
      (∏ e ∈ pathEdges p, g e) *
        ∏ e ∈ (Finset.univ : Finset E) \ pathEdges p, (1 + g e) := by
  classical
  let S := (Finset.univ : Finset E).powerset
  calc
    (∑ A ∈ S, if connected A then ∏ e ∈ A, g e else 0) ≤
        ∑ A ∈ S, ∑ p ∈ paths,
          if pathEdges p ⊆ A then ∏ e ∈ A, g e else 0 := by
      apply Finset.sum_le_sum
      intro A hA
      by_cases hconn : connected A
      · have hleft : (if connected A then ∏ e ∈ A, g e else 0) = ∏ e ∈ A, g e := by
          simp [hconn]
        rw [hleft]
        obtain ⟨p, hp, hpa⟩ := hcover A hA hconn
        calc
          (∏ e ∈ A, g e) =
              (if pathEdges p ⊆ A then ∏ e ∈ A, g e else 0) := by simp [hpa]
          _ ≤ ∑ p ∈ paths,
              if pathEdges p ⊆ A then ∏ e ∈ A, g e else 0 := by
                have hsingle := Finset.single_le_sum
                  (s := paths)
                  (f := fun q : ι => if pathEdges q ⊆ A then ∏ e ∈ A, g e else 0)
                  (fun q _ => by
                    by_cases hqa : pathEdges q ⊆ A
                    · simp [hqa, Finset.prod_nonneg (fun e he => hg e)]
                    · simp [hqa])
                  hp
                simpa [hpa] using hsingle
      · have hleft : (if connected A then ∏ e ∈ A, g e else 0) = 0 := by
          simp [hconn]
        rw [hleft]
        exact Finset.sum_nonneg fun p _ => by
          by_cases hpa : pathEdges p ⊆ A
          · simp [hpa, Finset.prod_nonneg (fun e he => hg e)]
          · simp [hpa]
    _ = ∑ p ∈ paths, ∑ A ∈ S,
        if pathEdges p ⊆ A then ∏ e ∈ A, g e else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ p ∈ paths,
        (∏ e ∈ pathEdges p, g e) *
          ∏ e ∈ (Finset.univ : Finset E) \ pathEdges p, (1 + g e) := by
          apply Finset.sum_congr rfl
          intro p _hp
          exact sum_prod_supersets_eq (R := ℝ) g (pathEdges p)
            (Finset.subset_univ _)

/-- Normalize the supersets sum by the unrestricted bond product. -/
theorem sum_prod_supersets_eq_total_mul_ratio
    {E : Type*} [DecidableEq E] [Fintype E]
    (g : E → ℝ) (P : Finset E) (hden : ∀ e, 1 + g e ≠ 0) :
    (∑ A ∈ (Finset.univ : Finset E).powerset,
      if P ⊆ A then ∏ e ∈ A, g e else 0) =
      (∏ e : E, (1 + g e)) * ∏ e ∈ P, g e / (1 + g e) := by
  rw [sum_prod_supersets_eq (R := ℝ) g P (Finset.subset_univ P)]
  have hsplit (e : E) : g e = (1 + g e) * (g e / (1 + g e)) := by
    calc
      g e = g e / (1 + g e) * (1 + g e) := (div_mul_cancel₀ (g e) (hden e)).symm
      _ = (1 + g e) * (g e / (1 + g e)) := mul_comm _ _
  calc
    (∏ e ∈ P, g e) * ∏ e ∈ Finset.univ \ P, (1 + g e) =
        (∏ e ∈ P, (1 + g e) * (g e / (1 + g e))) *
          ∏ e ∈ Finset.univ \ P, (1 + g e) := by
            congr 1
            apply Finset.prod_congr rfl
            intro e he
            exact hsplit e
    _ = ((∏ e ∈ P, (1 + g e)) * ∏ e ∈ P, (g e / (1 + g e))) *
          ∏ e ∈ Finset.univ \ P, (1 + g e) := by rw [Finset.prod_mul_distrib]
    _ = ((∏ e ∈ P, (1 + g e)) *
          ∏ e ∈ Finset.univ \ P, (1 + g e)) *
          ∏ e ∈ P, (g e / (1 + g e)) := by ac_rfl
    _ = (∏ e : E, (1 + g e)) * ∏ e ∈ P, (g e / (1 + g e)) := by
          rw [← Finset.prod_sdiff (Finset.subset_univ P)]
          ac_rfl

/-- The path factor in the connected-subset union bound is the full bond
product times the path's normalized edge ratios. -/
theorem prod_path_and_complement_eq_total_mul_ratio
    {E : Type*} [DecidableEq E] [Fintype E]
    (g : E → ℝ) (P : Finset E) (hden : ∀ e, 1 + g e ≠ 0) :
    (∏ e ∈ P, g e) * ∏ e ∈ Finset.univ \ P, (1 + g e) =
      (∏ e : E, (1 + g e)) * ∏ e ∈ P, g e / (1 + g e) := by
  calc
    (∏ e ∈ P, g e) * ∏ e ∈ Finset.univ \ P, (1 + g e) =
        (∑ A ∈ (Finset.univ : Finset E).powerset,
          if P ⊆ A then ∏ e ∈ A, g e else 0) := by
            symm
            exact sum_prod_supersets_eq (R := ℝ) g P (Finset.subset_univ P)
    _ = (∏ e : E, (1 + g e)) * ∏ e ∈ P, g e / (1 + g e) :=
      sum_prod_supersets_eq_total_mul_ratio g P hden

/-- A uniform edge-ratio bound gives a path-length power. -/
theorem prod_bondRatio_le_pow
    {E : Type*} [DecidableEq E] (g : E → ℝ) (P : Finset E) (p : ℝ)
    (hg : ∀ e, 0 ≤ g e) (hden : ∀ e, 0 < 1 + g e)
    (hratio : ∀ e, g e / (1 + g e) ≤ p) :
    (∏ e ∈ P, g e / (1 + g e)) ≤ p ^ P.card := by
  calc
    (∏ e ∈ P, g e / (1 + g e)) ≤ ∏ _e ∈ P, p := by
      apply Finset.prod_le_prod₀
      · intro e he
        exact div_nonneg (hg e) (hden e).le
      · intro e he
        exact hratio e
    _ = p ^ P.card := by simp

end FroehlichSpencer.BKT.Clock.HighTemp

end
