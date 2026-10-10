/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Finite weighted contour removal

An injective encoding of configurations containing a fixed contour by a removed configuration
and a finite contour label gives a Peierls bound. The hypotheses are the concrete injection,
label-cardinality estimate, nonnegative weights, and pointwise energy comparison.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace FroehlichSpencer.BKT.Clock.Peierls

/-- A finite injective contour-removal encoding gives the weighted Peierls inequality.

`A` is the set of configurations containing the contour, `k` is its size, and `remove` records
both the removed configuration and the finite contour label needed to recover the original one.
The label-cardinality and pointwise weight assumptions imply that the total weight on `A` is at
most the Peierls activity to the `k`th power times the full partition function.
-/
theorem weightedContourRemoval
    {Config Label : Type*} [Fintype Config] [Fintype Label]
    (n k : ℕ) (β κ : ℝ) (W : Config → ℝ) (A : Finset Config)
    (remove : {σ : Config // σ ∈ A} → Config × Label)
    (hremove_injective : Function.Injective remove)
    (hweight : ∀ σ : {σ : Config // σ ∈ A},
      W σ.1 ≤ Real.exp (-(β * κ) * (k : ℝ)) * W (remove σ).1)
    (hW_nonneg : ∀ σ, 0 ≤ W σ)
    (hlabels : (Fintype.card Label : ℝ) ≤ ((n : ℝ) - 1) ^ k) :
    (∑ σ : {σ : Config // σ ∈ A}, W σ.1) ≤
      (((n : ℝ) - 1) * Real.exp (-(β * κ))) ^ k * ∑ σ : Config, W σ := by
  classical
  let Containing := {σ : Config // σ ∈ A}
  have himage_sum :
      (∑ σ : Containing, W (remove σ).1) =
        ∑ p ∈ (Finset.univ.image remove), W p.1 := by
    apply Finset.sum_bij (fun σ _ => remove σ)
    · intro σ hσ
      exact Finset.mem_image_of_mem _ hσ
    · intro σ hσ τ hτ hEq
      exact hremove_injective hEq
    · intro p hp
      rcases Finset.mem_image.mp hp with ⟨σ, hσ, rfl⟩
      exact ⟨σ, hσ, rfl⟩
    · intro σ hσ
      rfl
  have hproduct_sum :
      (∑ p : Config × Label, W p.1) =
        (Fintype.card Label : ℝ) * ∑ σ : Config, W σ := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum]
  have hremoved_sum :
      (∑ σ : Containing, W (remove σ).1) ≤
        (Fintype.card Label : ℝ) * ∑ σ : Config, W σ := by
    calc
      (∑ σ : Containing, W (remove σ).1) =
          ∑ p ∈ (Finset.univ.image remove), W p.1 := himage_sum
      _ ≤ ∑ p : Config × Label, W p.1 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro p hp hnot
        exact hW_nonneg p.1
      _ = (Fintype.card Label : ℝ) * ∑ σ : Config, W σ := hproduct_sum
  have hpartition_nonneg : 0 ≤ ∑ σ : Config, W σ := by
    apply Finset.sum_nonneg
    intro σ hσ
    exact hW_nonneg σ
  have hremoved_bound :
      (∑ σ : Containing, W (remove σ).1) ≤
        ((n : ℝ) - 1) ^ k * ∑ σ : Config, W σ := by
    exact le_trans hremoved_sum (mul_le_mul_of_nonneg_right hlabels hpartition_nonneg)
  have hexp : Real.exp (-(β * κ) * (k : ℝ)) = Real.exp (-(β * κ)) ^ k := by
    rw [show -(β * κ) * (k : ℝ) = (k : ℝ) * (-(β * κ)) by ring,
      Real.exp_nat_mul]
  have hactivity :
      Real.exp (-(β * κ) * (k : ℝ)) * ((n : ℝ) - 1) ^ k =
        (((n : ℝ) - 1) * Real.exp (-(β * κ))) ^ k := by
    rw [hexp, ← mul_pow]
    ring
  calc
    (∑ σ : Containing, W σ.1) ≤
        Real.exp (-(β * κ) * (k : ℝ)) * ∑ σ : Containing, W (remove σ).1 := by
      calc
        (∑ σ ∈ (Finset.univ : Finset Containing), W σ.1) ≤
            ∑ σ ∈ (Finset.univ : Finset Containing),
              Real.exp (-(β * κ) * (k : ℝ)) * W (remove σ).1 := by
          apply Finset.sum_le_sum
          intro σ hσ
          exact hweight σ
        _ = Real.exp (-(β * κ) * (k : ℝ)) *
            ∑ σ ∈ (Finset.univ : Finset Containing), W (remove σ).1 := by
          rw [Finset.mul_sum]
    _ ≤ Real.exp (-(β * κ) * (k : ℝ)) *
        (((n : ℝ) - 1) ^ k * ∑ σ : Config, W σ) :=
      mul_le_mul_of_nonneg_left hremoved_bound (Real.exp_nonneg _)
    _ = (((n : ℝ) - 1) * Real.exp (-(β * κ))) ^ k *
        ∑ σ : Config, W σ := by
      rw [← mul_assoc, hactivity]

end FroehlichSpencer.BKT.Clock.Peierls

end
