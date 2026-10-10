/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Products of factor comparisons (generic core)
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

/-- Multiplying per-factor exponential comparisons. -/
theorem prod_mul_exp_le_prod {ι : Type*} (s : Finset ι) (u₀ u₁ d r : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < u₀ i) (h : ∀ i ∈ s, u₀ i * Real.exp (d i / u₀ i - r i) ≤ u₁ i) :
    (∏ i ∈ s, u₀ i) * Real.exp (∑ i ∈ s, d i / u₀ i - ∑ i ∈ s, r i) ≤ ∏ i ∈ s, u₁ i := by
  rw [← Finset.sum_sub_distrib, Real.exp_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀ (fun i hi => mul_nonneg (hpos i hi).le (Real.exp_pos _).le) h

end FroehlichSpencer.BKT.Generic

end
