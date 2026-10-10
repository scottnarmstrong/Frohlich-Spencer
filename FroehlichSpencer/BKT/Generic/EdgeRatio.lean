/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The edge ratio of a complex translation (generic core)

`R_b(x) = ∏_e w(x_e + i b_e) / w(x_e)`,  with `x = ∇φ` and `b = ∇a`.

This module records the algebra of `R_b` that the generic translation step
(`Generic/ProductTranslation.lean`) needs: `R_0 = 1`, and `R` is multiplicative over shifts with
pairwise disjoint supports.

The second fact is FS81 (6.20) in the form used by KP §2.3.3: spin
waves of distinct densities have disjoint gradient supports, so the joint translation factors
into one ratio per density.

Both need only that `w` does not vanish at the real points `x_e`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open Complex

variable {E : Type*} [Fintype E]

/-- FS81 (4.38)/(6.4): the edge ratio `R_b(x) = ∏_e w(x_e + i b_e) / w(x_e)`. -/
def edgeRatio (w : ℂ → ℂ) (b x : E → ℝ) : ℂ :=
  ∏ e, w ((x e : ℂ) + (b e : ℂ) * I) / w (x e)

omit [Fintype E] in
/-- An edge with zero shift contributes the factor one. -/
lemma edgeRatio_factor_of_eq_zero (w : ℂ → ℂ) {b x : E → ℝ} {e : E} (hb : b e = 0)
    (hw : w (x e) ≠ 0) : w ((x e : ℂ) + (b e : ℂ) * I) / w (x e) = 1 := by
  rw [hb, Complex.ofReal_zero, zero_mul, add_zero, div_self hw]

/-- `R_0 = 1`. -/
theorem edgeRatio_zero (w : ℂ → ℂ) (x : E → ℝ) (hw : ∀ e, w (x e) ≠ 0) :
    edgeRatio w 0 x = 1 :=
  Finset.prod_eq_one fun e _ => edgeRatio_factor_of_eq_zero w (Pi.zero_apply e) (hw e)

/-- `R_{b₁ + b₂} = R_{b₁} R_{b₂}` when no edge carries both shifts. -/
theorem edgeRatio_add (w : ℂ → ℂ) (b₁ b₂ x : E → ℝ) (hw : ∀ e, w (x e) ≠ 0)
    (hdisj : ∀ e, b₁ e = 0 ∨ b₂ e = 0) :
    edgeRatio w (b₁ + b₂) x = edgeRatio w b₁ x * edgeRatio w b₂ x := by
  unfold edgeRatio
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  rcases hdisj e with h | h
  · rw [edgeRatio_factor_of_eq_zero w h (hw e), one_mul, Pi.add_apply, h, zero_add]
  · rw [edgeRatio_factor_of_eq_zero w h (hw e), mul_one, Pi.add_apply, h, add_zero]

/-- `R_{∑_{i ∈ s} b_i} = ∏_{i ∈ s} R_{b_i}` for shifts with pairwise disjoint supports. -/
theorem edgeRatio_sum {ι : Type*} (s : Finset ι) (w : ℂ → ℂ) (b : ι → E → ℝ) (x : E → ℝ)
    (hw : ∀ e, w (x e) ≠ 0)
    (hdisj : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → ∀ e, b i e = 0 ∨ b i' e = 0) :
    edgeRatio w (∑ i ∈ s, b i) x = ∏ i ∈ s, edgeRatio w (b i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, edgeRatio_zero w x hw]
  | insert i₀ s hi₀ ih =>
    rw [Finset.sum_insert hi₀, Finset.prod_insert hi₀, edgeRatio_add w _ _ x hw, ih fun i hi i' hi' =>
      hdisj i (Finset.mem_insert_of_mem hi) i' (Finset.mem_insert_of_mem hi')]
    intro e
    by_cases h : b i₀ e = 0
    · exact Or.inl h
    · refine Or.inr ?_
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hne : i₀ ≠ i := fun h' => hi₀ (h' ▸ hi)
      exact (hdisj i₀ (Finset.mem_insert_self i₀ s) i (Finset.mem_insert_of_mem hi) hne e).resolve_left h

end FroehlichSpencer.BKT.Generic

end
