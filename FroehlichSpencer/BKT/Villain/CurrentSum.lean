/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.BigOperators
public import FroehlichSpencer.BKT.Fourier.PeriodizedGaussian

/-!
# Products of edge Fourier sums

Absolutely summable edge coefficients factor over a finite edge type. This identifies the product
of one-edge Fourier series with the single series indexed by integer currents, as required in the
finite Villain expansion (KP §6.1, p. 33).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Villain

universe u

private theorem prod_option_of_fintype {α M : Type*} [Fintype α] [Fintype (Option α)]
    [CommMonoid M] (f : Option α → M) :
    ∏ o : Option α, f o = f none * ∏ i : α, f (some i) := by
  classical
  have hUniv :
      (Finset.univ : Finset (Option α)) =
        Finset.insertNone (Finset.univ : Finset α) := by
    ext o
    cases o <;> simp
  calc
    ∏ o : Option α, f o = ∏ o ∈ (Finset.univ : Finset (Option α)), f o := rfl
    _ = ∏ o ∈ Finset.insertNone (Finset.univ : Finset α), f o := by rw [hUniv]
    _ = f none * ∏ i ∈ (Finset.univ : Finset α), f (some i) :=
      Finset.prod_insertNone f _
    _ = f none * ∏ i : α, f (some i) := by simp

/-- The product of absolutely summable edge coefficients is absolutely summable over all integer
currents on a finite edge type. -/
theorem summable_norm_prod_currents {E : Type u} [Fintype E]
    (a : E → ℤ → ℂ) (ha : ∀ e, Summable (fun q => ‖a e q‖)) :
    Summable (fun q : E → ℤ => ‖∏ e, a e (q e)‖) := by
  classical
  let P : Type u → Prop := fun E =>
    ∀ [Fintype E] (a : E → ℤ → ℂ),
      (∀ e, Summable (fun q => ‖a e q‖)) →
      Summable (fun q : E → ℤ => ‖∏ e, a e (q e)‖)
  have hP : P E := by
    clear a ha
    induction E using Finite.induction_empty_option with
    | @of_equiv α β e ih =>
        intro _ a ha
        have instα : Fintype α := Fintype.ofEquiv β e.symm
        let a' : α → ℤ → ℂ := fun i q => a (e i) q
        have ha' : ∀ i, Summable (fun q => ‖a' i q‖) := by
          intro i
          exact ha (e i)
        have hα := ih a' ha'
        let eQ : (β → ℤ) ≃ (α → ℤ) :=
          { toFun := fun q i => q (e i)
            invFun := fun q i => q (e.symm i)
            left_inv := by
              intro q
              funext i
              simp
            right_inv := by
              intro q
              funext i
              simp }
        apply (hα.comp_injective eQ.injective).congr
        intro q
        change ‖∏ i : α, a (e i) (q (e i))‖ = ‖∏ j : β, a j (q j)‖
        rw [Fintype.prod_equiv e (fun i => a (e i) (q (e i)))
          (fun j => a j (q j)) (by intro i; rfl)]
    | h_empty =>
        intro _ a ha
        exact Summable.of_finite
    | @h_option α _ ih =>
        intro _ a ha
        let a₀ : ℤ → ℂ := fun q => a none q
        let a' : α → ℤ → ℂ := fun i q => a (some i) q
        let b : (α → ℤ) → ℂ := fun q => ∏ i, a' i (q i)
        have h₀ : Summable (fun q => ‖a₀ q‖) := by
          simpa [a₀] using ha none
        have ha' : ∀ i, Summable (fun q => ‖a' i q‖) := by
          intro i
          exact ha (some i)
        have hα : Summable (fun q : α → ℤ => ‖b q‖) := ih a' ha'
        let eQ : (Option α → ℤ) ≃ (ℤ × (α → ℤ)) :=
          { toFun := fun q => (q none, fun i => q (some i))
            invFun := fun p o => o.elim p.1 p.2
            left_inv := by
              intro q
              funext o
              cases o <;> rfl
            right_inv := by
              rintro ⟨q₀, q⟩
              rfl }
        have hpair :
            Summable (fun p : ℤ × (α → ℤ) =>
              a₀ p.1 * b p.2) :=
          summable_mul_of_summable_norm h₀ hα
        have hpairNorm : Summable (fun p : ℤ × (α → ℤ) =>
              ‖a₀ p.1 * b p.2‖) := hpair.norm
        have hcomp := hpairNorm.comp_injective eQ.injective
        apply hcomp.congr
        intro q
        have hprod :
            ∏ o : Option α, a o (q o) =
              a none (q none) * ∏ i : α, a (some i) (q (some i)) :=
          prod_option_of_fintype (fun o : Option α => a o (q o))
        change ‖a₀ (q none) * b (fun i => q (some i))‖ =
          ‖∏ o : Option α, a o (q o)‖
        rw [hprod]

  exact hP a ha

/-- The product of the edge Fourier sums equals the sum over integer currents. The summability
assumption is stated in absolute-value form, which also supplies summability of the current series.
KP §6.1, p. 33. -/
theorem tsum_prod_currents {E : Type u} [Fintype E]
    (a : E → ℤ → ℂ) (ha : ∀ e, Summable (fun q => ‖a e q‖)) :
    ∏ e, ∑' q, a e q = ∑' q : E → ℤ, ∏ e, a e (q e) := by
  classical
  let P : Type u → Prop := fun E =>
    ∀ [Fintype E] (a : E → ℤ → ℂ),
      (∀ e, Summable (fun q => ‖a e q‖)) →
      ∏ e, ∑' q, a e q = ∑' q : E → ℤ, ∏ e, a e (q e)
  have hP : P E := by
    clear a ha
    induction E using Finite.induction_empty_option with
    | @of_equiv α β e ih =>
        intro _ a ha
        have instα : Fintype α := Fintype.ofEquiv β e.symm
        let a' : α → ℤ → ℂ := fun i q => a (e i) q
        have ha' : ∀ i, Summable (fun q => ‖a' i q‖) := by
          intro i
          exact ha (e i)
        have hα := ih a' ha'
        let eQ : (β → ℤ) ≃ (α → ℤ) :=
          { toFun := fun q i => q (e i)
            invFun := fun q i => q (e.symm i)
            left_inv := by
              intro q
              funext i
              simp
            right_inv := by
              intro q
              funext i
              simp }
        calc
          ∏ j : β, ∑' q, a j q = ∏ i : α, ∑' q, a (e i) q := by
            symm
            exact Fintype.prod_equiv e _ _ fun _ => rfl
          _ = ∑' q : α → ℤ, ∏ i, a' i (q i) := hα
          _ = ∑' q : β → ℤ, ∏ j, a j (q j) := by
            rw [← eQ.tsum_eq (fun q : α → ℤ => ∏ i, a' i (q i))]
            apply tsum_congr
            intro q
            change ∏ i : α, a (e i) (q (e i)) = ∏ j : β, a j (q j)
            exact Fintype.prod_equiv e _ _ (by intro i; rfl)
    | h_empty =>
        intro _ a ha
        simp
    | @h_option α _ ih =>
        intro _ a ha
        let a₀ : ℤ → ℂ := fun q => a none q
        let a' : α → ℤ → ℂ := fun i q => a (some i) q
        let b : (α → ℤ) → ℂ := fun q => ∏ i, a' i (q i)
        have h₀ : Summable (fun q => ‖a₀ q‖) := by
          simpa [a₀] using ha none
        have ha' : ∀ i, Summable (fun q => ‖a' i q‖) := by
          intro i
          exact ha (some i)
        have hα := ih a' ha'
        let eQ : (Option α → ℤ) ≃ (ℤ × (α → ℤ)) :=
          { toFun := fun q => (q none, fun i => q (some i))
            invFun := fun p o => o.elim p.1 p.2
            left_inv := by
              intro q
              funext o
              cases o <;> rfl
            right_inv := by
              rintro ⟨q₀, q⟩
              rfl }
        have hαnorm : Summable (fun q : α → ℤ => ‖b q‖) :=
          summable_norm_prod_currents a' ha'
        calc
          ∏ o : Option α, ∑' q, a o q =
              (∑' q : ℤ, a₀ q) * ∏ i : α, ∑' q, a' i q := by
                simpa [a₀, a'] using
                  (prod_option_of_fintype
                    (fun o : Option α => ∑' q : ℤ, a o q))
          _ = ∑' p : ℤ × (α → ℤ),
                a₀ p.1 * b p.2 := by
              rw [hα]
              exact tsum_mul_tsum_of_summable_norm h₀ hαnorm
          _ = ∑' q : Option α → ℤ, ∏ o, a o (q o) := by
              rw [← eQ.tsum_eq (fun p : ℤ × (α → ℤ) =>
                a₀ p.1 * b p.2)]
              apply tsum_congr
              intro q
              calc
                a₀ (eQ q).1 * b (eQ q).2 =
                    a none (q none) * ∏ i, a (some i) (q (some i)) := by
                  rfl
                _ = ∏ o : Option α, a o (q o) :=
                  (prod_option_of_fintype
                    (fun o : Option α => a o (q o))).symm

  exact hP a ha

end FroehlichSpencer.BKT.Villain

end
