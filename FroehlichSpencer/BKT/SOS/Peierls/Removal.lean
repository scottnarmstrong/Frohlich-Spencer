/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Peierls.GenericGradient
public import FroehlichSpencer.BKT.Clock.Peierls.FieldSplittingSquare
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Fin

/-! # Countable weighted removal for SOS contours

This module records the countable-sum form of contour removal.  A removal encoding is an
injection from the configurations containing a fixed contour into a removed configuration and a
label.  The energy identity turns the original weight into the removed weight times the label
activity; injectivity then bounds the restricted sum by the full partition function times the
total label activity.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace FroehlichSpencer.BKT.SOS.Peierls

/-- A countable weighted removal encoding bounds the total weight of configurations in an event.

`factor` is the exact energy factorization after removing the contour.  The lemma itself is purely
an injection argument and is stated for `ENNReal`, so it does not need prior summability of either
side.
-/
theorem weightedContourRemoval_tsum
    {Config Label : Type*} (A : Set Config) (W : Config → ENNReal)
    (activity : Label → ENNReal)
    (remove : A → Config × Label) (hremove : Function.Injective remove)
    (term : A → ENNReal)
    (factor : ∀ n, term n = W (remove n).1 * activity (remove n).2) :
    (∑' n : A, term n) ≤ (∑' c : Config, W c) * (∑' d : Label, activity d) := by
  calc
    (∑' n : A, term n) =
        ∑' n : A, W (remove n).1 * activity (remove n).2 := by
      apply tsum_congr
      exact factor
    _ ≤ ∑' p : Config × Label, W p.1 * activity p.2 :=
      ENNReal.tsum_comp_le_tsum_of_injective hremove
        (fun p : Config × Label => W p.1 * activity p.2)
    _ = (∑' c : Config, W c) * (∑' d : Label, activity d) := by
      calc
        (∑' p : Config × Label, W p.1 * activity p.2) =
            ∑' c : Config, ∑' d : Label, W c * activity d :=
          ENNReal.tsum_prod (f := fun c d => W c * activity d)
        _ = ∑' c : Config, W c * ∑' d : Label, activity d := by
          apply tsum_congr
          intro c
          exact ENNReal.tsum_mul_left
        _ = (∑' c : Config, W c) * (∑' d : Label, activity d) :=
          ENNReal.tsum_mul_right

/-- The label space for a contour records one nonzero integer on each of its edges. -/
abbrev IntegerContourLabel {Edge : Type*} (Γ : Finset Edge) :=
  ({x : Edge // x ∈ Γ} → {d : ℤ // d ≠ 0})

/-- Product activity of an integer contour label.  The per-edge activity may already include both
the observable factor and the Boltzmann factor. -/
def integerContourLabelActivity {Edge : Type*} (Γ : Finset Edge)
    (inst : Fintype {x : Edge // x ∈ Γ})
    (a : {d : ℤ // d ≠ 0} → ENNReal) (label : IntegerContourLabel Γ) : ENNReal :=
  @Finset.prod {x : Edge // x ∈ Γ} ENNReal inferInstance
    (@Finset.univ {x : Edge // x ∈ Γ} inst) (fun edge => a (label edge))

/-- If an integer contour removal has an injective encoding and its weight factors over the
removed configuration and the recorded edge labels, then the contour-restricted sum is bounded by
the partition sum times the product label sum. -/
theorem integerContourRemoval_tsum
    {Config Edge : Type*} (Γ : Finset Edge) (inst : Fintype {x : Edge // x ∈ Γ})
    (A : Set Config)
    (W : Config → ENNReal) (a : {d : ℤ // d ≠ 0} → ENNReal)
    (remove : A → Config × IntegerContourLabel Γ)
    (hremove : Function.Injective remove)
    (term : A → ENNReal)
    (factor : ∀ n, term n =
      W (remove n).1 * integerContourLabelActivity Γ inst a (remove n).2) :
    (∑' n : A, term n) ≤
      (∑' c : Config, W c) *
        (∑' label : IntegerContourLabel Γ, integerContourLabelActivity Γ inst a label) := by
  exact weightedContourRemoval_tsum A W (integerContourLabelActivity Γ inst a) remove hremove term factor

/-- Product activity summed over labels on an `n`-edge set is the `n`th power of the one-edge
activity sum. -/
theorem tsum_fin_pi_prod_eq_pow (D : Type*) (q : D → ENNReal) :
    ∀ n : ℕ, (∑' f : Fin n → D, ∏ i, q (f i)) = (∑' d, q d) ^ n := by
  intro n
  induction n with
  | zero =>
      let f₀ : Fin 0 → D := Fin.elim0
      rw [tsum_eq_single f₀]
      · simp [f₀]
      · intro f hf
        exact False.elim (hf (Subsingleton.elim _ _))
  | succ n ih =>
      let E : (Fin (n + 1) → D) ≃ D × (Fin n → D) :=
        (Fin.consEquiv (fun _ : Fin (n + 1) => D)).symm
      have hprod (f : Fin (n + 1) → D) :
          (∏ i : Fin (n + 1), q (f i)) = q (f 0) * ∏ i : Fin n, q (f i.succ) := by
        rw [Fin.prod_univ_succ]
      calc
        (∑' f : Fin (n + 1) → D, ∏ i, q (f i)) =
            ∑' f : Fin (n + 1) → D, q (f 0) * ∏ i : Fin n, q (f i.succ) := by
          apply tsum_congr
          exact hprod
        _ = ∑' p : D × (Fin n → D), q p.1 * ∏ i : Fin n, q (p.2 i) := by
          simpa [E, Fin.consEquiv, Fin.tail] using
            E.tsum_eq (fun p : D × (Fin n → D) => q p.1 * ∏ i : Fin n, q (p.2 i))
        _ = (∑' d, q d) * (∑' f : Fin n → D, ∏ i, q (f i)) := by
          calc
            _ = ∑' d : D, ∑' f : Fin n → D, q d * ∏ i : Fin n, q (f i) :=
              ENNReal.tsum_prod (f := fun d : D => fun f : Fin n → D => q d * ∏ i : Fin n, q (f i))
            _ = ∑' d : D, q d * ∑' f : Fin n → D, ∏ i : Fin n, q (f i) := by
              apply tsum_congr
              intro d
              exact ENNReal.tsum_mul_left
            _ = _ := ENNReal.tsum_mul_right
        _ = (∑' d, q d) ^ (n + 1) := by
          rw [ih, pow_succ, mul_comm]

/-- The same product-activity factorization for any finite edge carrier. -/
theorem tsum_pi_prod_eq_pow {D α : Type*} (q : D → ENNReal) [Fintype α] :
    (∑' f : α → D, ∏ i, q (f i)) = (∑' d, q d) ^ Fintype.card α := by
  classical
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let E : (α → D) ≃ (Fin (Fintype.card α) → D) :=
    Equiv.arrowCongr e (Equiv.refl D)
  have hprod (f : α → D) :
      (∏ i : α, q (f i)) = ∏ j : Fin (Fintype.card α), q (E f j) := by
    exact Fintype.prod_equiv e (fun i => q (f i)) (fun j => q (E f j)) (by
      intro i
      simp [E])
  calc
    (∑' f : α → D, ∏ i, q (f i)) =
        ∑' f : α → D, ∏ j : Fin (Fintype.card α), q (E f j) := by
      apply tsum_congr
      exact hprod
    _ = ∑' f : Fin (Fintype.card α) → D, ∏ j, q (f j) :=
      E.tsum_eq (fun f : Fin (Fintype.card α) → D => ∏ j, q (f j))
    _ = (∑' d, q d) ^ Fintype.card α := tsum_fin_pi_prod_eq_pow D q _

/-- Sum of a product edge activity over all labels on a finite contour factors as the corresponding
one-edge sum raised to the contour size. -/
theorem tsum_integerContourLabelActivity_eq_pow {Edge : Type*} (Γ : Finset Edge)
    (inst : Fintype {x : Edge // x ∈ Γ})
    (a : {d : ℤ // d ≠ 0} → ENNReal) :
    (∑' label : IntegerContourLabel Γ, integerContourLabelActivity Γ inst a label) =
      (∑' d : {d : ℤ // d ≠ 0}, a d) ^ Γ.card := by
  classical
  simpa [integerContourLabelActivity, @Fintype.card_coe Edge Γ inst] using
    @tsum_pi_prod_eq_pow {d : ℤ // d ≠ 0} {x : Edge // x ∈ Γ} a inst

/-- The countable contour-removal estimate in its factored form, with the label sum replaced by
the one-edge activity raised to the contour cardinality. -/
theorem integerContourRemoval_tsum_pow
    {Config Edge : Type*} (Γ : Finset Edge) (inst : Fintype {x : Edge // x ∈ Γ})
    (A : Set Config)
    (W : Config → ENNReal) (a : {d : ℤ // d ≠ 0} → ENNReal)
    (remove : A → Config × IntegerContourLabel Γ)
    (hremove : Function.Injective remove)
    (term : A → ENNReal)
    (factor : ∀ n, term n =
      W (remove n).1 * integerContourLabelActivity Γ inst a (remove n).2) :
    (∑' n : A, term n) ≤
      (∑' c : Config, W c) * (∑' d : {d : ℤ // d ≠ 0}, a d) ^ Γ.card := by
  rw [← tsum_integerContourLabelActivity_eq_pow Γ inst a]
  exact integerContourRemoval_tsum Γ inst A W a remove hremove term factor

end FroehlichSpencer.BKT.SOS.Peierls

end
