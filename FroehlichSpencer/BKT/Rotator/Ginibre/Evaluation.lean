/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Ginibre.Algebra
public import FroehlichSpencer.BKT.Rotator.Ginibre.Measure
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Evaluating duplicated trigonometric polynomials

The basis element `(p, q)` of the duplicated algebra evaluates to `exp(i(p·θ + q·θ'))` on two
angle configurations. Character orthogonality on `[-π, π)^V` integrates an evaluated polynomial
against the doubled raw angle measure to `(2π)^{2|V|}` times its constant coefficient.
-/

@[expose] public section

open AddMonoidAlgebra MeasureTheory
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Ginibre

variable {V : Type*} [Fintype V]

/-- The phase `m·θ = Σ_x m_x θ_x` of an integer frequency vector. -/
def phase (m : Frequency V) (θ : V → ℝ) : ℝ :=
  ∑ x, (m x : ℝ) * θ x

/-- The character `exp(i m·θ)`, written as a product over the sites. -/
def character (m : Frequency V) (θ : V → ℝ) : ℂ :=
  ∏ x, Complex.exp (Complex.I * (m x : ℂ) * (θ x : ℂ))

theorem character_eq_exp (m : Frequency V) (θ : V → ℝ) :
    character m θ = Complex.exp ((phase m θ : ℂ) * Complex.I) := by
  rw [character, phase, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem phase_neg (m : Frequency V) (θ : V → ℝ) : phase (-m) θ = -phase m θ := by
  simp [phase, Finset.sum_neg_distrib]

theorem character_zero (θ : V → ℝ) : character (0 : Frequency V) θ = 1 := by
  simp [character]

theorem character_add (m n : Frequency V) (θ : V → ℝ) :
    character (m + n) θ = character m θ * character n θ := by
  simp only [character, ← Finset.prod_mul_distrib, ← Complex.exp_add]
  refine Finset.prod_congr rfl fun x _ => ?_
  congr 1
  rw [Pi.add_apply]
  push_cast
  ring

theorem norm_character (m : Frequency V) (θ : V → ℝ) : ‖character m θ‖ = 1 := by
  rw [character_eq_exp, Complex.norm_exp_ofReal_mul_I]

theorem continuous_character (m : Frequency V) : Continuous (character m) := by
  unfold character
  fun_prop

/-- The characters of duplicated frequencies, as a monoid homomorphism into functions of two angle
configurations. -/
def dupCharacter (V : Type*) [Fintype V] :
    Multiplicative (Frequency V × Frequency V) →* ((V → ℝ) × (V → ℝ) → ℂ) where
  toFun g z := character g.toAdd.1 z.1 * character g.toAdd.2 z.2
  map_one' := by
    funext z
    simp [character_zero]
  map_mul' a b := by
    funext z
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, character_add, Pi.mul_apply]
    ring

/-- Evaluation of duplicated formal polynomials as functions of `(θ, θ')`. -/
def dupEval (V : Type*) [Fintype V] :
    DupTrigAlgebra V →ₐ[ℝ] ((V → ℝ) × (V → ℝ) → ℂ) :=
  AddMonoidAlgebra.lift ℝ _ _ (dupCharacter V)

theorem dupEval_single (g : Frequency V × Frequency V) (r : ℝ) (z : (V → ℝ) × (V → ℝ)) :
    dupEval V (single g r) z = (r : ℂ) * (character g.1 z.1 * character g.2 z.2) := by
  rw [dupEval, lift_single, Pi.smul_apply, Complex.real_smul]
  rfl

theorem dupEval_cosPair (m : Frequency V) (σ : ℝ) (z : (V → ℝ) × (V → ℝ)) :
    dupEval V (cosPair m σ) z =
      ((Real.cos (phase m z.1) + σ * Real.cos (phase m z.2) : ℝ) : ℂ) := by
  simp only [cosPair, map_add, Pi.add_apply, dupEval_single, character_zero, mul_one, one_mul]
  simp only [character_eq_exp, phase_neg]
  push_cast
  rw [Complex.cos, Complex.cos]
  ring_nf

theorem continuous_dupEval (P : DupTrigAlgebra V) : Continuous (dupEval V P) := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero =>
      rw [map_zero]
      exact continuous_const
  | add P Q hP hQ =>
      rw [map_add]
      exact hP.add hQ
  | single g r =>
      have h : dupEval V (single g r) =
          fun z => (r : ℂ) * (character g.1 z.1 * character g.2 z.2) :=
        funext (dupEval_single g r)
      rw [h]
      have h₁ := continuous_character g.1
      have h₂ := continuous_character g.2
      fun_prop

theorem exists_norm_dupEval_le (P : DupTrigAlgebra V) :
    ∃ C, ∀ z, ‖dupEval V P z‖ ≤ C := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, fun z => by simp⟩
  | add P Q hP hQ =>
      obtain ⟨C₁, h₁⟩ := hP
      obtain ⟨C₂, h₂⟩ := hQ
      refine ⟨C₁ + C₂, fun z => ?_⟩
      rw [map_add, Pi.add_apply]
      exact (norm_add_le _ _).trans (add_le_add (h₁ z) (h₂ z))
  | single g r =>
      refine ⟨|r|, fun z => ?_⟩
      rw [dupEval_single, norm_mul, norm_mul, norm_character, norm_character,
        Complex.norm_real, Real.norm_eq_abs, mul_one, mul_one]

variable [DecidableEq V]

theorem integrable_dupEval (P : DupTrigAlgebra V) :
    Integrable (dupEval V P) ((rotatorRawAngleMeasure V).prod (rotatorRawAngleMeasure V)) := by
  obtain ⟨C, hC⟩ := exists_norm_dupEval_le P
  exact Integrable.of_bound (continuous_dupEval P).aestronglyMeasurable C (ae_of_all _ hC)

theorem integral_character (m : Frequency V) :
    ∫ θ, character m θ ∂rotatorRawAngleMeasure V =
      if m = 0 then (2 * π : ℂ) ^ Fintype.card V else 0 :=
  FroehlichSpencer.BKT.integral_product_character_Ico m

/-- Character orthogonality for duplicated polynomials: the integral of the evaluation is
`(2π)^{2|V|}` times the constant coefficient. -/
theorem integral_dupEval (P : DupTrigAlgebra V) :
    ∫ z, dupEval V P z ∂(rotatorRawAngleMeasure V).prod (rotatorRawAngleMeasure V) =
      (((2 * π) ^ (2 * Fintype.card V) * P.coeff 0 : ℝ) : ℂ) := by
  classical
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ =>
      simp only [map_add, Pi.add_apply]
      rw [integral_add (integrable_dupEval P) (integrable_dupEval Q), hP, hQ,
        coeff_add, Finsupp.add_apply]
      push_cast
      ring
  | single g r =>
      simp_rw [dupEval_single]
      rw [integral_const_mul, integral_prod_mul (fun θ => character g.1 θ)
        (fun θ => character g.2 θ), integral_character, integral_character, coeff_single,
        Finsupp.single_apply]
      obtain ⟨p, q⟩ := g
      by_cases hp : p = 0 <;> by_cases hq : q = 0
      · subst hp hq
        simp only [ite_true, Prod.mk_zero_zero]
        push_cast
        ring
      · simp [hp, hq]
      · simp [hp, hq]
      · simp [hp, hq]

end FroehlichSpencer.BKT.Rotator.Ginibre

end
