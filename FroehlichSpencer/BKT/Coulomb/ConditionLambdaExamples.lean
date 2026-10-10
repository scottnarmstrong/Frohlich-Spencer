/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.ConditionLambdaLimit
public import FroehlichSpencer.BKT.Rotator.BesselInterp.CoeffBound
import Mathlib.Tactic

/-!
# FS81's example gases are Condition-λ gases

* hard core (1.10): `conditionLambda_hardCore` (`Coulomb/ConditionLambdaFree.lean`), with
  `C = max 1 (e^α/2)`, `ε = 1/17` on FS81 Theorem 5.1's activity range;
* the **standard gas** (1.11), `λ(q) = I_q(z)`, normalized by `I_0(z) > 0`
  (`standardWeightInternal`; normalization does not change expectations,
  `fullGasExpectation_standard`): `conditionLambda_standard`, `C = 1`, `α = ε = 0` for **every**
  `z ≥ 0` (`|I_q(z)| ≤ I_0(z)`, `besselCoeffRe_le_zero`; Bessel coefficients from
  `Rotator/BesselInterp`);
* the **Villain gas** (1.12), `λ ≡ 1`: `conditionLambda_villain`, `C = 1`, `α = ε = 0`.

`standard_villain_bounds`: FS81 Theorems 5.1 and A (free b.c., every finite `Λ`) and Theorem A in
infinite volume hold for the standard and Villain gases with one threshold `κ₀(δ)`, uniformly in
the activity `z`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open Filter Topology
open FroehlichSpencer.BKT.Rotator.BesselInterp

/-! ### FS81 Examples 2 and 3 (J p. 530) -/

/-- `I_q(z) ≤ I_0(z)`. -/
theorem besselCoeffRe_le_zero (z : ℝ) (n : ℤ) : besselCoeffRe z n ≤ besselCoeffRe z 0 := by
  unfold besselCoeffRe
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine intervalIntegral.integral_mono_on (by positivity)
    ((by fun_prop : Continuous fun θ : ℝ => Real.exp (z * Real.cos θ) * Real.cos (n * θ)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun θ : ℝ => Real.exp (z * Real.cos θ) * Real.cos ((0 : ℤ) * θ)).intervalIntegrable _ _)
    fun θ _ => ?_
  simp only [Int.cast_zero, zero_mul, Real.cos_zero, mul_one]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.cos_le_one _)

/-- `I_0(z) > 0` for every real `z`. -/
theorem besselCoeffRe_zero_pos (z : ℝ) : 0 < besselCoeffRe z 0 := by
  unfold besselCoeffRe
  refine mul_pos (by positivity) (intervalIntegral.intervalIntegral_pos_of_pos_on
    ((by fun_prop : Continuous fun θ : ℝ =>
      Real.exp (z * Real.cos θ) * Real.cos ((0 : ℤ) * θ)).intervalIntegrable _ _)
    (fun θ _ => ?_) (by positivity))
  simp only [Int.cast_zero, zero_mul, Real.cos_zero, mul_one]
  exact Real.exp_pos _

/-- FS81 (1.11), the **standard gas**, normalized to vacancy weight one:
`λ(q) = I_q(z) / I_0(z)` with `I_q(z) = (2π)⁻¹ ∫₀^{2π} e^{z cos θ} cos (q θ) dθ`. -/
def standardWeightInternal (z : ℝ) (q : ℤ) : ℝ :=
  besselCoeffRe z q / besselCoeffRe z 0

/-- The standard gas satisfies Condition λ with `C = 1`, `α = ε = 0` for **every** activity
`z ≥ 0` and every `κ`, and is physical. -/
theorem conditionLambda_standard {z : ℝ} (hz : 0 ≤ z) (κ : ℝ) :
    ConditionLambdaInternal 1 0 0 κ (standardWeightInternal z) ∧
      PhysicalWeightInternal (standardWeightInternal z) := by
  have h0 := besselCoeffRe_zero_pos z
  refine ⟨⟨fun n => by simp only [standardWeightInternal, besselCoeffRe_neg], fun n => ?_⟩,
    div_self h0.ne', fun n => div_nonneg (besselCoeffRe_nonneg hz n) h0.le⟩
  simp only [zero_mul, add_zero, Real.exp_zero, mul_one, standardWeightInternal]
  rw [abs_div, abs_of_pos h0, abs_of_nonneg (besselCoeffRe_nonneg hz n), div_le_one h0]
  exact besselCoeffRe_le_zero z n

/-- FS81 (1.12), the **Villain gas** `λ ≡ 1`, satisfies Condition λ with `C = 1`, `α = ε = 0` and
is physical. -/
theorem conditionLambda_villain (κ : ℝ) :
    ConditionLambdaInternal 1 0 0 κ (fun _ => 1) ∧ PhysicalWeightInternal (fun _ => 1) :=
  ⟨⟨fun _ => rfl, fun n => by simp⟩, rfl, fun _ => zero_le_one⟩

/-- FS81's unnormalized standard gas `λ(q) = I_q(z)` has the same expectations as the normalized
one . -/
theorem fullGasExpectation_standard {V : Type*} [Fintype V] (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ z : ℝ)
    (F : (V → ℤ) → ℝ) :
    fullGasExpectationInternal T κ (fun _ => standardWeightInternal z) F =
      fullGasExpectationInternal T κ (fun _ q => besselCoeffRe z q) F := by
  have h0 := (besselCoeffRe_zero_pos z).ne'
  have hfun : (fun (_ : V) q => standardWeightInternal z q) =
      fun j q => (fun _ : V => (besselCoeffRe z 0)⁻¹) j * besselCoeffRe z q := by
    funext j q
    simp only [standardWeightInternal, div_eq_inv_mul]
  rw [hfun, fullGasExpectation_smul]
  rw [Finset.prod_const]
  exact pow_ne_zero _ (inv_ne_zero h0)

/-- **FS81 Theorems 5.1 and A for the standard and Villain gases, uniformly in the activity**
(free b.c., every finite `Λ ⊂ ℤ²`, and infinite volume): for `0 < δ ≤ 1` there is `κ₀` such that
for `κ > κ₀` and every weight `λ` that is the Villain weight or a standard-gas weight with
`z ≥ 0`, `free_conditionLambda_physical` and `conditionLambda_thermodynamic_limit` apply with the
same `κ₀`. -/
theorem standard_villain_bounds (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ FreeConditionLambdaBoundInternal δ 1 0 0 κ₀ ∧
      ∀ κ : ℝ, κ₀ < κ → ∀ lam : ℤ → ℝ,
        (lam = (fun _ => 1) ∨ ∃ z, 0 ≤ z ∧ lam = standardWeightInternal z) →
        ConditionLambdaInternal 1 0 0 κ lam ∧ PhysicalWeightInternal lam ∧
        (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Γ : ℤ × ℤ → ℤ × ℤ → ℝ,
          ∀ x y, Tendsto (fun k => lambdaFieldCorrelationInternal κ lam (φ k) x y) atTop
            (𝓝 (Γ x y))) ∧
        (∀ φ : ℕ → ℕ, StrictMono φ → ∀ Γ : ℤ × ℤ → ℤ × ℤ → ℝ,
          (∀ x y, Tendsto (fun k => lambdaFieldCorrelationInternal κ lam (φ k) x y) atTop
            (𝓝 (Γ x y))) →
          ∀ (R : ℕ) (f : ℤ × ℤ → ℝ), SupportedInBox R f → ∑ x ∈ boxInternal R, f x = 0 →
            (1 - δ) * κ * wholePlaneQuadInternal R f ≤
              ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, f x * f y * Γ x y ∧
            ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, f x * f y * Γ x y ≤
              κ * wholePlaneQuadInternal R f) := by
  obtain ⟨κ₁, hκ₁, h1⟩ := free_conditionLambda_bound δ hδ 1 0 0 (by norm_num)
  obtain ⟨κ₂, hκ₂, h2⟩ := conditionLambda_thermodynamic_limit δ hδ hδ1 1 0 0 (by norm_num)
  have hmono : ∀ {κ₀ κ₀'}, κ₀ ≤ κ₀' → FreeConditionLambdaBoundInternal δ 1 0 0 κ₀ →
      FreeConditionLambdaBoundInternal δ 1 0 0 κ₀' :=
    fun hle h Λ κ hκ => h Λ κ (hle.trans_lt hκ)
  refine ⟨max κ₁ κ₂, lt_max_of_lt_left hκ₁, hmono (le_max_left _ _) h1,
    fun κ hκ lam hlam => ?_⟩
  have hcl : ConditionLambdaInternal 1 0 0 κ lam ∧ PhysicalWeightInternal lam := by
    rcases hlam with rfl | ⟨z, hz, rfl⟩
    · exact conditionLambda_villain κ
    · exact conditionLambda_standard hz κ
  exact ⟨hcl.1, hcl.2, h2 κ ((le_max_right _ _).trans_lt hκ) lam hcl.1 hcl.2⟩

end FroehlichSpencer.BKT.Coulomb
