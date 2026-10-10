/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Ginibre.Kernel
public import FroehlichSpencer.BKT.Rotator.Ginibre.Positivity

/-!
# The closed Ginibre cone

A real function of the duplicated angles `(θ, θ')` lies in the closed Ginibre cone when it is the
pointwise limit of uniformly bounded evaluations of elements of Ginibre's (algebraic) cone. The
closed cone contains the cone, is closed under products, and contains `exp S` whenever `S` is the
evaluation of a cone element. By dominated convergence, every element of the closed cone integrates
nonnegatively against `ν^V ⊗ ν'^V` whenever the single-site Fourier coefficients form an
equivalence kernel (`dupFunctional_nonneg`).
-/

@[expose] public section

open AddMonoidAlgebra MeasureTheory Filter Topology
open FroehlichSpencer.BKT.Rotator.Ginibre
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Ginibre

variable {V : Type*} [Fintype V]

/-- Bounded pointwise limits of evaluations of Ginibre-cone elements. -/
def IsGinibreLimit (F : (V → ℝ) × (V → ℝ) → ℝ) : Prop :=
  ∃ (P : ℕ → DupTrigAlgebra V) (C : ℝ), (∀ N, IsGinibre (P N)) ∧
    (∀ N z, ‖dupEval V (P N) z‖ ≤ C) ∧
    ∀ z, Tendsto (fun N => dupEval V (P N) z) atTop (𝓝 (F z : ℂ))

namespace IsGinibreLimit

theorem of_isGinibre {P : DupTrigAlgebra V} (hP : IsGinibre P)
    {F : (V → ℝ) × (V → ℝ) → ℝ} (hF : ∀ z, dupEval V P z = (F z : ℂ)) : IsGinibreLimit F := by
  obtain ⟨C, hC⟩ := exists_norm_dupEval_le P
  exact ⟨fun _ => P, C, fun _ => hP, fun _ => hC, fun z => by
    rw [← hF z]
    exact tendsto_const_nhds⟩

theorem one : IsGinibreLimit (fun _ : (V → ℝ) × (V → ℝ) => (1 : ℝ)) :=
  of_isGinibre IsGinibre.one fun z => by simp

theorem mul {F G : (V → ℝ) × (V → ℝ) → ℝ} (hF : IsGinibreLimit F) (hG : IsGinibreLimit G) :
    IsGinibreLimit fun z => F z * G z := by
  obtain ⟨P, C, hP, hC, hlimP⟩ := hF
  obtain ⟨Q, D, hQ, hD, hlimQ⟩ := hG
  refine ⟨fun N => P N * Q N, C * D, fun N => (hP N).mul (hQ N), fun N z => ?_, fun z => ?_⟩
  · rw [map_mul, Pi.mul_apply, norm_mul]
    exact mul_le_mul (hC N z) (hD N z) (norm_nonneg _) ((norm_nonneg _).trans (hC N z))
  · simp only [map_mul, Pi.mul_apply, Complex.ofReal_mul]
    exact (hlimP z).mul (hlimQ z)

theorem finsetProd {ι : Type*} (s : Finset ι) {F : ι → (V → ℝ) × (V → ℝ) → ℝ}
    (h : ∀ i ∈ s, IsGinibreLimit (F i)) : IsGinibreLimit fun z => ∏ i ∈ s, F i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one : IsGinibreLimit (V := V) fun _ => (1 : ℝ))
  | insert a s ha ih =>
      simp_rw [Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congr {F G : (V → ℝ) × (V → ℝ) → ℝ} (hF : IsGinibreLimit F) (h : ∀ z, F z = G z) :
    IsGinibreLimit G := by
  have : F = G := funext h
  rwa [← this]

/-- The exponential of the evaluation of a cone element lies in the closed cone. -/
theorem exp {Q : DupTrigAlgebra V} (hQ : IsGinibre Q) {S : (V → ℝ) × (V → ℝ) → ℝ}
    (hS : ∀ z, dupEval V Q z = (S z : ℂ)) : IsGinibreLimit fun z => Real.exp (S z) := by
  obtain ⟨CQ, hCQ⟩ := exists_norm_dupEval_le Q
  have hSb : ∀ z, |S z| ≤ CQ := fun z => by
    have := hCQ z
    rwa [hS z, Complex.norm_real, Real.norm_eq_abs] at this
  refine ⟨fun N => ∑ k ∈ Finset.range N, ((Nat.factorial k : ℝ)⁻¹) • Q ^ k, Real.exp CQ,
    fun N => IsGinibre.sum _ fun k _ => (hQ.pow k).smul (by positivity), fun N z => ?_,
    fun z => ?_⟩
  · have hev : dupEval V (∑ k ∈ Finset.range N, ((Nat.factorial k : ℝ)⁻¹) • Q ^ k) z =
        ((∑ k ∈ Finset.range N, S z ^ k / (Nat.factorial k : ℝ) : ℝ) : ℂ) := by
      simp only [map_sum, map_smul, map_pow, Finset.sum_apply, Pi.smul_apply, Pi.pow_apply, hS z,
        Complex.real_smul]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hev, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_sum_pow_div_factorial_le (S z) N).trans (Real.exp_le_exp.mpr (hSb z))
  · have hev : ∀ N, dupEval V (∑ k ∈ Finset.range N, ((Nat.factorial k : ℝ)⁻¹) • Q ^ k) z =
        ((∑ k ∈ Finset.range N, S z ^ k / (Nat.factorial k : ℝ) : ℝ) : ℂ) := fun N => by
      simp only [map_sum, map_smul, map_pow, Finset.sum_apply, Pi.smul_apply, Pi.pow_apply, hS z,
        Complex.real_smul]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    simp_rw [hev]
    exact (Complex.continuous_ofReal.tendsto _).comp (tendsto_sum_pow_div_factorial (S z))

/-- **Positivity of the closed cone.** -/
theorem integral_nonneg {ν ν' : Measure ℝ} [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    {lam lam' : ℤ → ℝ} (hν : HasRealFourier ν lam) (hν' : HasRealFourier ν' lam')
    (hK : HasEquivKernel lam lam') {F : (V → ℝ) × (V → ℝ) → ℝ} (hF : IsGinibreLimit F) :
    0 ≤ ∫ z, F z ∂(siteProduct ν V).prod (siteProduct ν' V) := by
  obtain ⟨P, C, hP, hC, hlim⟩ := hF
  have hdct := tendsto_integral_of_dominated_convergence
    (μ := (siteProduct ν V).prod (siteProduct ν' V)) (F := fun N => dupEval V (P N))
    (f := fun z => (F z : ℂ)) (fun _ => C)
    (fun N => (continuous_dupEval (P N)).aestronglyMeasurable) (integrable_const _)
    (fun N => ae_of_all _ (hC N)) (ae_of_all _ hlim)
  simp_rw [integral_dupEval_siteProduct hν hν', integral_complex_ofReal] at hdct
  have hre := (Complex.continuous_re.tendsto _).comp hdct
  simp only [Function.comp_def, Complex.ofReal_re] at hre
  exact ge_of_tendsto' hre fun N => dupFunctional_nonneg hK (hP N)

end IsGinibreLimit

/-- A pair of bond weight functions whose duplicated product lies in the closed Ginibre cone for
every bond frequency. -/
def IsGinibrePair (V : Type*) [Fintype V] (w₁ w₂ : ℝ → ℝ) : Prop :=
  ∀ d : Frequency V, IsGinibreLimit fun z : (V → ℝ) × (V → ℝ) => w₁ (phase d z.1) * w₂ (phase d z.2)

theorem isGinibrePair_one : IsGinibrePair V (fun _ => 1) (fun _ => 1) := fun _ =>
  IsGinibreLimit.one.congr fun _ => by ring

/-- The plane-rotator bond weight `exp(J cos φ)`. -/
def expCosWeight (J : ℝ) (φ : ℝ) : ℝ :=
  Real.exp (J * Real.cos φ)

/-- `(exp(J₁ cos), exp(J₂ cos))` is a Ginibre pair for `0 ≤ J₂ ≤ J₁`. -/
theorem isGinibrePair_expCos {J₁ J₂ : ℝ} (h₂ : 0 ≤ J₂) (h₁₂ : J₂ ≤ J₁) :
    IsGinibrePair V (expCosWeight J₁) (expCosWeight J₂) := fun d => by
  have ha : 0 ≤ (J₁ + J₂) / 2 := by linarith
  have hb : 0 ≤ (J₁ - J₂) / 2 := by linarith
  have hQ : IsGinibre (((J₁ + J₂) / 2) • cosPair d 1 + ((J₁ - J₂) / 2) • cosPair d (-1)) :=
    ((isGinibre_cosPair d (by norm_num)).smul ha).add ((isGinibre_cosPair d (by norm_num)).smul hb)
  refine (IsGinibreLimit.exp hQ (S := fun z => J₁ * Real.cos (phase d z.1) +
    J₂ * Real.cos (phase d z.2)) fun z => ?_).congr fun z => ?_
  · simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, dupEval_cosPair, Complex.real_smul]
    push_cast
    ring
  · rw [expCosWeight, expCosWeight, ← Real.exp_add]

theorem isGinibrePair_expCos_one {J : ℝ} (hJ : 0 ≤ J) :
    IsGinibrePair V (expCosWeight J) (fun _ => 1) := fun d =>
  (isGinibrePair_expCos le_rfl hJ d).congr fun z => by simp [expCosWeight]

end FroehlichSpencer.BKT.Ginibre

end
