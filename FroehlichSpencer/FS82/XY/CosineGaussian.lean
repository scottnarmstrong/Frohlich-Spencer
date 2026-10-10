/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.GaugeAverage
public import FroehlichSpencer.FS82.Root.CosineJensen

/-!
# renormalization of a separated family by characteristic functions

For co-closed integer currents `J i` and gains `g i` with

`∑ s_i² g_i ≤ 2π ⟨k_s, A⁻¹ k_s⟩`,  `k_s = ∑ s_i k_i`,

the matrix `R_ij = 2π ⟨k_i, A⁻¹ k_j⟩ − δ_ij g_i` is positive semidefinite, and the gauge-averaged
integral of `∏ (1 + K_i cos(⟨J_i, φ⟩ + θ_i))` is the integral of
`∏ (1 + K_i e^{−g_i/2} cos(y_i + θ_i))` against the centred Gaussian with covariance `R`.

Both
sides are the same finite sum over sign patterns.

This is the renormalization of FS82 Section 2.8
and (4.36) for one terminal branch, in a form that needs no chart of the gauge quotient: the
reduced measure is a centred Gaussian on the index set, so it is even, and Jensen's inequality
(2.101) applies.

* `integral_cosineProduct_gaussian`: the sign-pattern sum of a Gaussian cosine product.
* `branchCovariance_posSemidef`, `branch_integral_eq_gaussian`: the renormalized identity.
* `gaussian_cosineProduct_jensen`: Jensen with phase representatives.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.GaugeAverage

open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Gaussian.RenormalizedFamily.RenormalizedCharacters
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.SourceEnsembleConstructor
open FroehlichSpencer.FS82.Root.MomentComparisonAssembly

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Gaussian cosine products -/

/-- The quadratic form of a covariance matrix at a sign pattern. -/
noncomputable def signQuadratic (R : Matrix ι ι ℝ) (σ : ι → Sign) : ℝ :=
  dotProduct (fun i => signValue (σ i)) (R.mulVec fun i => signValue (σ i))

theorem integrable_exp_gaussianPairing (R : Matrix ι ι ℝ) (s : ι → ℝ) :
    Integrable (fun y : EuclideanSpace ℝ ι =>
      Complex.exp (Complex.I * ((∑ i, s i * y i : ℝ) : ℂ))) (multivariateGaussian 0 R) := by
  refine Integrable.of_bound ?_ 1 (ae_of_all _ fun y => ?_)
  · have hm : Measurable fun y : EuclideanSpace ℝ ι => ∑ i, s i * y i := by fun_prop
    exact (Complex.measurable_exp.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp hm))).aestronglyMeasurable
  · rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

theorem integral_cosineProduct_gaussian {R : Matrix ι ι ℝ} (hR : R.PosSemidef) (K θ : ι → ℝ) :
    ((∫ y : EuclideanSpace ℝ ι, ∏ i, (1 + K i * Real.cos (y i + θ i))
        ∂multivariateGaussian 0 R : ℝ) : ℂ) =
      ∑ σ : ι → Sign, signWeight K θ σ * Complex.exp (-(signQuadratic R σ / 2 : ℝ)) := by
  rw [← integral_complex_ofReal]
  have hpt : ∀ y : EuclideanSpace ℝ ι,
      ((∏ i, (1 + K i * Real.cos (y i + θ i)) : ℝ) : ℂ) =
        ∑ σ : ι → Sign, signWeight K θ σ *
          Complex.exp (Complex.I * ((∑ i, signValue (σ i) * y i : ℝ) : ℂ)) :=
    fun y => cosineProduct_expansion K θ fun i => y i
  simp_rw [hpt]
  rw [integral_finsetSum _ fun σ _ => (integrable_exp_gaussianPairing R _).const_mul _]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_const_mul]
  congr 1
  let s : EuclideanSpace ℝ ι := WithLp.toLp 2 fun i => signValue (σ i)
  have hch := charFun_multivariateGaussian (μ := (0 : EuclideanSpace ℝ ι)) hR s
  rw [charFun_apply] at hch
  have hfun : (fun y : EuclideanSpace ℝ ι =>
      Complex.exp (Complex.I * ((∑ i, signValue (σ i) * y i : ℝ) : ℂ))) =
      fun y => Complex.exp ((inner ℝ y s : ℝ) * Complex.I) := by
    funext y
    congr 1
    have : inner ℝ y s = ∑ i, signValue (σ i) * y i := by
      simp [s, PiLp.inner_apply]
    rw [this, mul_comm]
  rw [hfun, hch]
  congr 1
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, signQuadratic, s]
  push_cast
  ring

/-- A centred multivariate Gaussian is even. -/
theorem multivariateGaussian_map_neg {R : Matrix ι ι ℝ} (hR : R.PosSemidef) :
    Measure.map (fun y : EuclideanSpace ℝ ι => -y) (multivariateGaussian 0 R) =
      multivariateGaussian 0 R := by
  apply Measure.ext_of_charFun
  funext t
  have hneg : (fun y : EuclideanSpace ℝ ι => -y) = fun y => (-1 : ℝ) • y := by
    funext y
    simp
  rw [hneg, charFun_map_smul, charFun_multivariateGaussian hR, charFun_multivariateGaussian hR]
  simp [Matrix.mulVec_neg]

theorem integrable_cosineProduct_gaussian (R : Matrix ι ι ℝ) (z θ : ι → ℝ) :
    Integrable (fun y : EuclideanSpace ℝ ι => ∏ i, (1 + z i * Real.cos (y i + θ i)))
      (multivariateGaussian 0 R) := by
  refine Integrable.of_bound ?_ (∏ i, (1 + |z i|)) (ae_of_all _ fun y => ?_)
  · have hm : Measurable fun y : EuclideanSpace ℝ ι =>
        ∏ i, (1 + z i * Real.cos (y i + θ i)) := by fun_prop
    exact hm.aestronglyMeasurable
  · rw [Real.norm_eq_abs, Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
    calc |1 + z i * Real.cos (y i + θ i)| ≤ |1| + |z i * Real.cos (y i + θ i)| := abs_add_le _ _
      _ ≤ 1 + |z i| := by
        rw [abs_one, abs_mul]
        have hc := Real.abs_cos_le_one (y i + θ i)
        nlinarith [abs_nonneg (z i)]

/-- Nonnegativity of a Gaussian cosine product with amplitudes in `[0, 1]`. -/
theorem integral_cosineProduct_gaussian_nonneg (R : Matrix ι ι ℝ) (z θ : ι → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1) :
    0 ≤ ∫ y : EuclideanSpace ℝ ι, ∏ i, (1 + z i * Real.cos (y i + θ i))
      ∂multivariateGaussian 0 R := by
  refine integral_nonneg fun y => Finset.prod_nonneg fun i _ => ?_
  have hc := Real.neg_one_le_cos (y i + θ i)
  nlinarith [hz0 i, hz1 i]

/-- Positivity of a Gaussian cosine product with amplitudes in `[0, 1)`. -/
theorem integral_cosineProduct_gaussian_pos (R : Matrix ι ι ℝ) (z θ : ι → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i < 1) :
    0 < ∫ y : EuclideanSpace ℝ ι, ∏ i, (1 + z i * Real.cos (y i + θ i))
      ∂multivariateGaussian 0 R := by
  have hc : 0 < ∏ i, (1 - z i) := Finset.prod_pos fun i _ => by linarith [hz1 i]
  have hle : ∫ _ : EuclideanSpace ℝ ι, ∏ i, (1 - z i) ∂multivariateGaussian 0 R ≤
      ∫ y : EuclideanSpace ℝ ι, ∏ i, (1 + z i * Real.cos (y i + θ i))
        ∂multivariateGaussian 0 R := by
    refine integral_mono (integrable_const _) (integrable_cosineProduct_gaussian R z θ) fun y => ?_
    refine Finset.prod_le_prod₀ (fun i _ => by linarith [hz1 i]) fun i _ => ?_
    have hcos := Real.neg_one_le_cos (y i + θ i)
    nlinarith [hz0 i]
  rw [integral_const] at hle
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hle
  exact lt_of_lt_of_le hc hle

/-- **Jensen on the reduced Gaussian (2.101)**, with phase representatives. -/
theorem gaussian_cosineProduct_jensen {R : Matrix ι ι ℝ} (hR : R.PosSemidef)
    (z θ' : ι → ℝ) (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i < 1) :
    Real.exp (-∑ i, SourceJensen.sourceJensenGamma (z i) * θ' i ^ 2) *
        ∫ y : EuclideanSpace ℝ ι, ∏ i, (1 + z i * Real.cos (y i)) ∂multivariateGaussian 0 R ≤
      ∫ y : EuclideanSpace ℝ ι, ∏ i, (1 + z i * Real.cos (y i - θ' i))
        ∂multivariateGaussian 0 R := by
  have h := cosineProduct_jensen (multivariateGaussian 0 R) (multivariateGaussian_map_neg hR)
    z θ' (fun i (y : EuclideanSpace ℝ ι) => y i) hz0 hz1 (fun i => by fun_prop)
    (fun i y => by simp)
  simpa [SourceJensen.ensembleJensenBudget, ensembleCosineDensity,
    ensembleShiftedCosineDensity] using h

end FroehlichSpencer.FS82.XY.GaugeAverage

end
