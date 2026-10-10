/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.FiniteHodge
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Finite Gaussian adapters

Characteristic, moment, matrix, and positivity adapters for finite centered
multivariate Gaussians.
-/

public section

namespace FroehlichSpencer.FS82.Gaussian

open scoped InnerProductSpace
open ProbabilityTheory
/-- Generic finite-dimensional Gaussian characteristic formula. The source box
covariance still has to be identified with a matrix `S`. -/
theorem finiteGaussianAdapter_characteristic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef)
    (u : EuclideanSpace ℝ ι) :
    MeasureTheory.charFun
      (ProbabilityTheory.multivariateGaussian 0 S) u =
      Complex.exp (-(↑(u.ofLp ⬝ᵥ S.mulVec u.ofLp) / 2)) := by
  simpa using ProbabilityTheory.charFun_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ ι)) hS u

/-- The centered Mathlib Gaussian is a genuine probability measure. -/
theorem finiteGaussianAdapter_is_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (_hS : S.PosSemidef) :
    MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.multivariateGaussian
      (0 : EuclideanSpace ℝ ι) S) := by
  infer_instance

/-- The one-dimensional pushforward of a centered multivariate Gaussian has
the source's real exponential-moment formula. This is the finite-dimensional
adapter used once the box covariance matrix has been identified. -/
theorem finiteGaussianAdapter_mgf_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef)
    (u : EuclideanSpace ℝ ι) (t : ℝ) :
    ProbabilityTheory.mgf (fun x : EuclideanSpace ℝ ι => inner ℝ u x)
      (ProbabilityTheory.multivariateGaussian 0 S) t =
      Real.exp (t ^ 2 * (u.ofLp ⬝ᵥ S.mulVec u.ofLp) / 2) := by
  let μ := ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ ι) S
  let L : StrongDual ℝ (EuclideanSpace ℝ ι) :=
    InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ ι) u
  have hmean : μ[L] = 0 := by
    rw [IsGaussian.integral_dual]
    simp [μ]
  have hvariance :
    ProbabilityTheory.variance L μ = u.ofLp ⬝ᵥ S.mulVec u.ofLp := by
    rw [← ProbabilityTheory.covarianceBilinDual_self_eq_variance
      IsGaussian.memLp_two_id L,
      ← ProbabilityTheory.covarianceBilin_eq_covarianceBilinDual (μ := μ) u u]
    simpa [μ] using ProbabilityTheory.covarianceBilin_multivariateGaussian hS u u
  have hQ : 0 ≤ u.ofLp ⬝ᵥ S.mulVec u.ofLp := by
    rw [← hvariance]
    exact ProbabilityTheory.variance_nonneg L μ
  change ProbabilityTheory.mgf L μ t = _
  rw [← ProbabilityTheory.mgf_id_map L.continuous.aemeasurable,
    ProbabilityTheory.IsGaussian.map_eq_gaussianReal L,
    ProbabilityTheory.mgf_id_gaussianReal]
  rw [hmean, hvariance]
  simp only [zero_mul, zero_add, Real.toNNReal_of_nonneg hQ]
  push_cast
  ring_nf


noncomputable def matrixOfLinearMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  fun i j => (T (EuclideanSpace.single j 1)).ofLp i

theorem matrixOfLinearMap_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) :
    (matrixOfLinearMap T).mulVec x.ofLp = (T x).ofLp := by
  ext i
  have hrepr : x = ∑ j, x j • EuclideanSpace.single j 1 := by
    have h := (EuclideanSpace.basisFun ι ℝ).sum_repr x
    simpa [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using h.symm
  have hT : T x = ∑ j, x j • T (EuclideanSpace.single j 1) := by
    calc
      T x = T (∑ j, x j • EuclideanSpace.single j 1) := congrArg T hrepr
      _ = ∑ j, T (x j • EuclideanSpace.single j 1) := map_sum T _ _
      _ = ∑ j, x j • T (EuclideanSpace.single j 1) := by simp
  simpa [Matrix.mulVec_apply, dotProduct, matrixOfLinearMap,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, mul_comm] using
      (congrArg (fun y : EuclideanSpace ℝ ι => y.ofLp i) hT).symm

theorem matrixOfLinearMap_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
    (hsym : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (hpos : ∀ x, 0 ≤ inner ℝ x (T x)) : (matrixOfLinearMap T).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    change (T (EuclideanSpace.single i 1)).ofLp j =
      (T (EuclideanSpace.single j 1)).ofLp i
    have h := hsym (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
    simpa [EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_left,
      mul_one, one_mul] using h.symm
  · intro x
    let v : EuclideanSpace ℝ ι := WithLp.toLp 2 x
    have hp := hpos v
    change 0 ≤ star v.ofLp ⬝ᵥ (matrixOfLinearMap T).mulVec v.ofLp
    rw [matrixOfLinearMap_mulVec T v]
    simpa [dotProduct, PiLp.inner_apply, mul_comm] using hp


end FroehlichSpencer.FS82.Gaussian
end
