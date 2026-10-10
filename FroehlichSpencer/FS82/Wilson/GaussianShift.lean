/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/

module
public import FroehlichSpencer.FS82.Gaussian.FiniteQuotientGaussian
public import FroehlichSpencer.FS82.Wilson.LoopCovariance
public import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.ComplexMGF

/-!
# The Gaussian translation of the Wilson loop

Finite-dimensional Cameron–Martin translation on the real gauge quotient,
with the loop-field residual as its Gaussian cost (FS82 (2.48)–(2.54)).
-/

public section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
open Matrix
open scoped MatrixOrder
set_option linter.style.haveILetI false

namespace FroehlichSpencer.FS82.Wilson

theorem stdGaussian_complexLinearTransform
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L M : StrongDual ℝ E) :
    ∫ x : E, Complex.exp ((L x : ℂ) + Complex.I * (M x : ℂ))
        ∂ProbabilityTheory.stdGaussian E =
      Complex.exp ((∑ i : Fin (Module.finrank ℝ E),
        ((L (stdOrthonormalBasis ℝ E i) : ℂ) +
          Complex.I * (M (stdOrthonormalBasis ℝ E i) : ℂ)) ^ 2) / 2) := by
  let b := stdOrthonormalBasis ℝ E
  let g : (Fin (Module.finrank ℝ E) → ℝ) → E := fun x => ∑ i, x i • b i
  rw [ProbabilityTheory.stdGaussian, integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  have harg (x : Fin (Module.finrank ℝ E) → ℝ) :
      (L (g x) : ℂ) + Complex.I * (M (g x) : ℂ) =
        ∑ i, (x i : ℂ) * ((L (b i) : ℂ) + Complex.I * (M (b i) : ℂ)) := by
    simp only [g, map_sum, map_smul, smul_eq_mul, Complex.ofReal_sum,
      Complex.ofReal_mul]
    calc
      _ = ∑ i, ((x i : ℂ) * (L (b i) : ℂ) +
          Complex.I * ((x i : ℂ) * (M (b i) : ℂ))) := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      _ = ∑ i, (x i : ℂ) *
          ((L (b i) : ℂ) + Complex.I * (M (b i) : ℂ)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring_nf
  have harg' (x : Fin (Module.finrank ℝ E) → ℝ) :
      (L (∑ i, x i • b i) : ℂ) + Complex.I * (M (∑ i, x i • b i) : ℂ) =
        ∑ i, (x i : ℂ) * ((L (b i) : ℂ) + Complex.I * (M (b i) : ℂ)) := by
    simpa [g] using harg x
  change (∫ x : Fin (Module.finrank ℝ E) → ℝ, Complex.exp ((L (g x) : ℂ) + Complex.I * (M (g x) : ℂ)) ∂Measure.pi (fun _ : Fin (Module.finrank ℝ E) => ProbabilityTheory.gaussianReal 0 1)) = _
  simp_rw [harg]
  simp_rw [Complex.exp_sum]
  rw [integral_fintype_prod_eq_prod (f := fun i (x : ℝ) => Complex.exp
    ((x : ℂ) * ((L (b i) : ℂ) + Complex.I * (M (b i) : ℂ))))]
  have hcoord (i : Fin (Module.finrank ℝ E)) :
      (∫ x : ℝ, Complex.exp ((x : ℂ) *
        ((L (b i) : ℂ) + Complex.I * (M (b i) : ℂ)))
        ∂ProbabilityTheory.gaussianReal 0 1) =
      Complex.exp ((((L (b i) : ℂ) + Complex.I * (M (b i) : ℂ)) ^ 2) / 2) := by
    let c := (L (b i) : ℂ) + Complex.I * (M (b i) : ℂ)
    calc
      (∫ x : ℝ, Complex.exp ((x : ℂ) * c)
          ∂ProbabilityTheory.gaussianReal 0 1) =
        ProbabilityTheory.complexMGF id
          (ProbabilityTheory.gaussianReal 0 1) c := by
            rw [ProbabilityTheory.complexMGF]
            apply integral_congr_ae
            filter_upwards [] with x
            simp only [id_eq]
            ring_nf
      _ = Complex.exp (c ^ 2 / 2) := by
            rw [ProbabilityTheory.complexMGF_id_gaussianReal]
            simp
      _ = Complex.exp ((((L (b i) : ℂ) + Complex.I * (M (b i) : ℂ)) ^ 2) / 2) := by
            rfl
  simp_rw [hcoord]
  rw [← Complex.exp_sum]
  congr 1
  simp [Finset.sum_div, b]


theorem stdGaussian_inner_complexTransform
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (u v : E) :
    ∫ x : E, Complex.exp ((inner ℝ u x : ℝ) +
      Complex.I * (inner ℝ v x : ℝ)) ∂ProbabilityTheory.stdGaussian E =
      Complex.exp ((((inner ℝ u u : ℝ) - inner ℝ v v : ℝ) +
        2 * Complex.I * (inner ℝ u v : ℝ)) / 2) := by
  let b := stdOrthonormalBasis ℝ E
  let L := InnerProductSpace.toDualMap ℝ E u
  let M := InnerProductSpace.toDualMap ℝ E v
  have hgeneric := stdGaussian_complexLinearTransform L M
  have huu : ∑ i : Fin (Module.finrank ℝ E),
      (inner ℝ u (b i)) ^ 2 = inner ℝ u u := by
    calc
      _ = ∑ i, inner ℝ u (b i) * inner ℝ (b i) u := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [pow_two, real_inner_comm (b i) u]
      _ = inner ℝ u u := OrthonormalBasis.sum_inner_mul_inner b u u
  have hvv : ∑ i : Fin (Module.finrank ℝ E),
      (inner ℝ v (b i)) ^ 2 = inner ℝ v v := by
    calc
      _ = ∑ i, inner ℝ v (b i) * inner ℝ (b i) v := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [pow_two, real_inner_comm (b i) v]
      _ = inner ℝ v v := OrthonormalBasis.sum_inner_mul_inner b v v
  have huv : ∑ i : Fin (Module.finrank ℝ E),
      inner ℝ u (b i) * inner ℝ v (b i) = inner ℝ u v := by
    simpa [real_inner_comm] using OrthonormalBasis.sum_inner_mul_inner b u v
  have hA : ∑ i : Fin (Module.finrank ℝ E),
      (inner ℝ u (b i) : ℂ) ^ 2 = (inner ℝ u u : ℂ) := by
    calc
      _ = Complex.ofReal (∑ i, (inner ℝ u (b i)) ^ 2 : ℝ) := by
        simp only [Complex.ofReal_sum, Complex.ofReal_pow]
      _ = (inner ℝ u u : ℂ) := congrArg Complex.ofReal huu
  have hB : ∑ i : Fin (Module.finrank ℝ E),
      (inner ℝ v (b i) : ℂ) ^ 2 = (inner ℝ v v : ℂ) := by
    calc
      _ = Complex.ofReal (∑ i, (inner ℝ v (b i)) ^ 2 : ℝ) := by
        simp only [Complex.ofReal_sum, Complex.ofReal_pow]
      _ = (inner ℝ v v : ℂ) := congrArg Complex.ofReal hvv
  have hAB : ∑ i : Fin (Module.finrank ℝ E),
      (inner ℝ u (b i) : ℂ) * (inner ℝ v (b i) : ℂ) =
        (inner ℝ u v : ℂ) := by
    calc
      _ = Complex.ofReal (∑ i, inner ℝ u (b i) * inner ℝ v (b i) : ℝ) := by
        simp only [Complex.ofReal_sum, Complex.ofReal_mul]
      _ = (inner ℝ u v : ℂ) := congrArg Complex.ofReal huv
  have hsum :
      (∑ i : Fin (Module.finrank ℝ E),
        ((inner ℝ u (b i) : ℂ) +
          Complex.I * (inner ℝ v (b i) : ℂ)) ^ 2) =
      (inner ℝ u u : ℂ) - (inner ℝ v v : ℂ) +
        2 * Complex.I * (inner ℝ u v : ℂ) := by
    calc
      _ = ∑ i, ((inner ℝ u (b i) : ℂ) ^ 2 -
          (inner ℝ v (b i) : ℂ) ^ 2 +
          2 * Complex.I * ((inner ℝ u (b i) : ℂ) *
            (inner ℝ v (b i) : ℂ))) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring_nf
              rw [Complex.I_sq]
              ring_nf
      _ = (∑ i, (inner ℝ u (b i) : ℂ) ^ 2) -
          (∑ i, (inner ℝ v (b i) : ℂ) ^ 2) +
          2 * Complex.I *
            (∑ i, (inner ℝ u (b i) : ℂ) *
              (inner ℝ v (b i) : ℂ)) := by
                rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                  ← Finset.mul_sum]
      _ = _ := by rw [hA, hB, hAB]
  calc
    _ = Complex.exp ((∑ i : Fin (Module.finrank ℝ E),
        ((inner ℝ u (b i) : ℂ) +
          Complex.I * (inner ℝ v (b i) : ℂ)) ^ 2) / 2) := by
          simpa [L, M, b, InnerProductSpace.toDualMap_apply_apply] using hgeneric
    _ = Complex.exp ((((inner ℝ u u : ℝ) - inner ℝ v v : ℝ) +
        2 * Complex.I * (inner ℝ u v : ℝ)) / 2) := by
          congr 1
          rw [hsum]
          push_cast
          ring_nf
theorem multivariateGaussian_inner_complexTransform
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (_hS : S.PosSemidef)
    (u v : EuclideanSpace ℝ ι) :
    ∫ x : EuclideanSpace ℝ ι,
      Complex.exp ((inner ℝ u x : ℝ) + Complex.I * (inner ℝ v x : ℝ))
        ∂ProbabilityTheory.multivariateGaussian 0 S =
      Complex.exp ((((covarianceBilin
        (ProbabilityTheory.multivariateGaussian 0 S) u u : ℝ) -
          covarianceBilin (ProbabilityTheory.multivariateGaussian 0 S) v v : ℝ) +
        2 * Complex.I * covarianceBilin
        (ProbabilityTheory.multivariateGaussian 0 S) u v) / 2) := by
  letI : S.PosSemidef := _hS
  let A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  let μ := ProbabilityTheory.multivariateGaussian 0 S
  have hmap : μ = Measure.map A
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
    simp [μ, ProbabilityTheory.multivariateGaussian, A]
  have hcov (x y : EuclideanSpace ℝ ι) :
      covarianceBilin μ x y = inner ℝ (A.adjoint x) (A.adjoint y) := by
    rw [hmap, ProbabilityTheory.covarianceBilin_map
      (ProbabilityTheory.IsGaussian.memLp_two_id) A x y]
    simp [ProbabilityTheory.covarianceBilin_stdGaussian, innerSL]
  have hmeas : Measurable (fun x : EuclideanSpace ℝ ι =>
      Complex.exp ((inner ℝ u x : ℝ) + Complex.I * (inner ℝ v x : ℝ))) := by
    fun_prop
  have harg (x : EuclideanSpace ℝ ι) :
      (inner ℝ u (A x) : ℝ) + Complex.I * (inner ℝ v (A x) : ℝ) =
        (inner ℝ (A.adjoint u) x : ℝ) +
          Complex.I * (inner ℝ (A.adjoint v) x : ℝ) := by
    rw [← ContinuousLinearMap.adjoint_inner_left A x u,
      ← ContinuousLinearMap.adjoint_inner_left A x v]
  have hstd := stdGaussian_inner_complexTransform
    (A.adjoint u) (A.adjoint v)
  calc
    ∫ x : EuclideanSpace ℝ ι,
        Complex.exp ((inner ℝ u x : ℝ) + Complex.I * (inner ℝ v x : ℝ)) ∂μ =
      ∫ x : EuclideanSpace ℝ ι,
        Complex.exp ((inner ℝ u x : ℝ) + Complex.I * (inner ℝ v x : ℝ))
          ∂Measure.map A (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
            rw [hmap]
    _ = ∫ x : EuclideanSpace ℝ ι,
        Complex.exp ((inner ℝ u (A x) : ℝ) +
          Complex.I * (inner ℝ v (A x) : ℝ))
          ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι) :=
            MeasureTheory.integral_map A.continuous.aemeasurable
              hmeas.aestronglyMeasurable
    _ = ∫ x : EuclideanSpace ℝ ι,
        Complex.exp ((inner ℝ (A.adjoint u) x : ℝ) +
          Complex.I * (inner ℝ (A.adjoint v) x : ℝ))
          ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with x
            rw [harg]
    _ = Complex.exp ((((inner ℝ (A.adjoint u) (A.adjoint u) : ℝ) -
          inner ℝ (A.adjoint v) (A.adjoint v) : ℝ) +
          2 * Complex.I * (inner ℝ (A.adjoint u) (A.adjoint v) : ℝ)) / 2) := hstd
    _ = Complex.exp ((((covarianceBilin μ u u : ℝ) -
          covarianceBilin μ v v : ℝ) +
          2 * Complex.I * covarianceBilin μ u v) / 2) := by
            congr 1
            rw [← hcov u u, ← hcov v v, ← hcov u v]

/-- Exponential tilting of a centered finite Gaussian by one linear functional is
translation by its covariance vector. This is the finite-dimensional Cameron–Martin
formula used below. -/
theorem finiteGaussian_tilt_eq_map_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef)
    (u h : EuclideanSpace ℝ ι)
    (hh : ∀ v, ProbabilityTheory.covarianceBilin
      (ProbabilityTheory.multivariateGaussian 0 S) u v = inner ℝ v h) :
    (ProbabilityTheory.multivariateGaussian 0 S).tilted (fun x => inner ℝ u x) =
      Measure.map (fun x : EuclideanSpace ℝ ι => x + h)
        (ProbabilityTheory.multivariateGaussian 0 S) := by
  let μ := ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ ι) S
  let f : EuclideanSpace ℝ ι → ℝ := fun x => inner ℝ u x
  let Z : ℝ := ∫ x, Real.exp (f x) ∂μ
  haveI : S.PosSemidef := hS
  haveI : ProbabilityTheory.IsGaussian μ := by dsimp [μ]; infer_instance
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hmean (w : EuclideanSpace ℝ ι) : ∫ x, (InnerProductSpace.toDualMap ℝ
      (EuclideanSpace ℝ ι) w) x ∂μ = 0 := by
    rw [ProbabilityTheory.IsGaussian.integral_dual]
    simp [μ]
  have hvar (w : EuclideanSpace ℝ ι) : ProbabilityTheory.variance
      (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ ι) w) μ =
      ProbabilityTheory.covarianceBilin μ w w := by
    rw [← ProbabilityTheory.covarianceBilinDual_self_eq_variance
      (ProbabilityTheory.IsGaussian.memLp_two_id (μ := μ))
        (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ ι) w),
      ← ProbabilityTheory.covarianceBilin_eq_covarianceBilinDual
        (μ := μ) w w]
  have hZ : Z = Real.exp (ProbabilityTheory.covarianceBilin μ u u / 2) := by
    have hq : ProbabilityTheory.covarianceBilin μ u u =
        u.ofLp ⬝ᵥ S.mulVec u.ofLp := by
      simpa [μ] using ProbabilityTheory.covarianceBilin_multivariateGaussian hS u u
    simpa [Z, f, ProbabilityTheory.mgf, hq] using
      Gaussian.finiteGaussianAdapter_mgf_inner S hS u 1
  have hZint : Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (f x)) μ := by
    letI : S.PosSemidef := hS
    let L' : StrongDual ℝ (EuclideanSpace ℝ ι) :=
      InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ ι) u
    have hpush : Measure.map L' μ = ProbabilityTheory.gaussianReal
        (∫ x, L' x ∂μ) (ProbabilityTheory.variance L' μ).toNNReal :=
      ProbabilityTheory.IsGaussian.map_eq_gaussianReal L'
    have hreal : Integrable (fun y : ℝ => Real.exp y) (Measure.map L' μ) := by
      rw [hpush]
      simpa using ProbabilityTheory.integrable_exp_mul_gaussianReal
        (μ := ∫ x, L' x ∂μ) (v := (ProbabilityTheory.variance L' μ).toNNReal) 1
    have hcomp := (integrable_map_measure (by fun_prop) L'.continuous.aemeasurable).mp hreal
    convert hcomp using 1
    ext x
    simp [L', f, InnerProductSpace.toDualMap_apply_apply]
  have htiltProb : IsProbabilityMeasure (μ.tilted f) := by
    exact MeasureTheory.isProbabilityMeasure_tilted hZint
  have hshiftProb : IsProbabilityMeasure (Measure.map (fun x : EuclideanSpace ℝ ι => x + h) μ) := by
    constructor
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp
  apply MeasureTheory.Measure.ext_of_charFun
  funext v
  let Vv : StrongDual ℝ (EuclideanSpace ℝ ι) := InnerProductSpace.toDualMap ℝ _ v
  have htiltChar : charFun (μ.tilted f) v =
      Complex.exp ((-(ProbabilityTheory.covarianceBilin μ v v) / 2 : ℝ) +
        Complex.I * (ProbabilityTheory.covarianceBilin μ u v : ℝ)) := by
    rw [MeasureTheory.charFun_eq_charFunDual_toDualMap, MeasureTheory.charFunDual_apply]
    have hpoint (x : EuclideanSpace ℝ ι) :
        (Real.exp (f x) / Z : ℝ) • Complex.exp (Vv x * Complex.I) =
          ((Z⁻¹ : ℝ) : ℂ) * Complex.exp
            ((inner ℝ u x : ℝ) + Complex.I * inner ℝ v x) := by
      change ((Real.exp (f x) / Z : ℝ) : ℂ) *
        Complex.exp (↑(inner ℝ v x) * Complex.I) = _
      rw [Complex.ofReal_div, Complex.ofReal_exp]
      rw [div_eq_mul_inv]
      rw [Complex.ofReal_inv]
      calc
        Complex.exp ↑(f x) * (↑Z)⁻¹ *
            Complex.exp (↑(inner ℝ v x) * Complex.I) =
          (↑Z)⁻¹ * (Complex.exp ↑(f x) *
            Complex.exp (↑(inner ℝ v x) * Complex.I)) := by ring
        _ = (↑Z)⁻¹ * Complex.exp
            (↑(inner ℝ u x) + Complex.I * ↑(inner ℝ v x)) := by
          rw [← Complex.exp_add]
          congr 2
          simp [f]
          ring
    have hmeas : Measurable (fun x : EuclideanSpace ℝ ι =>
        Complex.exp ((inner ℝ u x : ℝ) + Complex.I * inner ℝ v x)) := by fun_prop
    calc
      (∫ x, Complex.exp (Vv x * Complex.I) ∂μ.tilted f) =
          ∫ x, ((Z⁻¹ : ℝ) : ℂ) * Complex.exp
            ((inner ℝ u x : ℝ) + Complex.I * inner ℝ v x) ∂μ := by
              rw [MeasureTheory.integral_tilted]
              apply MeasureTheory.integral_congr_ae
              filter_upwards [] with x
              exact hpoint x
      _ = ((Z⁻¹ : ℝ) : ℂ) * ∫ x, Complex.exp
            ((inner ℝ u x : ℝ) + Complex.I * inner ℝ v x) ∂μ := by
              rw [MeasureTheory.integral_const_mul]
      _ = ((Z⁻¹ : ℝ) : ℂ) * Complex.exp
            ((((ProbabilityTheory.covarianceBilin μ u u : ℝ) -
                ProbabilityTheory.covarianceBilin μ v v : ℝ) +
              2 * Complex.I * ProbabilityTheory.covarianceBilin μ u v) / 2) := by
              rw [multivariateGaussian_inner_complexTransform S hS u v]
      _ = Complex.exp ((-(ProbabilityTheory.covarianceBilin μ v v) / 2 : ℝ) +
            Complex.I * (ProbabilityTheory.covarianceBilin μ u v : ℝ)) := by
              rw [hZ]
              rw [Complex.ofReal_inv, Complex.ofReal_exp]
              push_cast
              rw [← Complex.exp_neg, ← Complex.exp_add]
              congr 1
              ring
  have hshiftChar : charFun (Measure.map (fun x : EuclideanSpace ℝ ι => x + h) μ) v =
      Complex.exp ((-(ProbabilityTheory.covarianceBilin μ v v) / 2 : ℝ) +
        Complex.I * (ProbabilityTheory.covarianceBilin μ u v : ℝ)) := by
    rw [MeasureTheory.charFun_eq_charFunDual_toDualMap,
      MeasureTheory.charFunDual_map_add_const]
    have hbase : charFunDual μ Vv =
        Complex.exp (-(ProbabilityTheory.covarianceBilin μ v v) / 2) := by
      rw [ProbabilityTheory.IsGaussian.charFunDual_eq']
      have hm : μ[id] = 0 := by simp [μ]
      rw [hm,
        ProbabilityTheory.covarianceBilinDual_self_eq_variance
          (ProbabilityTheory.IsGaussian.memLp_two_id (μ := μ)) Vv,
        show ProbabilityTheory.variance Vv μ =
          ProbabilityTheory.covarianceBilin μ v v by simpa [Vv] using hvar v]
      simp [Vv]
      congr 1
      ring
    rw [hbase]
    have hinner : Vv h = ProbabilityTheory.covarianceBilin μ u v := by
      change inner ℝ v h = ProbabilityTheory.covarianceBilin μ u v
      exact (hh v).symm
    rw [hinner]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  exact htiltChar.trans hshiftChar.symm

/-- A linear exponential is integrable under every finite centered Gaussian. -/
theorem multivariateGaussian_exp_inner_integrable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (_hS : S.PosSemidef) (u : EuclideanSpace ℝ ι) :
    Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (inner ℝ u x))
      (ProbabilityTheory.multivariateGaussian 0 S) := by
  let μ := ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ ι) S
  let L : StrongDual ℝ (EuclideanSpace ℝ ι) :=
    InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ ι) u
  letI : S.PosSemidef := _hS
  have hpush : Measure.map L μ = ProbabilityTheory.gaussianReal
      (∫ x, L x ∂μ) (ProbabilityTheory.variance L μ).toNNReal :=
    ProbabilityTheory.IsGaussian.map_eq_gaussianReal L
  have hreal : Integrable (fun y : ℝ => Real.exp y) (Measure.map L μ) := by
    rw [hpush]
    simpa using ProbabilityTheory.integrable_exp_mul_gaussianReal
      (μ := ∫ x, L x ∂μ) (v := (ProbabilityTheory.variance L μ).toNNReal) 1
  have hcomp := (integrable_map_measure (by fun_prop) L.continuous.aemeasurable).mp hreal
  convert hcomp using 1
  ext x
  simp [L, InnerProductSpace.toDualMap_apply_apply]

/-- If a Gaussian measure is tilted by a functional that factors through a
measurable linear map, the tilted law descends to the tilt of its pushforward.
This is the measurable quotient step in the Wilson change of variables. -/
theorem map_tilted_eq_tilted_map
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} [SFinite μ] (q : X → Y) (hq : Measurable q)
    (g : Y → ℝ) (hg : Measurable g) :
    Measure.map q (μ.tilted (fun x => g (q x))) =
      (Measure.map q μ).tilted g := by
  have hZ : (∫ x, Real.exp (g (q x)) ∂μ) =
      ∫ y, Real.exp (g y) ∂Measure.map q μ := by
    symm
    exact MeasureTheory.integral_map hq.aemeasurable (by fun_prop)
  ext s hs
  rw [Measure.map_apply hq hs,
    MeasureTheory.tilted_apply _ _ (q ⁻¹' s),
    MeasureTheory.tilted_apply _ _ s, hZ]
  symm
  exact MeasureTheory.setLIntegral_map hs (by fun_prop) hq

open FroehlichSpencer.FS82.Gaussian

section WilsonDecomposition

variable {V E P : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P]

/-- The co-closed representative of the Wilson Gaussian shift. -/
@[expose] noncomputable def wilsonGaussianShift (C : ExactOneComplex V E P)
    (σ : EuclideanSpace ℝ P) : EuclideanSpace ℝ E :=
  hodgeInverseOnCoClosed C ⟨C.d₁.adjoint σ, adjoint_mem_coClosed C σ⟩

/-- The Hodge shift solves the source's orthogonal projection equation. -/
theorem wilsonGaussianShift_curl (C : ExactOneComplex V E P)
    (σ : EuclideanSpace ℝ P) :
    C.d₁ (wilsonGaussianShift C σ) = σ - loopFieldResidual C σ := by
  let η : coClosed C := ⟨C.d₁.adjoint σ, adjoint_mem_coClosed C σ⟩
  let τ := wilsonGaussianShift C σ
  have hLu : C.d₁.adjoint (C.d₁ (τ : EuclideanSpace ℝ E)) = C.d₁.adjoint σ := by
    have h := congrArg Subtype.val (hodgeOnCoClosed_hodgeInverse C η)
    change C.d₁.adjoint (C.d₁ τ) = C.d₁.adjoint σ
    exact h
  obtain ⟨τ', hτ'⟩ := exists_shift_eq_sub_loopFieldResidual C σ
  have hLτ : C.d₁.adjoint (C.d₁ τ') = C.d₁.adjoint σ := by
    rw [hτ', map_sub, adjoint_loopFieldResidual, sub_zero]
  have hd : C.d₁ (τ : EuclideanSpace ℝ E) = C.d₁ τ' := by
    have h0 : C.d₁.adjoint (C.d₁ ((τ : EuclideanSpace ℝ E) - τ')) = 0 := by
      rw [map_sub, map_sub, hLu, hLτ, sub_self]
    have hn : inner ℝ
        (C.d₁ ((τ : EuclideanSpace ℝ E) - τ'))
        (C.d₁ ((τ : EuclideanSpace ℝ E) - τ')) = 0 := by
      rw [← LinearMap.adjoint_inner_left, h0, inner_zero_left]
    have hz := inner_self_eq_zero.mp hn
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  change C.d₁ τ = σ - loopFieldResidual C σ
  rw [hd, hτ']

/-- The complete finite-dimensional decomposition used in (2.51). -/
theorem exists_wilsonGaussianShift_decomposition (C : ExactOneComplex V E P)
    (σ : EuclideanSpace ℝ P) :
    ∃ τ : EuclideanSpace ℝ E,
      C.d₁ τ = σ - loopFieldResidual C σ ∧
      ∀ α : EuclideanSpace ℝ E,
        inner ℝ (C.d₁ α) (loopFieldResidual C σ) = 0 := by
  refine ⟨wilsonGaussianShift C σ, wilsonGaussianShift_curl C σ, ?_⟩
  intro α
  rw [real_inner_comm]
  exact loopFieldResidual_inner_exact C σ α

/-- Ambient finite-Gaussian covariance in the quotient Laplacian normalization. -/
theorem finiteComplexGaussian_covarianceBilin
    (C : ExactOneComplex V E P) {β : ℝ} (hβ : 0 ≤ β)
    (x y : EuclideanSpace ℝ E) :
    ProbabilityTheory.covarianceBilin
        (ProbabilityTheory.multivariateGaussian 0
          (finiteComplexCovarianceMatrix C β)) x y =
      inner ℝ x ((β • finiteComplexAmbientCovariance C) y) := by
  let S := finiteComplexCovarianceMatrix C β
  let T := β • finiteComplexAmbientCovariance C
  have hS : S.PosSemidef := finiteComplexCovarianceMatrix_posSemidef C hβ
  rw [ProbabilityTheory.covarianceBilin_multivariateGaussian hS]
  calc
    x.ofLp ⬝ᵥ S.mulVec y.ofLp = x.ofLp ⬝ᵥ (T y).ofLp := by
      simp [S, T, finiteComplexCovarianceMatrix, matrixOfLinearMap_mulVec]
    _ = inner ℝ x (T y) := by
      simp [dotProduct, PiLp.inner_apply, mul_comm]

/-- The covariance vector of the source tilt is exactly the Hodge shift. -/
theorem wilsonGaussianShift_covariance_vector
    (C : ExactOneComplex V E P) {β : ℝ} (hβ : 0 < β)
    (σ : EuclideanSpace ℝ P) :
    ∀ v : EuclideanSpace ℝ E,
      ProbabilityTheory.covarianceBilin
          (ProbabilityTheory.multivariateGaussian 0
            (finiteComplexCovarianceMatrix C β))
          ((β⁻¹) • C.d₁.adjoint σ) v =
        inner ℝ v (wilsonGaussianShift C σ) := by
  let η : coClosed C := ⟨C.d₁.adjoint σ, adjoint_mem_coClosed C σ⟩
  have hKη : finiteComplexAmbientCovariance C (η : EuclideanSpace ℝ E) =
      wilsonGaussianShift C σ := by
    rw [finiteComplexAmbientCovariance_coClosed_apply]
    rfl
  intro v
  rw [finiteComplexGaussian_covarianceBilin C hβ.le]
  rw [show (β⁻¹) • C.d₁.adjoint σ = (β⁻¹) • (η : EuclideanSpace ℝ E) by rfl]
  calc
    inner ℝ ((β⁻¹) • (η : EuclideanSpace ℝ E))
        ((β • finiteComplexAmbientCovariance C) v) =
      (β⁻¹) * β * inner ℝ (η : EuclideanSpace ℝ E)
        (finiteComplexAmbientCovariance C v) := by
          simp [LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right,
            mul_assoc]
          ring
    _ = inner ℝ (finiteComplexAmbientCovariance C (η : EuclideanSpace ℝ E)) v := by
      rw [finiteComplexAmbientCovariance_symmetric]
      simp [ne_of_gt hβ]
    _ = inner ℝ v (wilsonGaussianShift C σ) := by
      rw [hKη, real_inner_comm]

/-- The exponential tilt by the Wilson sheet is translation by its Hodge shift
on the gauge quotient. -/
theorem finiteComplexQuotientGaussian_wilson_tilt_law
    (C : ExactOneComplex V E P) {β : ℝ} (hβ : 0 < β)
    (σ : EuclideanSpace ℝ P) :
    (finiteComplexQuotientGaussian C β hβ.le).tilted
        (fun a => finiteComplexQuotientTestFunctional C
          ⟨C.d₁.adjoint σ, adjoint_mem_coClosed C σ⟩ a / β) =
      Measure.map (fun a : FiniteGaugeQuotient C =>
        a + finiteComplexQuotientMap C (wilsonGaussianShift C σ))
        (finiteComplexQuotientGaussian C β hβ.le) := by
  let η : coClosed C := ⟨C.d₁.adjoint σ, adjoint_mem_coClosed C σ⟩
  let τ := wilsonGaussianShift C σ
  let q := finiteComplexQuotientMap C
  let S := finiteComplexCovarianceMatrix C β
  let base := ProbabilityTheory.multivariateGaussian
    (0 : EuclideanSpace ℝ E) S
  let μQ := finiteComplexQuotientGaussian C β hβ.le
  let qtest := finiteComplexQuotientTestFunctional C η
  let u : EuclideanSpace ℝ E := (β⁻¹) • (η : EuclideanSpace ℝ E)
  let g : FiniteGaugeQuotient C → ℝ := fun a => qtest a / β
  have hS : S.PosSemidef := finiteComplexCovarianceMatrix_posSemidef C hβ.le
  have hqtest (x : EuclideanSpace ℝ E) :
      qtest (q x) = inner ℝ (η : EuclideanSpace ℝ E) x := by
    have hcomp := finiteComplexQuotientTestFunctional_comp C η
    have hx := congrArg (fun L : StrongDual ℝ (EuclideanSpace ℝ E) => L x) hcomp
    simpa [q, qtest, ContinuousLinearMap.comp_apply,
      InnerProductSpace.toDualMap_apply_apply] using hx
  have hfactor (x : EuclideanSpace ℝ E) : g (q x) = inner ℝ u x := by
    rw [show g (q x) = qtest (q x) / β by rfl, hqtest]
    simp [u, real_inner_smul_left, div_eq_mul_inv]
    ring
  have hgaussianTilt : base.tilted (fun x => inner ℝ u x) =
      Measure.map (fun x : EuclideanSpace ℝ E => x + τ) base := by
    apply finiteGaussian_tilt_eq_map_add S hS u τ
    exact wilsonGaussianShift_covariance_vector C hβ σ
  letI : OpensMeasurableSpace (FiniteGaugeQuotient C) := ⟨by
    change MeasurableSpace.generateFrom
      {s : Set (FiniteGaugeQuotient C) | IsOpen s} ≤ _
    rw [MeasurableSpace.generateFrom_le_iff]
    intro s hs
    have hsopen : IsOpen s := by simpa only [Set.mem_ofPred_eq] using hs
    have hms : MeasurableSet s := by
      rw [measurableSet_quotient]
      exact ((finiteComplexQuotientMap C).continuous.isOpen_preimage
        s hsopen).measurableSet
    simpa only [Set.mem_ofPred_eq] using hms
  ⟩
  have hquotientMap : μQ = Measure.map q base := by
    simp [μQ, q, base, S, finiteComplexQuotientGaussian]
  have hqtestMeas : Measurable qtest := qtest.continuous.measurable
  have hg : Measurable g := hqtestMeas.div_const β
  have htiltMap : Measure.map q (base.tilted (fun x => g (q x))) =
      (Measure.map q base).tilted g :=
    map_tilted_eq_tilted_map (μ := base) q
      (finiteComplexQuotientMap_measurable C) g hg
  have hqmeas : Measurable q := finiteComplexQuotientMap_measurable C
  have hshiftMeas : Measurable (fun a : FiniteGaugeQuotient C => a + q τ) := by
    apply measurable_from_quotient.mpr
    change Measurable (fun x : EuclideanSpace ℝ E => q x + q τ)
    have hcomp : (fun x : EuclideanSpace ℝ E => q x + q τ) =
        q ∘ (fun x => x + τ) := by
      funext x
      exact q.map_add x τ
    rw [hcomp]
    exact hqmeas.comp (measurable_add_const τ)
  have hfactorFun : (fun x : EuclideanSpace ℝ E => g (q x)) =
      (fun x => inner ℝ u x) := funext hfactor
  change μQ.tilted g = Measure.map (fun a : FiniteGaugeQuotient C => a + q τ) μQ
  rw [hquotientMap]
  calc
    (Measure.map q base).tilted g =
        Measure.map q (base.tilted (fun x => g (q x))) := htiltMap.symm
    _ = Measure.map q (base.tilted (fun x => inner ℝ u x)) := by
      rw [hfactorFun]
    _ = Measure.map q (Measure.map (fun x : EuclideanSpace ℝ E => x + τ) base) :=
      congrArg (Measure.map q) hgaussianTilt
    _ = Measure.map (fun a : FiniteGaugeQuotient C =>
        a + q τ) (Measure.map q base) := by
      rw [Measure.map_map hqmeas (by fun_prop),
        Measure.map_map hshiftMeas hqmeas]
      congr 1
    _ = Measure.map (fun a : FiniteGaugeQuotient C =>
        a + finiteComplexQuotientMap C (wilsonGaussianShift C σ)) μQ := by
      change Measure.map (fun a : FiniteGaugeQuotient C => a + q τ)
        (Measure.map q base) = Measure.map (fun a => a + q τ) μQ
      exact congrArg (Measure.map (fun a : FiniteGaugeQuotient C => a + q τ))
        hquotientMap.symm

/-- The Hodge pairing is the squared norm of the exact part of the sheet. -/
theorem wilsonGaussianShift_hodge_pairing
    (C : ExactOneComplex V E P) (σ : EuclideanSpace ℝ P) :
    inner ℝ (C.d₁.adjoint σ) (wilsonGaussianShift C σ) =
      ‖C.d₁ (wilsonGaussianShift C σ)‖ ^ 2 := by
  let τ := wilsonGaussianShift C σ
  let ε := loopFieldResidual C σ
  have hdecomp : σ = C.d₁ τ + ε := by
    rw [show C.d₁ τ = σ - ε by
      simpa [τ, ε] using wilsonGaussianShift_curl C σ]
    abel
  have horth : inner ℝ ε (C.d₁ τ) = 0 := by
    exact loopFieldResidual_inner_exact C σ τ
  calc
    inner ℝ (C.d₁.adjoint σ) τ = inner ℝ σ (C.d₁ τ) :=
      LinearMap.adjoint_inner_left C.d₁ τ σ
    _ = inner ℝ (C.d₁ τ + ε) (C.d₁ τ) := by rw [← hdecomp]
    _ = ‖C.d₁ τ‖ ^ 2 := by
      simp [inner_add_left, horth]

/-- The normalizing exponential moment of the quotient tilt. -/
theorem finiteComplexQuotientGaussian_wilson_normalizer
    (C : ExactOneComplex V E P) {β : ℝ} (hβ : 0 < β)
    (σ : EuclideanSpace ℝ P) :
    (∫ a, Real.exp
      (finiteComplexQuotientTestFunctional C
        ⟨C.d₁.adjoint σ, adjoint_mem_coClosed C σ⟩ a / β)
      ∂finiteComplexQuotientGaussian C β hβ.le) =
      Real.exp (‖C.d₁ (wilsonGaussianShift C σ)‖ ^ 2 / (2 * β)) := by
  let η : coClosed C := ⟨C.d₁.adjoint σ, adjoint_mem_coClosed C σ⟩
  let q := finiteComplexQuotientMap C
  let S := finiteComplexCovarianceMatrix C β
  let base := ProbabilityTheory.multivariateGaussian
    (0 : EuclideanSpace ℝ E) S
  let μQ := finiteComplexQuotientGaussian C β hβ.le
  let qtest := finiteComplexQuotientTestFunctional C η
  let u : EuclideanSpace ℝ E := (β⁻¹) • (η : EuclideanSpace ℝ E)
  letI : OpensMeasurableSpace (FiniteGaugeQuotient C) := ⟨by
    change MeasurableSpace.generateFrom
      {s : Set (FiniteGaugeQuotient C) | IsOpen s} ≤ _
    rw [MeasurableSpace.generateFrom_le_iff]
    intro s hs
    have hsopen : IsOpen s := by simpa only [Set.mem_ofPred_eq] using hs
    have hms : MeasurableSet s := by
      rw [measurableSet_quotient]
      exact ((finiteComplexQuotientMap C).continuous.isOpen_preimage
        s hsopen).measurableSet
    simpa only [Set.mem_ofPred_eq] using hms
  ⟩
  have hS : S.PosSemidef := finiteComplexCovarianceMatrix_posSemidef C hβ.le
  have hquotientMap : μQ = Measure.map q base := by
    simp [μQ, q, base, S, finiteComplexQuotientGaussian]
  have hqtest (x : EuclideanSpace ℝ E) : qtest (q x) = inner ℝ
      (η : EuclideanSpace ℝ E) x := by
    have hcomp := finiteComplexQuotientTestFunctional_comp C η
    have hx := congrArg (fun L : StrongDual ℝ (EuclideanSpace ℝ E) => L x) hcomp
    simpa [q, qtest, ContinuousLinearMap.comp_apply,
      InnerProductSpace.toDualMap_apply_apply] using hx
  have hfactor (x : EuclideanSpace ℝ E) : qtest (q x) / β = inner ℝ u x := by
    rw [hqtest]
    simp [u, real_inner_smul_left, div_eq_mul_inv]
    ring
  have hdot : u.ofLp ⬝ᵥ S.mulVec u.ofLp = inner ℝ u
      (wilsonGaussianShift C σ) := by
    rw [← ProbabilityTheory.covarianceBilin_multivariateGaussian hS]
    exact wilsonGaussianShift_covariance_vector C hβ σ u
  have hpair := wilsonGaussianShift_hodge_pairing C σ
  have hscaledPair : inner ℝ u (wilsonGaussianShift C σ) =
      β⁻¹ * ‖C.d₁ (wilsonGaussianShift C σ)‖ ^ 2 := by
    change inner ℝ ((β⁻¹) • C.d₁.adjoint σ)
      (wilsonGaussianShift C σ) = _
    rw [real_inner_smul_left, hpair]
  have hmoment : ProbabilityTheory.mgf (fun x : EuclideanSpace ℝ E => inner ℝ u x)
      base 1 = Real.exp (u.ofLp ⬝ᵥ S.mulVec u.ofLp / 2) := by
    simpa [base, S, ProbabilityTheory.mgf] using
      Gaussian.finiteGaussianAdapter_mgf_inner S hS u 1
  have hqmeas : Measurable q := finiteComplexQuotientMap_measurable C
  have hqtestMeas : Measurable qtest := qtest.continuous.measurable
  have hExpoMeas : Measurable (fun a => Real.exp (qtest a / β)) := by
    fun_prop
  have hExpoAES : AEStronglyMeasurable (fun a => Real.exp (qtest a / β))
      (Measure.map q base) := hExpoMeas.aestronglyMeasurable
  change (∫ a, Real.exp (qtest a / β) ∂μQ) = _
  rw [hquotientMap]
  calc
    (∫ a, Real.exp (qtest a / β) ∂Measure.map q base) =
        ∫ x, Real.exp (inner ℝ u x) ∂base := by
          rw [MeasureTheory.integral_map hqmeas.aemeasurable hExpoAES]
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with x
          rw [hfactor]
    _ = ProbabilityTheory.mgf (fun x : EuclideanSpace ℝ E => inner ℝ u x) base 1 := by
          simp [ProbabilityTheory.mgf]
    _ = Real.exp (u.ofLp ⬝ᵥ S.mulVec u.ofLp / 2) := hmoment
    _ = Real.exp (‖C.d₁ (wilsonGaussianShift C σ)‖ ^ 2 / (2 * β)) := by
          rw [hdot]
          rw [hscaledPair]
          congr 1
          field_simp [ne_of_gt hβ]

/-- Pythagoras for the exact and loop parts of the Wilson sheet. -/
theorem wilsonGaussianShift_norm_decomposition
    (C : ExactOneComplex V E P) (σ : EuclideanSpace ℝ P) :
    ‖σ‖ ^ 2 = ‖C.d₁ (wilsonGaussianShift C σ)‖ ^ 2 +
      ‖loopFieldResidual C σ‖ ^ 2 := by
  let τ := wilsonGaussianShift C σ
  let ε := loopFieldResidual C σ
  have hdecomp : σ = C.d₁ τ + ε := by
    rw [show C.d₁ τ = σ - ε by
      simpa [τ, ε] using wilsonGaussianShift_curl C σ]
    abel
  have horth : inner ℝ (C.d₁ τ) ε = 0 := by
    rw [real_inner_comm]
    exact loopFieldResidual_inner_exact C σ τ
  calc
    ‖σ‖ ^ 2 = ‖C.d₁ τ + ε‖ ^ 2 := by rw [hdecomp]
    _ = ‖C.d₁ τ‖ ^ 2 + ‖ε‖ ^ 2 := by
      simpa only [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_real horth

/-- Finite-volume Cameron--Martin formula on the gauge quotient. The source
linear functional is the quotient representative of `(d₁ α, σ)`. The stated
integrability hypothesis is on the translated observable; it implies the
weighted integrability needed on the left for arbitrary unbounded `F`. -/
theorem finiteComplexQuotientGaussian_wilson_shift_integral
    (C : ExactOneComplex V E P) {β : ℝ} (hβ : 0 < β)
    (σ : EuclideanSpace ℝ P) (F : FiniteGaugeQuotient C → ℂ)
    (hF : Integrable F (Measure.map
      (fun a : FiniteGaugeQuotient C => a +
        finiteComplexQuotientMap C (wilsonGaussianShift C σ))
      (finiteComplexQuotientGaussian C β hβ.le))) :
    (∫ a, F a *
      (Real.exp (finiteComplexQuotientTestFunctional C
        ⟨C.d₁.adjoint σ, adjoint_mem_coClosed C σ⟩ a / β) : ℂ) *
      (Real.exp (-‖σ‖ ^ 2 / (2 * β)) : ℂ)
      ∂finiteComplexQuotientGaussian C β hβ.le) =
    (Real.exp (-‖loopFieldResidual C σ‖ ^ 2 / (2 * β)) : ℂ) *
      ∫ a, F (a + finiteComplexQuotientMap C
        (wilsonGaussianShift C σ)) ∂finiteComplexQuotientGaussian C β hβ.le := by
  let η : coClosed C := ⟨C.d₁.adjoint σ, adjoint_mem_coClosed C σ⟩
  let τ := wilsonGaussianShift C σ
  let q := finiteComplexQuotientMap C
  let S := finiteComplexCovarianceMatrix C β
  let base := ProbabilityTheory.multivariateGaussian
    (0 : EuclideanSpace ℝ E) S
  let μQ := finiteComplexQuotientGaussian C β hβ.le
  let qtest := finiteComplexQuotientTestFunctional C η
  let u : EuclideanSpace ℝ E := (β⁻¹) • (η : EuclideanSpace ℝ E)
  let g : FiniteGaugeQuotient C → ℝ := fun a => qtest a / β
  let shift : FiniteGaugeQuotient C → FiniteGaugeQuotient C := fun a => a + q τ
  let cost : ℝ := Real.exp (-‖σ‖ ^ 2 / (2 * β))
  let Z : ℝ := ∫ a, Real.exp (g a) ∂μQ
  have hS : S.PosSemidef := finiteComplexCovarianceMatrix_posSemidef C hβ.le
  letI : OpensMeasurableSpace (FiniteGaugeQuotient C) := ⟨by
    change MeasurableSpace.generateFrom
      {s : Set (FiniteGaugeQuotient C) | IsOpen s} ≤ _
    rw [MeasurableSpace.generateFrom_le_iff]
    intro s hs
    have hsopen : IsOpen s := by simpa only [Set.mem_ofPred_eq] using hs
    have hms : MeasurableSet s := by
      rw [measurableSet_quotient]
      exact ((finiteComplexQuotientMap C).continuous.isOpen_preimage
        s hsopen).measurableSet
    simpa only [Set.mem_ofPred_eq] using hms
  ⟩
  have hquotientMap : μQ = Measure.map q base := by
    simp [μQ, q, base, S, finiteComplexQuotientGaussian]
  have hqtest (x : EuclideanSpace ℝ E) : qtest (q x) =
      inner ℝ (η : EuclideanSpace ℝ E) x := by
    have hcomp := finiteComplexQuotientTestFunctional_comp C η
    have hx := congrArg (fun L : StrongDual ℝ (EuclideanSpace ℝ E) => L x) hcomp
    simpa [q, qtest, ContinuousLinearMap.comp_apply,
      InnerProductSpace.toDualMap_apply_apply] using hx
  have hfactor (x : EuclideanSpace ℝ E) : g (q x) = inner ℝ u x := by
    rw [show g (q x) = qtest (q x) / β by rfl, hqtest]
    simp [u, real_inner_smul_left, div_eq_mul_inv]
    ring
  have hqmeas : Measurable q := finiteComplexQuotientMap_measurable C
  have hqtestMeas : Measurable qtest := qtest.continuous.measurable
  have hg : Measurable g := hqtestMeas.div_const β
  have hExpoMeas : Measurable (fun a => Real.exp (g a)) := by fun_prop
  have hExpoAES : AEStronglyMeasurable (fun a => Real.exp (g a))
      (Measure.map q base) := hExpoMeas.aestronglyMeasurable
  have hquotientExpIntegrable : Integrable (fun a => Real.exp (g a)) μQ := by
    rw [hquotientMap]
    have hbaseExp := multivariateGaussian_exp_inner_integrable S hS u
    have hcomp : Integrable (fun x : EuclideanSpace ℝ E => Real.exp (g (q x))) base := by
      convert hbaseExp using 1
      ext x
      rw [hfactor]
    exact (integrable_map_measure hExpoAES hqmeas.aemeasurable).mpr hcomp
  have htilt : μQ.tilted g = Measure.map shift μQ := by
    dsimp [shift, g, qtest, μQ, q, base, S]
    exact finiteComplexQuotientGaussian_wilson_tilt_law C hβ σ
  have hFtilt : Integrable F (μQ.tilted g) := by
    rw [htilt]
    exact hF
  have hnormalizer : Z = Real.exp (‖C.d₁ τ‖ ^ 2 / (2 * β)) := by
    simpa [Z, τ] using finiteComplexQuotientGaussian_wilson_normalizer C hβ σ
  have hZpos : 0 < Z := by rw [hnormalizer]; exact Real.exp_pos _
  have hWeighted : Integrable (fun a => Real.exp (g a) • F a) μQ :=
    (MeasureTheory.integrable_tilted_iff hquotientExpIntegrable F).mp hFtilt
  have hweightedComplex : Integrable
      (fun a => (Real.exp (g a) : ℂ) * F a) μQ := by
    simpa [smul_eq_mul, mul_comm] using hWeighted
  have hratioInt :
      (∫ a, ((Real.exp (g a) / Z : ℝ) : ℂ) * F a ∂μQ) =
        ∫ a, (Real.exp (g a) / (∫ x, Real.exp (g x) ∂μQ)) • F a ∂μQ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with a
    simp [Complex.ofReal_div, Z]
  have hscale : (∫ a, F a * (Real.exp (g a) : ℂ) ∂μQ) =
      (Z : ℂ) * ∫ a, F a ∂μQ.tilted g := by
    have hpoint (a : FiniteGaugeQuotient C) :
        F a * (Real.exp (g a) : ℂ) =
          (((Real.exp (g a) / Z : ℝ) : ℂ) * F a) * (Z : ℂ) := by
      rw [Complex.ofReal_div]
      field_simp [ne_of_gt hZpos]
    calc
      (∫ a, F a * (Real.exp (g a) : ℂ) ∂μQ) =
          ∫ a, (((Real.exp (g a) / Z : ℝ) : ℂ) * F a) * (Z : ℂ) ∂μQ := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with a
            exact hpoint a
      _ = (∫ a, ((Real.exp (g a) / Z : ℝ) : ℂ) * F a ∂μQ) * (Z : ℂ) :=
            MeasureTheory.integral_mul_const (Z : ℂ) _
      _ = (∫ a, F a ∂μQ.tilted g) * (Z : ℂ) := by
            rw [hratioInt, ← MeasureTheory.integral_tilted g F]
      _ = (Z : ℂ) * ∫ a, F a ∂μQ.tilted g := by ring
  have hshiftMeas : Measurable shift := by
    apply measurable_from_quotient.mpr
    change Measurable (fun x : EuclideanSpace ℝ E => q x + q τ)
    have hcomp : (fun x : EuclideanSpace ℝ E => q x + q τ) =
        q ∘ (fun x => x + τ) := by
      funext x
      exact q.map_add x τ
    rw [hcomp]
    exact hqmeas.comp (measurable_add_const τ)
  have hFmapIntegral : ∫ a, F a ∂μQ.tilted g =
      ∫ a, F (shift a) ∂μQ := by
    rw [htilt]
    exact MeasureTheory.integral_map hshiftMeas.aemeasurable hF.aestronglyMeasurable
  have hcost : cost * Real.exp (‖C.d₁ τ‖ ^ 2 / (2 * β)) =
      Real.exp (-‖loopFieldResidual C σ‖ ^ 2 / (2 * β)) := by
    dsimp [cost]
    rw [← Real.exp_add]
    congr 1
    rw [wilsonGaussianShift_norm_decomposition C σ]
    field_simp [ne_of_gt hβ]
    ring
  change (∫ a, F a * (Real.exp (g a) : ℂ) * (cost : ℂ) ∂μQ) = _
  calc
    (∫ a, F a * (Real.exp (g a) : ℂ) * (cost : ℂ) ∂μQ) =
        (cost : ℂ) * ∫ a, F a * (Real.exp (g a) : ℂ) ∂μQ := by
          rw [MeasureTheory.integral_mul_const]
          ring
    _ = (cost : ℂ) * ((Z : ℂ) * ∫ a, F a ∂μQ.tilted g) := by rw [hscale]
    _ = (Real.exp (-‖loopFieldResidual C σ‖ ^ 2 / (2 * β)) : ℂ) *
        ∫ a, F a ∂μQ.tilted g := by
          have hcoeff : cost * Z =
              Real.exp (-‖loopFieldResidual C σ‖ ^ 2 / (2 * β)) := by
            rw [hnormalizer]
            exact hcost
          rw [← mul_assoc, ← Complex.ofReal_mul, hcoeff]
    _ = (Real.exp (-‖loopFieldResidual C σ‖ ^ 2 / (2 * β)) : ℂ) *
        ∫ a, F (a + q τ) ∂μQ := by rw [hFmapIntegral]

/-- The Wilson Gaussian disorder expectation, obtained by taking `F = 1` in
the quotient translation identity. -/
theorem finiteComplexQuotientGaussian_wilson_expectation
    (C : ExactOneComplex V E P) {β : ℝ} (hβ : 0 < β)
    (σ : EuclideanSpace ℝ P) :
    (∫ a, Real.exp
      (finiteComplexQuotientTestFunctional C
        ⟨C.d₁.adjoint σ, adjoint_mem_coClosed C σ⟩ a / β) *
      Real.exp (-‖σ‖ ^ 2 / (2 * β))
      ∂finiteComplexQuotientGaussian C β hβ.le) =
      Real.exp (-‖loopFieldResidual C σ‖ ^ 2 / (2 * β)) := by
  let η : coClosed C := ⟨C.d₁.adjoint σ, adjoint_mem_coClosed C σ⟩
  let q := finiteComplexQuotientMap C
  let μQ := finiteComplexQuotientGaussian C β hβ.le
  let shift : FiniteGaugeQuotient C → FiniteGaugeQuotient C := fun a =>
    a + q (wilsonGaussianShift C σ)
  let g : FiniteGaugeQuotient C → ℝ := fun a =>
    (finiteComplexQuotientTestFunctional C η a) / β
  let cost : ℝ := Real.exp (-‖σ‖ ^ 2 / (2 * β))
  letI : IsProbabilityMeasure μQ := finiteComplexQuotientGaussian_is_probability C hβ.le
  letI : IsProbabilityMeasure (Measure.map shift μQ) := inferInstance
  have hF : Integrable (fun _ : FiniteGaugeQuotient C => (1 : ℂ))
      (Measure.map shift μQ) := integrable_const _
  have hmain := finiteComplexQuotientGaussian_wilson_shift_integral C hβ σ
    (fun _ => (1 : ℂ)) hF
  have hcomplex :
      (∫ a, ((Real.exp (g a) * cost : ℝ) : ℂ) ∂μQ) =
        (Real.exp (-‖loopFieldResidual C σ‖ ^ 2 / (2 * β)) : ℂ) := by
    simpa [g, cost, η, q, μQ, one_mul, Complex.ofReal_mul] using hmain
  have hcast :
      (↑(∫ a, Real.exp (g a) * cost ∂μQ) : ℂ) =
        (Real.exp (-‖loopFieldResidual C σ‖ ^ 2 / (2 * β)) : ℂ) := by
    simpa only [integral_complex_ofReal] using hcomplex
  exact Complex.ofReal_injective hcast


end WilsonDecomposition


end FroehlichSpencer.FS82.Wilson

end
