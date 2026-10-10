/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.LatticeComplex
public import FroehlichSpencer.FS82.Moment.GaugeCharacter
public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Gauge-averaged Gaussian on the physical link torus

The source current is represented in the cubical orientation.

Its Fourier mode
on the physical link torus includes integer orientation twist.

The gauge
field is the integer-incidence coboundary of a Haar-uniform vertex torus field.
-/

@[expose] public section

set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

namespace FroehlichSpencer.FS82.Gaussian.GaugeAveraged

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Moment.SourceCoercivity
open FroehlichSpencer.FS82.Moment.GaugeCharacter
open FroehlichSpencer.FS82.Moment.PhysicalGaugeCurrent

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

open Matrix
open scoped MatrixOrder

private theorem stdGaussian_complexLinearTransform
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


private theorem stdGaussian_inner_complexTransform
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
private theorem multivariateGaussian_inner_complexTransform
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


variable {B : Box 4}

/-- Vertex fields modulo integer shifts. -/
abbrev VertexTorus := UnitAddTorus (SourceDualZeroCells B)


/--
The integer incidence coefficient of the physical coboundary.

It is obtained by applying the integer cubical boundary after the primal-dual
star, followed by the source-to-lattice orientation sign.
-/
noncomputable def latticeGaugeIncidence (v : SourceDualZeroCells B)
    (e : SourceDualOneCells B) : ℤ :=
  sourceDualT e * boundary (basisChain (primalDualCellEquiv.symm v.1))
    (primalDualCellEquiv.symm e.1)

/--
The source current's physical integer frequency is its orientation
sign twist.
-/
def latticePhysicalMode (j : IntegerCurrent B) : SourceDualOneCells B → ℤ :=
  fun e => sourceDualT e * j e


/-- Normalized Haar probability on the compact vertex gauge torus. -/
noncomputable def vertexTorusHaar : Measure (VertexTorus (B := B)) :=
  Measure.pi (fun _ : SourceDualZeroCells B => AddCircle.haarAddCircle)

theorem vertexTorusHaar_is_probability :
    IsProbabilityMeasure (vertexTorusHaar (B := B)) := by
  unfold vertexTorusHaar
  infer_instance

theorem latticeGaugeIncidence_cast (v : SourceDualZeroCells B)
    (e : SourceDualOneCells B) :
    (latticeGaugeIncidence v e : ℝ) =
      (latticeExactOneComplex (B := B) Cubical.originZero).d₀
        (EuclideanSpace.single v 1) e := by
  classical
  rw [latticeGaugeIncidence, latticeExactOneComplex,
    LinearMap.comp_apply, sourceDualTLinear_apply,
    sourceDualD₀_coefficient]
  simp only [sourceDualZeroToChain, LinearMap.comp_apply,
    euclideanToFinsupp_single,
    embedDualSubtype_apply_single]
  rw [Int.cast_mul, sourceDualT_cast_eq_orientationSign]
  rw [Cubical.dualExteriorDifference]
  simp [starMap, starMapInverse, realBoundary, realifyLinearMap,
    basisChain, Finsupp.equivMapDomain_apply,
    sourceDualZeroEmbedding, sourceDualOneEmbedding]
  left
  simp [castIntegerChain]


theorem haarAddCircle_fourier_integral (n : ℤ) :
    ∫ x : AddCircle (1 : ℝ), fourier n x ∂AddCircle.haarAddCircle =
      if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [ite_eq_right hn]
    apply integral_eq_zero_of_add_right_eq_neg
    intro x
    exact fourier_add_half_inv_index hn (by norm_num) x

theorem vertexTorusHaar_mFourier_integral
    (n : SourceDualZeroCells B → ℤ) :
    ∫ u : VertexTorus (B := B), UnitAddTorus.mFourier n u
        ∂vertexTorusHaar (B := B) = if n = 0 then 1 else 0 := by
  classical
  change ∫ u : VertexTorus (B := B),
      ∏ v : SourceDualZeroCells B, fourier (n v) (u v)
        ∂Measure.pi (fun _ : SourceDualZeroCells B => AddCircle.haarAddCircle) = _
  rw [integral_fintype_prod_eq_prod]
  by_cases hn : n = 0
  · subst n
    simp [integral_const]
  · rw [ite_eq_right hn]
    obtain ⟨v, hv⟩ := Function.ne_iff.mp hn
    have hzero :
        ∫ x : AddCircle (1 : ℝ), fourier (n v) x
            ∂AddCircle.haarAddCircle = 0 := by
      rw [haarAddCircle_fourier_integral]
      have hnv : n v ≠ 0 := by simpa using hv
      simp [hnv]
    rw [Finset.prod_eq_zero (Finset.mem_univ v) hzero]


noncomputable def latticeIntegerModeVector (j : IntegerCurrent B) :
    EuclideanSpace ℝ (SourceDualOneCells B) :=
  WithLp.toLp 2 (fun e => ((latticePhysicalMode (B := B) j e : ℤ) : ℝ))

noncomputable def latticeGaugeFrequency (j : IntegerCurrent B)
    (v : SourceDualZeroCells B) : ℤ :=
  ∑ e : SourceDualOneCells B,
    latticePhysicalMode (B := B) j e * latticeGaugeIncidence v e

theorem latticeIntegerModeVector_apply (j : IntegerCurrent B)
    (e : SourceDualOneCells B) :
    latticeIntegerModeVector (B := B) j e =
      ((latticePhysicalMode (B := B) j e : ℤ) : ℝ) := rfl

theorem latticeGaugeFrequency_cast_eq_adjoint (j : IntegerCurrent B)
    (v : SourceDualZeroCells B) :
    ((latticeGaugeFrequency (B := B) j v : ℤ) : ℝ) =
      (latticeExactOneComplex (B := B) Cubical.originZero).d₀.adjoint
        (latticeIntegerModeVector (B := B) j) v := by
  classical
  let C := latticeExactOneComplex (B := B) Cubical.originZero
  let q := latticeIntegerModeVector (B := B) j
  have hcoord (e : SourceDualOneCells B) :
      C.d₀ (EuclideanSpace.single v 1) e =
        (latticeGaugeIncidence v e : ℝ) := by
    simpa [C] using (latticeGaugeIncidence_cast (B := B) v e).symm
  calc
    ((latticeGaugeFrequency (B := B) j v : ℤ) : ℝ) =
        ∑ e : SourceDualOneCells B,
          ((latticePhysicalMode (B := B) j e : ℤ) : ℝ) *
            (latticeGaugeIncidence v e : ℝ) := by
          rw [latticeGaugeFrequency, Int.cast_sum]
          apply Finset.sum_congr rfl
          intro e he
          rw [Int.cast_mul]
    _ = inner ℝ (C.d₀ (EuclideanSpace.single v 1)) q := by
          rw [PiLp.inner_apply]
          simp only [Real.inner_apply, q, latticeIntegerModeVector_apply]
          apply Finset.sum_congr rfl
          intro e he
          rw [hcoord]
          ring_nf
    _ = inner ℝ (EuclideanSpace.single v 1) (C.d₀.adjoint q) :=
          (LinearMap.adjoint_inner_right C.d₀ (EuclideanSpace.single v 1) q).symm
    _ = C.d₀.adjoint q v := by
          rw [EuclideanSpace.inner_single_left]
          simp

theorem latticeIntegerModeVector_eq_orientedSourceVector
    (j : IntegerCurrent B) :
    latticeIntegerModeVector (B := B) j =
      sourceDualTLinear (sourceRealLinkVector (B := B) j) := by
  ext e
  simp [latticeIntegerModeVector_apply, latticePhysicalMode,
    sourceDualTLinear_apply, sourceRealLinkVector_apply,
    sourceDualT_cast_eq_orientationSign]

theorem latticeGaugeFrequency_cast_eq_currentDivergence
    (j : IntegerCurrent B) (v : SourceDualZeroCells B) :
    ((latticeGaugeFrequency (B := B) j v : ℤ) : ℝ) =
      (currentDivergence j v : ℝ) := by
  let C := latticeExactOneComplex (B := B) Cubical.originZero
  let q := latticeIntegerModeVector (B := B) j
  have hD0 : currentDivergence j v = inner ℝ
      (sourceDualD₀ (B := B) (EuclideanSpace.single v (1 : ℝ)))
        (sourceRealLinkVector (B := B) j) := by
    rw [currentDivergence_eq_D0_inner]
    congr 1
    ext e
    simp [sourceRealLinkVector_apply]
  have hC : C.d₀ (EuclideanSpace.single v (1 : ℝ)) =
      sourceDualTLinear (sourceDualD₀ (B := B)
        (EuclideanSpace.single v (1 : ℝ))) := by
    simp [C, latticeExactOneComplex]
  have hT (a b : EuclideanSpace ℝ (SourceDualOneCells B)) :
      inner ℝ (sourceDualTLinear a) (sourceDualTLinear b) =
        inner ℝ a b := by
    calc
      inner ℝ (sourceDualTLinear a) (sourceDualTLinear b) =
          inner ℝ a (sourceDualTLinear (sourceDualTLinear b)) :=
        sourceDualTLinear_symmetric a (sourceDualTLinear b)
      _ = inner ℝ a b := by rw [sourceDualTLinear_apply_apply]
  have hpair : inner ℝ (C.d₀ (EuclideanSpace.single v (1 : ℝ))) q =
      currentDivergence j v := by
    rw [hC, show q = sourceDualTLinear (sourceRealLinkVector (B := B) j) by
      exact latticeIntegerModeVector_eq_orientedSourceVector (B := B) j]
    rw [hT, hD0]
  calc
    ((latticeGaugeFrequency (B := B) j v : ℤ) : ℝ) =
        C.d₀.adjoint q v := latticeGaugeFrequency_cast_eq_adjoint (B := B) j v
    _ = inner ℝ (C.d₀ (EuclideanSpace.single v (1 : ℝ))) q := by
        calc
          C.d₀.adjoint q v =
              inner ℝ (EuclideanSpace.single v (1 : ℝ)) (C.d₀.adjoint q) := by
                rw [EuclideanSpace.inner_single_left]
                simp
          _ = inner ℝ (C.d₀ (EuclideanSpace.single v (1 : ℝ))) q :=
                LinearMap.adjoint_inner_right _ _ _
    _ = (currentDivergence j v : ℝ) := by rw [hpair]

theorem latticeGaugeFrequency_zero_iff_currentDivergence_zero
    (j : IntegerCurrent B) :
    latticeGaugeFrequency (B := B) j = 0 ↔ currentDivergence j = 0 := by
  constructor
  · intro h
    funext v
    have hv : ((latticeGaugeFrequency (B := B) j v : ℤ) : ℝ) = 0 := by
      rw [h]
      simp
    rw [latticeGaugeFrequency_cast_eq_currentDivergence] at hv
    exact_mod_cast hv
  · intro h
    funext v
    have hv : ((latticeGaugeFrequency (B := B) j v : ℤ) : ℝ) = 0 := by
      rw [latticeGaugeFrequency_cast_eq_currentDivergence]
      exact_mod_cast congrFun h v
    exact_mod_cast hv

theorem latticeIntegerModeVector_mem_coClosed_iff_frequency_zero
    (j : IntegerCurrent B) :
    latticeIntegerModeVector (B := B) j ∈
        coClosed (latticeExactOneComplex (B := B) Cubical.originZero) ↔
      latticeGaugeFrequency (B := B) j = 0 := by
  classical
  rw [coClosed, LinearMap.mem_ker]
  constructor
  · intro h
    funext v
    have hv :
        ((latticeGaugeFrequency (B := B) j v : ℤ) : ℝ) = 0 := by
      rw [latticeGaugeFrequency_cast_eq_adjoint]
      have hval := congrArg (fun f : EuclideanSpace ℝ
          (SourceDualZeroCells B) => f v) h
      simpa using hval
    exact_mod_cast hv
  · intro h
    ext v
    rw [← latticeGaugeFrequency_cast_eq_adjoint, h]
    simp

/-- The physical finite complex used for the gauge average. -/
noncomputable abbrev physicalComplex :=
  latticeExactOneComplex (B := B) Cubical.originZero

/--
A centered Gaussian sample on the co-closed physical link subspace.

Its
ambient covariance is the β-scaled covariance, projected to `W`.
-/
noncomputable def coClosedGaussian (β : ℝ) (_hβ : 0 ≤ β) :
    Measure (coClosed (physicalComplex (B := B))) := by
  letI : (finiteComplexCovarianceMatrix
      (physicalComplex (B := B)) β).PosSemidef :=
    finiteComplexCovarianceMatrix_posSemidef _ _hβ
  exact Measure.map
    (finiteComplexCoClosedProjection (physicalComplex (B := B)))
    (multivariateGaussian 0
      (finiteComplexCovarianceMatrix (physicalComplex (B := B)) β))

theorem coClosedGaussian_is_probability (β : ℝ) (hβ : 0 ≤ β) :
    IsProbabilityMeasure (coClosedGaussian (B := B) β hβ) := by
  unfold coClosedGaussian
  let C := physicalComplex (B := B)
  have hS : (finiteComplexCovarianceMatrix C β).PosSemidef :=
    finiteComplexCovarianceMatrix_posSemidef C hβ
  have hbase : IsProbabilityMeasure
      (multivariateGaussian 0 (finiteComplexCovarianceMatrix C β)) := by
    rw [multivariateGaussian]
    infer_instance
  have hmeas : Measurable (finiteComplexCoClosedProjection C) := by
    exact (finiteComplexCoClosedProjection C).continuous_of_finiteDimensional.measurable
  constructor
  rw [Measure.map_apply hmeas MeasurableSet.univ]
  simp

theorem coClosedGaussian_is_gaussian (β : ℝ) (hβ : 0 ≤ β) :
    ProbabilityTheory.IsGaussian (coClosedGaussian (B := B) β hβ) := by
  let C := physicalComplex (B := B)
  let P : EuclideanSpace ℝ (SourceDualOneCells B) →L[ℝ] coClosed C :=
    (finiteComplexCoClosedProjection C).toContinuousLinearMap
  let base := multivariateGaussian 0 (finiteComplexCovarianceMatrix C β)
  have hS : (finiteComplexCovarianceMatrix C β).PosSemidef :=
    finiteComplexCovarianceMatrix_posSemidef C hβ
  have hbase : ProbabilityTheory.IsGaussian base := by
    dsimp [base]
    letI : (finiteComplexCovarianceMatrix C β).PosSemidef := hS
    infer_instance
  have hP : Measurable P := by
    exact (finiteComplexCoClosedProjection C).continuous_of_finiteDimensional.measurable
  change ProbabilityTheory.IsGaussian (Measure.map P base)
  exact ProbabilityTheory.isGaussian_map_of_measurable hP


private theorem physicalAmbientGaussian_covarianceBilin (β : ℝ)
    (hβ : 0 ≤ β)
    (u v : EuclideanSpace ℝ (SourceDualOneCells B)) :
    ProbabilityTheory.covarianceBilin
        (multivariateGaussian 0
          (finiteComplexCovarianceMatrix (physicalComplex (B := B)) β)) u v =
      inner ℝ u ((β • finiteComplexAmbientCovariance
        (physicalComplex (B := B))) v) := by
  let C := physicalComplex (B := B)
  let T := β • finiteComplexAmbientCovariance C
  let S := finiteComplexCovarianceMatrix C β
  have hS : S.PosSemidef := finiteComplexCovarianceMatrix_posSemidef C hβ
  rw [ProbabilityTheory.covarianceBilin_multivariateGaussian hS]
  calc
    u.ofLp ⬝ᵥ S.mulVec v.ofLp = u.ofLp ⬝ᵥ (T v).ofLp := by
      simp [S, T, finiteComplexCovarianceMatrix,
        Gaussian.matrixOfLinearMap_mulVec]
    _ = inner ℝ u (T v) := by
      simp [PiLp.inner_apply, dotProduct, mul_comm]


private theorem coClosedGaussian_complexTransform (β : ℝ) (hβ : 0 ≤ β)
    (u v : coClosed (physicalComplex (B := B))) :
    ∫ x : coClosed (physicalComplex (B := B)),
      Complex.exp ((inner ℝ u x : ℝ) + Complex.I * (inner ℝ v x : ℝ))
        ∂coClosedGaussian (B := B) β hβ =
      Complex.exp ((((ProbabilityTheory.covarianceBilin
          (multivariateGaussian 0 (finiteComplexCovarianceMatrix
            (physicalComplex (B := B)) β)) (u : _) (u : _) : ℝ) -
        ProbabilityTheory.covarianceBilin
          (multivariateGaussian 0 (finiteComplexCovarianceMatrix
            (physicalComplex (B := B)) β)) (v : _) (v : _) : ℝ) +
        2 * Complex.I * ProbabilityTheory.covarianceBilin
          (multivariateGaussian 0 (finiteComplexCovarianceMatrix
            (physicalComplex (B := B)) β)) (u : _) (v : _)) / 2) := by
  let C := physicalComplex (B := B)
  let P : EuclideanSpace ℝ (SourceDualOneCells B) →L[ℝ] coClosed C :=
    (finiteComplexCoClosedProjection C).toContinuousLinearMap
  let base := multivariateGaussian 0 (finiteComplexCovarianceMatrix C β)
  have hS : (finiteComplexCovarianceMatrix C β).PosSemidef :=
    finiteComplexCovarianceMatrix_posSemidef C hβ
  let f : coClosed C → ℂ := fun x =>
    Complex.exp ((inner ℝ u x : ℝ) + Complex.I * (inner ℝ v x : ℝ))
  have hfmeas : Measurable f := by
    fun_prop
  have hPmeas : Measurable P :=
    (finiteComplexCoClosedProjection C).continuous_of_finiteDimensional.measurable
  have hu (y : EuclideanSpace ℝ (SourceDualOneCells B)) :
      inner ℝ u (P y) = inner ℝ (u : EuclideanSpace ℝ (SourceDualOneCells B)) y := by
    change inner ℝ u ((coClosed C).orthogonalProjectionOnto y) = _
    exact (coClosed C).inner_orthogonalProjectionOnto_eq_of_mem_left u y
  have hv (y : EuclideanSpace ℝ (SourceDualOneCells B)) :
      inner ℝ v (P y) = inner ℝ (v : EuclideanSpace ℝ (SourceDualOneCells B)) y := by
    change inner ℝ v ((coClosed C).orthogonalProjectionOnto y) = _
    exact (coClosed C).inner_orthogonalProjectionOnto_eq_of_mem_left v y
  haveI : (finiteComplexCovarianceMatrix C β).PosSemidef := hS
  calc
    ∫ x : coClosed C, f x ∂coClosedGaussian (B := B) β hβ =
      ∫ y : EuclideanSpace ℝ (SourceDualOneCells B), f (P y) ∂base := by
        change ∫ x : coClosed C, f x ∂Measure.map P base = _
        exact MeasureTheory.integral_map hPmeas.aemeasurable
          hfmeas.aestronglyMeasurable
    _ = ∫ y : EuclideanSpace ℝ (SourceDualOneCells B),
        Complex.exp ((inner ℝ (u : EuclideanSpace ℝ
          (SourceDualOneCells B)) y : ℝ) + Complex.I *
            (inner ℝ (v : EuclideanSpace ℝ (SourceDualOneCells B)) y : ℝ))
          ∂base := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with y
            simp only [f]
            rw [hu, hv]
    _ = _ := by
        simpa [base, C] using
          multivariateGaussian_inner_complexTransform
            (finiteComplexCovarianceMatrix C β) hS
            (u : EuclideanSpace ℝ (SourceDualOneCells B))
            (v : EuclideanSpace ℝ (SourceDualOneCells B))

private theorem coClosedGaussian_realExp_integrable
    (β : ℝ) (hβ : 0 ≤ β)
    (u : coClosed (physicalComplex (B := B))) :
    Integrable (fun x : coClosed (physicalComplex (B := B)) =>
      Real.exp (inner ℝ u x)) (coClosedGaussian (B := B) β hβ) := by
  let W := coClosed (physicalComplex (B := B))
  let μ := coClosedGaussian (B := B) β hβ
  let L : StrongDual ℝ W := InnerProductSpace.toDualMap ℝ W u
  haveI : ProbabilityTheory.IsGaussian μ := coClosedGaussian_is_gaussian β hβ
  have hL : Measurable L := L.continuous.measurable
  have hpush : Measure.map L μ = ProbabilityTheory.gaussianReal
      (∫ x, L x ∂μ) (ProbabilityTheory.variance L μ).toNNReal :=
    ProbabilityTheory.IsGaussian.map_eq_gaussianReal L
  have hexp : Integrable (fun y : ℝ => Real.exp y) (Measure.map L μ) := by
    rw [hpush]
    simpa using ProbabilityTheory.integrable_exp_mul_gaussianReal
      (μ := ∫ x, L x ∂μ) (v := (ProbabilityTheory.variance L μ).toNNReal) 1
  have hreal : Integrable (fun x : W => Real.exp (inner ℝ u x)) μ := by
    have hmeas : AEStronglyMeasurable (fun y : ℝ => Real.exp y)
        (Measure.map L μ) := by fun_prop
    have hcomp := (MeasureTheory.integrable_map_measure hmeas
      hL.aemeasurable).mp hexp
    have hLx (x : W) : L x = inner ℝ u x := by
      simp [L, InnerProductSpace.toDualMap_apply_apply (𝕜 := ℝ)]
    convert hcomp using 1
    ext x
    simp [hLx]
  exact hreal

private theorem coClosedGaussian_complexLinear_integrable
    (β : ℝ) (hβ : 0 ≤ β)
    (u v : coClosed (physicalComplex (B := B))) :
    Integrable (fun x : coClosed (physicalComplex (B := B)) =>
      Complex.exp ((inner ℝ u x : ℝ) + Complex.I * (inner ℝ v x : ℝ)))
      (coClosedGaussian (B := B) β hβ) := by
  have hreal := coClosedGaussian_realExp_integrable (B := B) β hβ u
  apply Integrable.mono' hreal
  · fun_prop
  · filter_upwards [] with x
    simp [Complex.norm_exp]


/-- The canonical representative in `(0,1]` of one compact gauge coordinate. -/
noncomputable def vertexTorusRepresentative
    (u : VertexTorus (B := B)) (v : SourceDualZeroCells B) : ℝ :=
  (AddCircle.equivIoc (1 : ℝ) 0 (u v)).val

/-- Lift all compact gauge coordinates to the unit interval. -/
noncomputable def vertexTorusRepresentativeVector
    (u : VertexTorus (B := B)) :
    EuclideanSpace ℝ (SourceDualZeroCells B) :=
  WithLp.toLp 2 (vertexTorusRepresentative (B := B) u)

/-- The real coboundary of the chosen representative of a compact gauge field. -/
noncomputable def physicalRealGaugeShift
    (u : VertexTorus (B := B)) :
    EuclideanSpace ℝ (SourceDualOneCells B) :=
  (physicalComplex (B := B)).d₀
    (vertexTorusRepresentativeVector (B := B) u)

/-- A real representative of the physical field `X + d₀U`. -/
noncomputable def physicalRealField
    (x : EuclideanSpace ℝ (SourceDualOneCells B))
    (u : VertexTorus (B := B)) :
    EuclideanSpace ℝ (SourceDualOneCells B) :=
  x + physicalRealGaugeShift (B := B) u

theorem vertexTorusRepresentativeVector_measurable :
    Measurable (vertexTorusRepresentativeVector (B := B)) := by
  have hcoords : Measurable (fun u : VertexTorus (B := B) =>
      vertexTorusRepresentative (B := B) u) := by
    refine Measurable.of_eval fun v => ?_
    change Measurable (fun u : VertexTorus (B := B) =>
      (AddCircle.equivIoc (1 : ℝ) 0 (u v)).val)
    exact measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIoc (1 : ℝ) 0).measurable.comp
        (measurable_pi_apply v))
  have hcont : Continuous (WithLp.toLp 2 :
      (SourceDualZeroCells B → ℝ) →
        EuclideanSpace ℝ (SourceDualZeroCells B)) :=
    PiLp.continuous_toLp 2 (fun _ : SourceDualZeroCells B => ℝ)
  exact hcont.measurable.comp hcoords

theorem physicalRealField_measurable :
    Measurable (fun p : EuclideanSpace ℝ (SourceDualOneCells B) ×
      VertexTorus (B := B) => physicalRealField (B := B) p.1 p.2) := by
  have hshift : Measurable (fun p : EuclideanSpace ℝ
      (SourceDualOneCells B) × VertexTorus (B := B) =>
        (physicalComplex (B := B)).d₀
          (vertexTorusRepresentativeVector (B := B) p.2)) :=
    (physicalComplex (B := B)).d₀.continuous_of_finiteDimensional.measurable.comp
      (vertexTorusRepresentativeVector_measurable.comp measurable_snd)
  change Measurable (fun p : EuclideanSpace ℝ
      (SourceDualOneCells B) × VertexTorus (B := B) => p.1 +
        (physicalComplex (B := B)).d₀
          (vertexTorusRepresentativeVector (B := B) p.2))
  exact measurable_fst.add hshift

/-- The real-valued gauge-averaged law, built from independent co-closed
Gaussian and compact Haar coordinates. -/
noncomputable def gaugeAveragedRealGaussian (β : ℝ) (hβ : 0 ≤ β) :
    Measure (EuclideanSpace ℝ (SourceDualOneCells B)) :=
  Measure.map (fun p : coClosed (physicalComplex (B := B)) ×
      VertexTorus (B := B) => physicalRealField (B := B)
        (p.1 : EuclideanSpace ℝ (SourceDualOneCells B)) p.2)
    ((coClosedGaussian (B := B) β hβ).prod
      (vertexTorusHaar (B := B)))


theorem physicalRealField_pairing_coClosed
    (x : EuclideanSpace ℝ (SourceDualOneCells B))
    (u : VertexTorus (B := B))
    (τ : coClosed (physicalComplex (B := B))) :
    inner ℝ (τ : EuclideanSpace ℝ (SourceDualOneCells B))
        (physicalRealField (B := B) x u) =
      inner ℝ (τ : EuclideanSpace ℝ (SourceDualOneCells B)) x := by
  rw [physicalRealField, inner_add_right]
  have hzero : (physicalComplex (B := B)).d₀.adjoint
      (τ : EuclideanSpace ℝ (SourceDualOneCells B)) = 0 := by
    exact LinearMap.mem_ker.mp τ.property
  have hgauge : inner ℝ (τ : EuclideanSpace ℝ (SourceDualOneCells B))
      (physicalRealGaugeShift (B := B) u) = 0 := by
    calc
      inner ℝ (τ : EuclideanSpace ℝ (SourceDualOneCells B))
          (physicalRealGaugeShift (B := B) u) =
        inner ℝ (physicalRealGaugeShift (B := B) u)
          (τ : EuclideanSpace ℝ (SourceDualOneCells B)) := real_inner_comm _ _
      _ = inner ℝ (vertexTorusRepresentativeVector (B := B) u)
          ((physicalComplex (B := B)).d₀.adjoint
            (τ : EuclideanSpace ℝ (SourceDualOneCells B))) :=
        (LinearMap.adjoint_inner_right _ _ _).symm
      _ = 0 := by rw [hzero]; simp
  simp [hgauge]

theorem physicalRealGaugeShift_mFourier
    (j : IntegerCurrent B) (u : VertexTorus (B := B)) :
    Complex.exp (inner ℝ ((2 * Real.pi) •
      latticeIntegerModeVector (B := B) j)
        (physicalRealGaugeShift (B := B) u) * Complex.I) =
      UnitAddTorus.mFourier (latticeGaugeFrequency (B := B) j) u := by
  classical
  let C := physicalComplex (B := B)
  let q := latticeIntegerModeVector (B := B) j
  let r := (2 * Real.pi) • q
  let g := vertexTorusRepresentativeVector (B := B) u
  have hcoord (v : SourceDualZeroCells B) :
      C.d₀.adjoint r v = 2 * Real.pi *
        ((latticeGaugeFrequency (B := B) j v : ℤ) : ℝ) := by
    change C.d₀.adjoint ((2 * Real.pi) • q) v = _
    rw [map_smul]
    rw [PiLp.smul_apply, smul_eq_mul]
    rw [← latticeGaugeFrequency_cast_eq_adjoint]
  have hpair : inner ℝ r (C.d₀ g) =
      ∑ v : SourceDualZeroCells B, 2 * Real.pi *
        ((latticeGaugeFrequency (B := B) j v : ℤ) : ℝ) * g v := by
    calc
      inner ℝ r (C.d₀ g) = inner ℝ (C.d₀ g) r := real_inner_comm _ _
      _ = inner ℝ g (C.d₀.adjoint r) :=
        (LinearMap.adjoint_inner_right C.d₀ g r).symm
      _ = ∑ v : SourceDualZeroCells B,
          2 * Real.pi * ((latticeGaugeFrequency (B := B) j v : ℤ) : ℝ) * g v := by
            rw [PiLp.inner_apply]
            simp only [Real.inner_apply, hcoord]
            apply Finset.sum_congr rfl
            intro v hv
            ring_nf
  have hFourier : UnitAddTorus.mFourier
      (latticeGaugeFrequency (B := B) j) u =
      Complex.exp (∑ v : SourceDualZeroCells B,
        (2 * Real.pi : ℂ) * Complex.I *
          (latticeGaugeFrequency (B := B) j v : ℂ) * g v) := by
    change (∏ v : SourceDualZeroCells B,
        fourier (latticeGaugeFrequency (B := B) j v) (u v)) = _
    calc
      (∏ v : SourceDualZeroCells B,
          fourier (latticeGaugeFrequency (B := B) j v) (u v)) =
        ∏ v : SourceDualZeroCells B,
          Complex.exp ((2 * Real.pi : ℂ) * Complex.I *
            (latticeGaugeFrequency (B := B) j v : ℂ) * g v) := by
              apply Finset.prod_congr rfl
              intro v hv
              rw [← AddCircle.coe_equivIoc (p := (1 : ℝ)) (a := 0) (y := u v)]
              rw [fourier_coe_apply]
              simp [g, vertexTorusRepresentativeVector,
                vertexTorusRepresentative, div_one]
      _ = Complex.exp (∑ v : SourceDualZeroCells B,
          (2 * Real.pi : ℂ) * Complex.I *
            (latticeGaugeFrequency (B := B) j v : ℂ) * g v) := by
              rw [← Complex.exp_sum]
  rw [hFourier]
  apply congrArg Complex.exp
  change ((inner ℝ r (C.d₀ g) : ℝ) : ℂ) * Complex.I = _
  rw [hpair]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  ring_nf


/--
The Gaussian factor for an integer physical mode, written using the
ambient extension of covariance.
-/
noncomputable def physicalGaussianModeFactor (β : ℝ)
    (j : IntegerCurrent B) : ℂ :=
  Complex.exp (-↑(inner ℝ ((2 * Real.pi) •
    latticeIntegerModeVector (B := B) j)
      ((β • finiteComplexAmbientCovariance
        (physicalComplex (B := B)))
        ((2 * Real.pi) • latticeIntegerModeVector (B := B) j)) / 2))

/-- The co-closed projection of the real Fourier vector for an integer mode. -/
noncomputable def physicalModeCoClosedProjection (j : IntegerCurrent B) :
    coClosed (physicalComplex (B := B)) :=
  (coClosed (physicalComplex (B := B))).orthogonalProjectionOnto
    ((2 * Real.pi) • latticeIntegerModeVector (B := B) j)

/-- The Gaussian factor after a real tilt in direction `τ` and a Fourier
character in direction `j`, written in covariance form. -/
noncomputable def physicalGaussianTiltFactor (β : ℝ) (_hβ : 0 ≤ β)
    (t : ℝ) (τ : coClosed (physicalComplex (B := B)))
    (j : IntegerCurrent B) : ℂ := by
  let C := physicalComplex (B := B)
  let μ := multivariateGaussian 0 (finiteComplexCovarianceMatrix C β)
  let u := (t • τ : coClosed C)
  let v := physicalModeCoClosedProjection (B := B) j
  letI : (finiteComplexCovarianceMatrix C β).PosSemidef :=
    finiteComplexCovarianceMatrix_posSemidef C _hβ
  exact Complex.exp ((((ProbabilityTheory.covarianceBilin μ
      (u : EuclideanSpace ℝ (SourceDualOneCells B))
      (u : EuclideanSpace ℝ (SourceDualOneCells B)) : ℝ) -
    ProbabilityTheory.covarianceBilin μ
      (v : EuclideanSpace ℝ (SourceDualOneCells B))
      (v : EuclideanSpace ℝ (SourceDualOneCells B)) : ℝ) +
    2 * Complex.I * ProbabilityTheory.covarianceBilin μ
      (u : EuclideanSpace ℝ (SourceDualOneCells B))
      (v : EuclideanSpace ℝ (SourceDualOneCells B))) / 2)

theorem coClosedGaussian_tiltedMode_integral (β : ℝ) (hβ : 0 ≤ β)
    (t : ℝ) (τ : coClosed (physicalComplex (B := B)))
    (j : IntegerCurrent B) :
    ∫ x : coClosed (physicalComplex (B := B)),
      Complex.exp ((t * inner ℝ τ x : ℝ) + Complex.I *
        (inner ℝ ((2 * Real.pi) • latticeIntegerModeVector (B := B) j)
          (x : EuclideanSpace ℝ (SourceDualOneCells B)) : ℝ))
        ∂coClosedGaussian (B := B) β hβ =
      physicalGaussianTiltFactor (B := B) β hβ t τ j := by
  let C := physicalComplex (B := B)
  let r := (2 * Real.pi) • latticeIntegerModeVector (B := B) j
  let v := physicalModeCoClosedProjection (B := B) j
  have hproj (x : coClosed C) :
      inner ℝ v x = inner ℝ r (x : EuclideanSpace ℝ (SourceDualOneCells B)) := by
    change inner ℝ ((coClosed C).orthogonalProjectionOnto r) x = _
    exact (coClosed C).inner_orthogonalProjectionOnto_eq_of_mem_right x r
  have hsmul (x : coClosed C) :
      inner ℝ (t • τ) x = t * inner ℝ τ x := by
    simp [real_inner_smul_left]
  have h := coClosedGaussian_complexTransform (B := B) β hβ
    (t • τ) v
  have hpoint (x : coClosed C) :
      Complex.exp ((t * inner ℝ τ x : ℝ) + Complex.I *
        (inner ℝ r (x : EuclideanSpace ℝ (SourceDualOneCells B)) : ℝ)) =
      Complex.exp ((inner ℝ (t • τ) x : ℝ) + Complex.I * (inner ℝ v x : ℝ)) := by
    rw [hsmul, hproj]
  calc
    ∫ x : coClosed C,
        Complex.exp ((t * inner ℝ τ x : ℝ) + Complex.I *
          (inner ℝ r (x : EuclideanSpace ℝ (SourceDualOneCells B)) : ℝ))
          ∂coClosedGaussian (B := B) β hβ =
      ∫ x : coClosed C,
        Complex.exp ((inner ℝ (t • τ) x : ℝ) + Complex.I * (inner ℝ v x : ℝ))
          ∂coClosedGaussian (B := B) β hβ := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with x
            exact hpoint x
    _ = physicalGaussianTiltFactor (B := B) β hβ t τ j := by
          simpa [physicalGaussianTiltFactor, C, v] using h

/-- The real-valued gauge-averaged law has the tilted character formula. The
Haar factor removes non-co-closed currents; on surviving modes the Gaussian
factor is the completed-square covariance expression. -/
theorem gaugeAveragedRealGaussian_tiltedMode_integral
    (β : ℝ) (hβ : 0 ≤ β) (t : ℝ)
    (τ : coClosed (physicalComplex (B := B))) (j : IntegerCurrent B) :
    ∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
      Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α : ℝ) + Complex.I *
          (inner ℝ ((2 * Real.pi) • latticeIntegerModeVector (B := B) j)
            α : ℝ)) ∂gaugeAveragedRealGaussian (B := B) β hβ =
      if latticeGaugeFrequency (B := B) j = 0 then
        physicalGaussianTiltFactor (B := B) β hβ t τ j else 0 := by
  let C := physicalComplex (B := B)
  let μ := coClosedGaussian (B := B) β hβ
  let ν := vertexTorusHaar (B := B)
  let φ := fun p : coClosed C × VertexTorus (B := B) =>
    physicalRealField (B := B)
      (p.1 : EuclideanSpace ℝ (SourceDualOneCells B)) p.2
  let r := (2 * Real.pi) • latticeIntegerModeVector (B := B) j
  let v := physicalModeCoClosedProjection (B := B) j
  let f : coClosed C → ℂ := fun x =>
    Complex.exp ((inner ℝ (t • τ) x : ℝ) + Complex.I * (inner ℝ v x : ℝ))
  let g : VertexTorus (B := B) → ℂ := fun u =>
    UnitAddTorus.mFourier (latticeGaugeFrequency (B := B) j) u
  let F : EuclideanSpace ℝ (SourceDualOneCells B) → ℂ := fun α =>
    Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
      (SourceDualOneCells B)) α : ℝ) + Complex.I * (inner ℝ r α : ℝ))
  have hpair : Measurable (fun p : coClosed C × VertexTorus (B := B) =>
      ((p.1 : EuclideanSpace ℝ (SourceDualOneCells B)), p.2)) := by
    fun_prop
  have hφ : Measurable φ := physicalRealField_measurable.comp hpair
  have hF : Measurable F := by fun_prop
  haveI : IsProbabilityMeasure μ := coClosedGaussian_is_probability β hβ
  haveI : IsProbabilityMeasure ν := vertexTorusHaar_is_probability
  have hf : Integrable f μ := by
    simpa [f, inner_smul_left] using
      coClosedGaussian_complexLinear_integrable (B := B) β hβ (t • τ) v
  have hgMeas : Measurable g := by
    change Measurable ((UnitAddTorus.mFourier
      (latticeGaugeFrequency (B := B) j)) ∘ fun u => u)
    exact (UnitAddTorus.mFourier
      (latticeGaugeFrequency (B := B) j)).continuous.measurable
  have hgBound (u : VertexTorus (B := B)) : ‖g u‖ ≤ 1 := by
    have hnorm := (UnitAddTorus.mFourier
      (latticeGaugeFrequency (B := B) j)).norm_coe_le_norm u
    simpa [g, UnitAddTorus.mFourier_norm] using hnorm
  have hg : Integrable g ν :=
    Integrable.of_bound hgMeas.aestronglyMeasurable 1 (ae_of_all _ hgBound)
  have hproj (x : coClosed C) : inner ℝ v x = inner ℝ r
      (x : EuclideanSpace ℝ (SourceDualOneCells B)) := by
    change inner ℝ ((coClosed C).orthogonalProjectionOnto r) x = _
    exact (coClosed C).inner_orthogonalProjectionOnto_eq_of_mem_right x r
  have hgauss : ∫ x : coClosed C, f x ∂μ =
      physicalGaussianTiltFactor (B := B) β hβ t τ j := by
    calc
      ∫ x : coClosed C, f x ∂μ =
          ∫ x : coClosed C,
            Complex.exp ((t * inner ℝ τ x : ℝ) + Complex.I *
              (inner ℝ r (x : EuclideanSpace ℝ (SourceDualOneCells B)) : ℝ))
              ∂coClosedGaussian (B := B) β hβ := by
                apply MeasureTheory.integral_congr_ae
                filter_upwards [] with x
                simp [f, real_inner_smul_left, hproj]
      _ = physicalGaussianTiltFactor (B := B) β hβ t τ j :=
          coClosedGaussian_tiltedMode_integral (B := B) β hβ t τ j
  have hhaar : ∫ u : VertexTorus (B := B), g u ∂ν =
      if latticeGaugeFrequency (B := B) j = 0 then 1 else 0 := by
    simpa [g, ν] using vertexTorusHaar_mFourier_integral
      (B := B) (latticeGaugeFrequency (B := B) j)
  have hpoint (x : coClosed C) (u : VertexTorus (B := B)) :
      F (φ (x, u)) = f x * g u := by
    have htilt := physicalRealField_pairing_coClosed (B := B)
      (x : EuclideanSpace ℝ (SourceDualOneCells B)) u τ
    have hfield : inner ℝ r (physicalRealField (B := B)
        (x : EuclideanSpace ℝ (SourceDualOneCells B)) u) =
        inner ℝ r (x : EuclideanSpace ℝ (SourceDualOneCells B)) +
          inner ℝ r (physicalRealGaugeShift (B := B) u) := by
      rw [physicalRealField, inner_add_right]
    change Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) (physicalRealField (B := B)
          (x : EuclideanSpace ℝ (SourceDualOneCells B)) u) : ℝ) +
        Complex.I * (inner ℝ r (physicalRealField (B := B)
          (x : EuclideanSpace ℝ (SourceDualOneCells B)) u) : ℝ)) =
      Complex.exp ((inner ℝ (t • τ) x : ℝ) + Complex.I * (inner ℝ v x : ℝ)) *
        UnitAddTorus.mFourier (latticeGaugeFrequency (B := B) j) u
    rw [htilt, hfield, hproj, ← physicalRealGaugeShift_mFourier]
    rw [← Complex.exp_add]
    congr 1
    simp [r, real_inner_smul_left]
    ring_nf
  calc
    ∫ α : EuclideanSpace ℝ (SourceDualOneCells B), F α ∂
        gaugeAveragedRealGaussian (B := B) β hβ =
      ∫ p : coClosed C × VertexTorus (B := B), F (φ p) ∂(μ.prod ν) := by
          change ∫ α, F α ∂Measure.map φ (μ.prod ν) = _
          exact MeasureTheory.integral_map hφ.aemeasurable
            hF.aestronglyMeasurable
    _ = ∫ p : coClosed C × VertexTorus (B := B), f p.1 * g p.2 ∂(μ.prod ν) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with p
          exact hpoint p.1 p.2
    _ = (∫ x : coClosed C, f x ∂μ) *
        ∫ u : VertexTorus (B := B), g u ∂ν :=
          MeasureTheory.integral_prod_mul f g
    _ = if latticeGaugeFrequency (B := B) j = 0 then
          physicalGaussianTiltFactor (B := B) β hβ t τ j else 0 := by
          rw [hgauss, hhaar]
          by_cases hfreq : latticeGaugeFrequency (B := B) j = 0
          · simp [hfreq]
          · simp [hfreq]


private theorem gaugeAveragedRealGaussian_realExp_integrable
    (β : ℝ) (hβ : 0 ≤ β) (t : ℝ)
    (τ : coClosed (physicalComplex (B := B))) :
    Integrable (fun α : EuclideanSpace ℝ (SourceDualOneCells B) =>
      Real.exp (t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α))
      (gaugeAveragedRealGaussian (B := B) β hβ) := by
  let C := physicalComplex (B := B)
  let μ := coClosedGaussian (B := B) β hβ
  let ν := vertexTorusHaar (B := B)
  let φ := fun p : coClosed C × VertexTorus (B := B) =>
    physicalRealField (B := B)
      (p.1 : EuclideanSpace ℝ (SourceDualOneCells B)) p.2
  let F : EuclideanSpace ℝ (SourceDualOneCells B) → ℝ := fun α =>
    Real.exp (t * inner ℝ (τ : EuclideanSpace ℝ
      (SourceDualOneCells B)) α)
  haveI : IsProbabilityMeasure ν := vertexTorusHaar_is_probability
  have hpair : Measurable (fun p : coClosed C × VertexTorus (B := B) =>
      ((p.1 : EuclideanSpace ℝ (SourceDualOneCells B)), p.2)) := by
    fun_prop
  have hφ : Measurable φ := physicalRealField_measurable.comp hpair
  have hF : Measurable F := by fun_prop
  have hbase := coClosedGaussian_realExp_integrable (B := B) β hβ
    (t • τ)
  have hprod : Integrable
      (fun p : coClosed C × VertexTorus (B := B) =>
        Real.exp (inner ℝ (t • τ) p.1)) (μ.prod ν) := by
    exact hbase.comp_fst ν
  have hpoint (p : coClosed C × VertexTorus (B := B)) :
      Real.exp (inner ℝ (t • τ) p.1) = F (φ p) := by
    have hp := physicalRealField_pairing_coClosed (B := B)
      (p.1 : EuclideanSpace ℝ (SourceDualOneCells B)) p.2 (t • τ)
    calc
      Real.exp (inner ℝ (t • τ) p.1) =
          Real.exp (inner ℝ ((t • τ : coClosed C) :
            EuclideanSpace ℝ (SourceDualOneCells B))
              (p.1 : EuclideanSpace ℝ (SourceDualOneCells B))) := by
              rfl
      _ = Real.exp (inner ℝ ((t • τ : coClosed C) :
            EuclideanSpace ℝ (SourceDualOneCells B))
            (physicalRealField (B := B)
              (p.1 : EuclideanSpace ℝ (SourceDualOneCells B)) p.2)) := by
              congr 1
              exact hp.symm
      _ = Real.exp (t * inner ℝ (τ : EuclideanSpace ℝ
            (SourceDualOneCells B))
              (physicalRealField (B := B)
                (p.1 : EuclideanSpace ℝ (SourceDualOneCells B)) p.2)) := by
              congr 1
              change inner ℝ (t • (τ : EuclideanSpace ℝ
                (SourceDualOneCells B)))
                (physicalRealField (B := B)
                  (p.1 : EuclideanSpace ℝ (SourceDualOneCells B)) p.2) = _
              rw [real_inner_smul_left]
      _ = F (φ p) := by rfl
  have hpull : Integrable (fun p : coClosed C × VertexTorus (B := B) =>
      F (φ p)) (μ.prod ν) := by
    exact hprod.congr (ae_of_all _ fun p => hpoint p)
  change Integrable F (Measure.map φ (μ.prod ν))
  have hmap := (MeasureTheory.integrable_map_measure
    hF.aestronglyMeasurable hφ.aemeasurable).mpr hpull
  exact hmap


/-- The SourceCoercivity physical current associated with a closed integer mode is exactly
`2π` times the mode used by the torus character. -/
theorem sourcePhysicalCurrentCoClosed_eq_two_pi_mode
    (j : IntegerCurrent B) (hdiv : currentDivergence j = 0) :
    (sourcePhysicalCurrentCoClosed Cubical.originZero j hdiv :
      EuclideanSpace ℝ (SourceDualOneCells B)) =
      (2 * Real.pi) • latticeIntegerModeVector (B := B) j := by
  have hscale : sourcePhysicalCurrentVector j =
      (2 * Real.pi) • sourceRealLinkVector (B := B) j := by
    ext e
    simp [sourcePhysicalCurrentVector, sourceRealLinkVector,
      physicalCurrent_eq_scaled_realCurrent]
  ext e
  simp only [sourcePhysicalCurrentCoClosed, sourceDualTLinear_apply]
  rw [hscale]
  simp only [PiLp.smul_apply, smul_eq_mul, sourceRealLinkVector_apply,
    latticeIntegerModeVector_apply]
  simp only [latticePhysicalMode, Int.cast_mul,
    sourceDualT_cast_eq_orientationSign]
  ring_nf

/--
On a divergence-free integer current, the gauge-averaged Gaussian
character is exactly quotient Gaussian character.
-/
theorem physicalGaussianModeFactor_eq_sourcePhysicalGaussianCharacter
    (β : ℝ) (j : IntegerCurrent B) (hdiv : currentDivergence j = 0) :
    physicalGaussianModeFactor (B := B) β j =
      Complex.ofReal (FroehlichSpencer.FS82.Moment.QuotientGaussian.sourcePhysicalGaussianCharacter
        (B := B) β j hdiv) := by
  let C := physicalComplex (B := B)
  let ρ := sourcePhysicalCurrentCoClosed Cubical.originZero j hdiv
  let t := (2 * Real.pi) • latticeIntegerModeVector (B := B) j
  have hρ : (ρ : EuclideanSpace ℝ (SourceDualOneCells B)) = t := by
    simpa [ρ, t] using sourcePhysicalCurrentCoClosed_eq_two_pi_mode
      (B := B) j hdiv
  have hρcov : finiteComplexAmbientCovariance C (ρ :
      EuclideanSpace ℝ (SourceDualOneCells B)) = latticeVΛ
        (B := B) Cubical.originZero ρ :=
    finiteComplexAmbientCovariance_coClosed_apply C ρ
  have hexp : inner ℝ t ((β • finiteComplexAmbientCovariance C) t) / 2 =
      (β / 2) * Gaussian.quotientCovarianceQuadratic C ρ := by
    rw [← hρ]
    rw [LinearMap.smul_apply, hρcov]
    rw [real_inner_smul_right]
    simp [Gaussian.quotientCovarianceQuadratic, latticeVΛ, C,
      physicalComplex]
    ring_nf
  have hexp' : inner ℝ ((2 * Real.pi) •
      latticeIntegerModeVector (B := B) j)
        ((β • finiteComplexAmbientCovariance C)
          ((2 * Real.pi) • latticeIntegerModeVector (B := B) j)) / 2 =
      (β / 2) * Gaussian.quotientCovarianceQuadratic C ρ := by
    simpa [t] using hexp
  rw [physicalGaussianModeFactor, hexp']
  simp [FroehlichSpencer.FS82.Moment.QuotientGaussian.sourcePhysicalGaussianCharacter,
    Gaussian.quotientCovarianceQuadratic, ρ, C, physicalComplex,
    Complex.ofReal_exp]


/--
On a divergence-free integer current, the tilted factor is quotient Gaussian character times the exponential of the completed square.
-/
theorem physicalGaussianTiltFactor_eq_completedSquare
    (β : ℝ) (hβ : 0 ≤ β) (t : ℝ)
    (τ : coClosed (physicalComplex (B := B)))
    (j : IntegerCurrent B) (hdiv : currentDivergence j = 0) :
    physicalGaussianTiltFactor (B := B) β hβ t τ j =
      Complex.exp ((β / 2) * (t ^ 2 * inner ℝ τ
          (latticeVΛ (B := B) Cubical.originZero τ)) +
        Complex.I * (β * t * inner ℝ τ
          (latticeVΛ (B := B) Cubical.originZero
            (sourcePhysicalCurrentCoClosed Cubical.originZero j hdiv)))) *
      Complex.ofReal (FroehlichSpencer.FS82.Moment.QuotientGaussian.sourcePhysicalGaussianCharacter (B := B) β j hdiv) := by
  let C := physicalComplex (B := B)
  let W := coClosed C
  let μ := multivariateGaussian 0 (finiteComplexCovarianceMatrix C β)
  let q := latticeIntegerModeVector (B := B) j
  let r := (2 * Real.pi) • q
  let ρ := sourcePhysicalCurrentCoClosed Cubical.originZero j hdiv
  let T := β • finiteComplexAmbientCovariance C
  have hfreq : latticeGaugeFrequency (B := B) j = 0 :=
    (latticeGaugeFrequency_zero_iff_currentDivergence_zero (B := B) j).2 hdiv
  have hq : q ∈ W := by
    exact (latticeIntegerModeVector_mem_coClosed_iff_frequency_zero
      (B := B) j).2 hfreq
  have hr : r ∈ W := by
    dsimp [r, q]
    exact W.smul_mem (2 * Real.pi) hq
  have hproj : physicalModeCoClosedProjection (B := B) j =
      (⟨r, hr⟩ : W) := by
    change W.orthogonalProjectionOnto r = ⟨r, hr⟩
    exact W.orthogonalProjectionOnto_mem_subspace_eq_self ⟨r, hr⟩
  have hρ : (ρ : EuclideanSpace ℝ (SourceDualOneCells B)) = r := by
    simpa [ρ, r, q] using
      sourcePhysicalCurrentCoClosed_eq_two_pi_mode (B := B) j hdiv
  have hA : ProbabilityTheory.covarianceBilin μ
      ((t • τ : W) : EuclideanSpace ℝ (SourceDualOneCells B))
      ((t • τ : W) : EuclideanSpace ℝ (SourceDualOneCells B)) =
        β * t ^ 2 * inner ℝ τ
          (latticeVΛ (B := B) Cubical.originZero τ) := by
    rw [physicalAmbientGaussian_covarianceBilin (B := B) β hβ]
    simp [LinearMap.smul_apply, map_smul, real_inner_smul_left,
      real_inner_smul_right, finiteComplexAmbientCovariance_coClosed_apply,
      Gaussian.latticeVΛ]
    ring_nf
  have hB : ProbabilityTheory.covarianceBilin μ r r =
      β * inner ℝ ρ
        (latticeVΛ (B := B) Cubical.originZero ρ) := by
    rw [physicalAmbientGaussian_covarianceBilin (B := B) β hβ, ← hρ]
    simp [LinearMap.smul_apply,
      real_inner_smul_right, finiteComplexAmbientCovariance_coClosed_apply,
      Gaussian.latticeVΛ]
  have hAB : ProbabilityTheory.covarianceBilin μ
      ((t • τ : W) : EuclideanSpace ℝ (SourceDualOneCells B)) r =
        β * t * inner ℝ τ
          (latticeVΛ (B := B) Cubical.originZero ρ) := by
    rw [physicalAmbientGaussian_covarianceBilin (B := B) β hβ, ← hρ]
    simp [LinearMap.smul_apply, real_inner_smul_left,
      real_inner_smul_right, finiteComplexAmbientCovariance_coClosed_apply,
      Gaussian.latticeVΛ]
    ring_nf
  have hmodeCov : physicalGaussianModeFactor (B := B) β j =
      Complex.exp (-(ProbabilityTheory.covarianceBilin μ r r) / 2) := by
    rw [physicalGaussianModeFactor,
      physicalAmbientGaussian_covarianceBilin (B := B) β hβ]
    simp [r, q]
    ring_nf
  have hfactor : physicalGaussianTiltFactor (B := B) β hβ t τ j =
      Complex.exp ((((ProbabilityTheory.covarianceBilin μ
        ((t • τ : W) : EuclideanSpace ℝ (SourceDualOneCells B))
        ((t • τ : W) : EuclideanSpace ℝ (SourceDualOneCells B)) : ℝ) -
        ProbabilityTheory.covarianceBilin μ r r : ℝ) +
        2 * Complex.I * ProbabilityTheory.covarianceBilin μ
          ((t • τ : W) : EuclideanSpace ℝ (SourceDualOneCells B)) r) / 2) := by
    unfold physicalGaussianTiltFactor
    change Complex.exp ((((ProbabilityTheory.covarianceBilin μ
        ((t • τ : W) : EuclideanSpace ℝ (SourceDualOneCells B))
        ((t • τ : W) : EuclideanSpace ℝ (SourceDualOneCells B)) : ℝ) -
        ProbabilityTheory.covarianceBilin μ
          (physicalModeCoClosedProjection (B := B) j :
            EuclideanSpace ℝ (SourceDualOneCells B))
          (physicalModeCoClosedProjection (B := B) j :
            EuclideanSpace ℝ (SourceDualOneCells B)) : ℝ) +
        2 * Complex.I * ProbabilityTheory.covarianceBilin μ
          ((t • τ : W) : EuclideanSpace ℝ (SourceDualOneCells B))
          (physicalModeCoClosedProjection (B := B) j :
            EuclideanSpace ℝ (SourceDualOneCells B))) / 2) = _
    rw [hproj]
  rw [hfactor, hA, hB, hAB]
  rw [← physicalGaussianModeFactor_eq_sourcePhysicalGaussianCharacter
    (B := B) β j hdiv, hmodeCov]
  rw [← Complex.exp_add]
  congr 1
  rw [hB]
  simp [ρ]
  ring_nf


/-- The real-link version of a finite trigonometric polynomial. -/
noncomputable def physicalRealTrigPolynomial {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) (j : ι → IntegerCurrent B) :
    EuclideanSpace ℝ (SourceDualOneCells B) → ℂ := fun α =>
      ∑ i ∈ s, a i * Complex.exp
        (inner ℝ ((2 * Real.pi) • latticeIntegerModeVector (B := B) (j i)) α *
          Complex.I)

private theorem physicalRealTiltedTrigMonomial_integrable {ι : Type*}
    [DecidableEq ι] (β : ℝ) (hβ : 0 ≤ β) (t : ℝ)
    (τ : coClosed (physicalComplex (B := B))) (a : ι → ℂ)
    (j : ι → IntegerCurrent B) (i : ι) :
    Integrable (fun α : EuclideanSpace ℝ (SourceDualOneCells B) =>
      Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α : ℝ) : ℂ) *
        (a i * Complex.exp
          (inner ℝ ((2 * Real.pi) • latticeIntegerModeVector
            (B := B) (j i)) α * Complex.I)))
      (gaugeAveragedRealGaussian (B := B) β hβ) := by
  let R : EuclideanSpace ℝ (SourceDualOneCells B) → ℝ := fun α =>
    Real.exp (t * inner ℝ (τ : EuclideanSpace ℝ
      (SourceDualOneCells B)) α)
  have hR := gaugeAveragedRealGaussian_realExp_integrable
    (B := B) β hβ t τ
  have hdom : Integrable (fun α => ‖a i‖ * R α)
      (gaugeAveragedRealGaussian (B := B) β hβ) := by
    simpa [R, mul_comm] using hR.const_mul ‖a i‖
  apply Integrable.mono' hdom
  · fun_prop
  · filter_upwards [] with α
    have hnorm : ‖Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α : ℝ) : ℂ) *
        (a i * Complex.exp
          (inner ℝ ((2 * Real.pi) • latticeIntegerModeVector
            (B := B) (j i)) α * Complex.I))‖ =
        ‖a i‖ * Real.exp (t * inner ℝ (τ : EuclideanSpace ℝ
          (SourceDualOneCells B)) α) := by
      rw [norm_mul, norm_mul]
      simp [Complex.norm_exp, mul_comm]
    simpa [R] using (le_of_eq hnorm)

/--
A real tilt preserves the gauge average because its direction lies in
`W`.

The surviving Fourier terms are the quotient characters times the
completed-square factor.
-/
theorem gaugeAveragedRealGaussian_tiltedTrigPolynomial_integral
    {ι : Type*} [DecidableEq ι] (β : ℝ) (hβ : 0 ≤ β) (t : ℝ)
    (τ : coClosed (physicalComplex (B := B)))
    (s : Finset ι) (a : ι → ℂ) (j : ι → IntegerCurrent B) :
    ∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
      Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α : ℝ) : ℂ) *
        physicalRealTrigPolynomial (B := B) s a j α ∂
        gaugeAveragedRealGaussian (B := B) β hβ =
      ∑ i ∈ s, a i * (if latticeGaugeFrequency (B := B) (j i) = 0 then
        physicalGaussianTiltFactor (B := B) β hβ t τ (j i) else 0) := by
  classical
  change ∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
      Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α : ℝ) : ℂ) *
        (∑ i ∈ s, a i * Complex.exp
          (inner ℝ ((2 * Real.pi) • latticeIntegerModeVector
            (B := B) (j i)) α * Complex.I)) ∂
      gaugeAveragedRealGaussian (B := B) β hβ = _
  have hsum (α : EuclideanSpace ℝ (SourceDualOneCells B)) :
      Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α : ℝ) : ℂ) *
        (∑ i ∈ s, a i * Complex.exp
          (inner ℝ ((2 * Real.pi) • latticeIntegerModeVector
            (B := B) (j i)) α * Complex.I)) =
      ∑ i ∈ s, Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α : ℝ) : ℂ) *
          (a i * Complex.exp
            (inner ℝ ((2 * Real.pi) • latticeIntegerModeVector
              (B := B) (j i)) α * Complex.I)) := by
    exact Finset.mul_sum s (fun i => a i * Complex.exp
      (inner ℝ ((2 * Real.pi) • latticeIntegerModeVector
        (B := B) (j i)) α * Complex.I)) _
  calc
    ∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
        Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
          (SourceDualOneCells B)) α : ℝ) : ℂ) *
          (∑ i ∈ s, a i * Complex.exp
            (inner ℝ ((2 * Real.pi) • latticeIntegerModeVector
              (B := B) (j i)) α * Complex.I)) ∂
          gaugeAveragedRealGaussian (B := B) β hβ =
      ∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
        ∑ i ∈ s, Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
          (SourceDualOneCells B)) α : ℝ) : ℂ) *
            (a i * Complex.exp
              (inner ℝ ((2 * Real.pi) • latticeIntegerModeVector
                (B := B) (j i)) α * Complex.I)) ∂
          gaugeAveragedRealGaussian (B := B) β hβ := by
      apply integral_congr_ae
      filter_upwards [] with α
      exact hsum α
    _ = ∑ i ∈ s, a i * (if latticeGaugeFrequency (B := B) (j i) = 0 then
        physicalGaussianTiltFactor (B := B) β hβ t τ (j i) else 0) := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        have hpoint (α : EuclideanSpace ℝ (SourceDualOneCells B)) :
        Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
          (SourceDualOneCells B)) α : ℝ) : ℂ) *
          (a i * Complex.exp
            (inner ℝ ((2 * Real.pi) • latticeIntegerModeVector
              (B := B) (j i)) α * Complex.I)) =
        a i * Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
          (SourceDualOneCells B)) α : ℝ) + Complex.I *
            (inner ℝ ((2 * Real.pi) • latticeIntegerModeVector
              (B := B) (j i)) α : ℝ)) := by
          calc
            _ = a i * (Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
                  (SourceDualOneCells B)) α : ℝ) : ℂ) *
                Complex.exp (inner ℝ ((2 * Real.pi) • latticeIntegerModeVector
                  (B := B) (j i)) α * Complex.I)) := by ring_nf
            _ = a i * Complex.exp
                ((t * inner ℝ (τ : EuclideanSpace ℝ
                    (SourceDualOneCells B)) α : ℝ) + Complex.I *
                  (inner ℝ ((2 * Real.pi) • latticeIntegerModeVector
                    (B := B) (j i)) α : ℝ)) := by
                  rw [← Complex.exp_add]
                  congr 1
                  push_cast
                  ring_nf
        rw [integral_congr_ae (ae_of_all _ hpoint), integral_const_mul,
          gaugeAveragedRealGaussian_tiltedMode_integral]
      · intro i hi
        exact physicalRealTiltedTrigMonomial_integrable
          (B := B) β hβ t τ a j i

/--
The quotient character with its real-tilt completed square.

It is
zero on non-co-closed integer currents.
-/
noncomputable def physicalGaussianTiltCompletedSquareFactor
    (β : ℝ) (_hβ : 0 ≤ β) (t : ℝ)
    (τ : coClosed (physicalComplex (B := B))) (j : IntegerCurrent B) : ℂ :=
  if hdiv : currentDivergence j = 0 then
    Complex.exp ((β / 2) * (t ^ 2 * inner ℝ τ
        (latticeVΛ (B := B) Cubical.originZero τ)) +
      Complex.I * (β * t * inner ℝ τ
        (latticeVΛ (B := B) Cubical.originZero
          (sourcePhysicalCurrentCoClosed Cubical.originZero j hdiv)))) *
      Complex.ofReal (FroehlichSpencer.FS82.Moment.QuotientGaussian.sourcePhysicalGaussianCharacter
        (B := B) β j hdiv)
  else 0

theorem physicalGaussianTiltCompletedSquareFactor_eq_frequencyCase
    (β : ℝ) (hβ : 0 ≤ β) (t : ℝ)
    (τ : coClosed (physicalComplex (B := B))) (j : IntegerCurrent B) :
    physicalGaussianTiltCompletedSquareFactor (B := B) β hβ t τ j =
      if latticeGaugeFrequency (B := B) j = 0 then
        physicalGaussianTiltFactor (B := B) β hβ t τ j else 0 := by
  classical
  by_cases hf : latticeGaugeFrequency (B := B) j = 0
  · have hd : currentDivergence j = 0 :=
      (latticeGaugeFrequency_zero_iff_currentDivergence_zero
        (B := B) j).1 hf
    calc
      physicalGaussianTiltCompletedSquareFactor (B := B) β hβ t τ j =
          Complex.exp ((β / 2) * (t ^ 2 * inner ℝ τ
              (latticeVΛ (B := B) Cubical.originZero τ)) +
            Complex.I * (β * t * inner ℝ τ
              (latticeVΛ (B := B) Cubical.originZero
                (sourcePhysicalCurrentCoClosed Cubical.originZero j hd)))) *
            Complex.ofReal (FroehlichSpencer.FS82.Moment.QuotientGaussian.sourcePhysicalGaussianCharacter
              (B := B) β j hd) := by
          simp [physicalGaussianTiltCompletedSquareFactor, hd]
      _ = physicalGaussianTiltFactor (B := B) β hβ t τ j :=
          (physicalGaussianTiltFactor_eq_completedSquare
            (B := B) β hβ t τ j hd).symm
      _ = if latticeGaugeFrequency (B := B) j = 0 then
            physicalGaussianTiltFactor (B := B) β hβ t τ j else 0 := by
          simp [hf]
  · have hd : currentDivergence j ≠ 0 := by
      intro hdiv
      exact hf ((latticeGaugeFrequency_zero_iff_currentDivergence_zero
        (B := B) j).2 hdiv)
    calc
      physicalGaussianTiltCompletedSquareFactor (B := B) β hβ t τ j = 0 := by
        simp [physicalGaussianTiltCompletedSquareFactor, hd]
      _ = if latticeGaugeFrequency (B := B) j = 0 then
            physicalGaussianTiltFactor (B := B) β hβ t τ j else 0 := by
          simp [hf]

/--
The finite real-tilted Fourier sum, with each surviving term written as
quotient character times its completed square.
-/
theorem gaugeAveragedRealGaussian_tiltedTrigPolynomial_integral_completedSquare
    {ι : Type*} [DecidableEq ι] (β : ℝ) (hβ : 0 ≤ β) (t : ℝ)
    (τ : coClosed (physicalComplex (B := B)))
    (s : Finset ι) (a : ι → ℂ) (j : ι → IntegerCurrent B) :
    ∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
      Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α : ℝ) : ℂ) *
        physicalRealTrigPolynomial (B := B) s a j α ∂
        gaugeAveragedRealGaussian (B := B) β hβ =
      ∑ i ∈ s, a i *
        physicalGaussianTiltCompletedSquareFactor (B := B) β hβ t τ (j i) := by
  rw [gaugeAveragedRealGaussian_tiltedTrigPolynomial_integral]
  apply Finset.sum_congr rfl
  intro i hi
  rw [physicalGaussianTiltCompletedSquareFactor_eq_frequencyCase]

end FroehlichSpencer.FS82.Gaussian.GaugeAveraged

end
