/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.FiniteGaussian
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.MeasureTheory.Constructions.SubmoduleQuotient
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Generic quotient Gaussian on a finite exact complex

For any finite complex exact at degree one, this module constructs the
co-closed covariance and its centered Gaussian law on edge fields modulo
exact directions. No cubical or lattice operator is assumed.
-/

public section

namespace FroehlichSpencer.FS82.Gaussian

open scoped InnerProductSpace
open ProbabilityTheory

variable {V E P : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype P] [DecidableEq P]

@[expose] noncomputable def finiteComplexCoClosedProjection
    (C : ExactOneComplex V E P) :
    EuclideanSpace ℝ E →ₗ[ℝ] coClosed C :=
  ((coClosed C).orthogonalProjectionOnto).toLinearMap

@[expose] noncomputable def finiteComplexAmbientCovariance
    (C : ExactOneComplex V E P) :
    EuclideanSpace ℝ E →ₗ[ℝ] EuclideanSpace ℝ E :=
  ((coClosed C).subtype).comp
    ((hodgeInverseOnCoClosed C).comp (finiteComplexCoClosedProjection C))

theorem finiteComplexAmbientCovariance_symmetric
    (C : ExactOneComplex V E P) (x y : EuclideanSpace ℝ E) :
    inner ℝ (finiteComplexAmbientCovariance C x) y =
      inner ℝ x (finiteComplexAmbientCovariance C y) := by
  let K := coClosed C
  let V := hodgeInverseOnCoClosed C
  let px := finiteComplexCoClosedProjection C x
  let py := finiteComplexCoClosedProjection C y
  have hleft : inner ℝ (V px : EuclideanSpace ℝ E)
      (K.orthogonalProjectionOnto y : EuclideanSpace ℝ E) =
      inner ℝ (V px : EuclideanSpace ℝ E) y :=
    K.inner_orthogonalProjectionOnto_eq_of_mem_left (V px) y
  have hright : inner ℝ (K.orthogonalProjectionOnto x :
      EuclideanSpace ℝ E) (V py : EuclideanSpace ℝ E) =
      inner ℝ x (V py : EuclideanSpace ℝ E) :=
    K.inner_orthogonalProjectionOnto_eq_of_mem_right (V py) x
  calc
    inner ℝ (finiteComplexAmbientCovariance C x) y =
        inner ℝ (V px : EuclideanSpace ℝ E) y := rfl
    _ = inner ℝ (V px : EuclideanSpace ℝ E)
        (py : EuclideanSpace ℝ E) := by rw [← hleft]; rfl
    _ = inner ℝ (px : EuclideanSpace ℝ E) (V py : EuclideanSpace ℝ E) :=
      hodgeInverseOnCoClosed_symmetric C px py
    _ = inner ℝ x (V py : EuclideanSpace ℝ E) := by
      rw [← hright]
      rfl

theorem finiteComplexAmbientCovariance_nonneg
    (C : ExactOneComplex V E P) (x : EuclideanSpace ℝ E) :
    0 ≤ inner ℝ x (finiteComplexAmbientCovariance C x) := by
  let K := coClosed C
  let V := hodgeInverseOnCoClosed C
  let px := finiteComplexCoClosedProjection C x
  have hp := quotientCovarianceQuadratic_nonneg C px
  have hproj := K.inner_orthogonalProjectionOnto_eq_of_mem_left (V px) x
  calc
    0 ≤ inner ℝ (px : EuclideanSpace ℝ E) (V px : EuclideanSpace ℝ E) := hp
    _ = inner ℝ x (finiteComplexAmbientCovariance C x) := by
      rw [finiteComplexAmbientCovariance]
      change inner ℝ (K.orthogonalProjectionOnto x : EuclideanSpace ℝ E)
          (V px : EuclideanSpace ℝ E) =
        inner ℝ x (V px : EuclideanSpace ℝ E)
      calc
        inner ℝ (K.orthogonalProjectionOnto x : EuclideanSpace ℝ E)
            (V px : EuclideanSpace ℝ E) =
          inner ℝ (V px : EuclideanSpace ℝ E)
            (K.orthogonalProjectionOnto x : EuclideanSpace ℝ E) :=
              real_inner_comm _ _
        _ = inner ℝ (V px : EuclideanSpace ℝ E) x := hproj
        _ = inner ℝ x (V px : EuclideanSpace ℝ E) := real_inner_comm _ _

theorem finiteComplexAmbientCovariance_coClosed_apply
    (C : ExactOneComplex V E P) (μ : coClosed C) :
    finiteComplexAmbientCovariance C μ = hodgeInverseOnCoClosed C μ := by
  change (coClosed C).subtype
    (hodgeInverseOnCoClosed C
      ((coClosed C).orthogonalProjectionOnto
        (μ : EuclideanSpace ℝ E))) = _
  have hproj : (coClosed C).orthogonalProjectionOnto
      (μ : EuclideanSpace ℝ E) = μ :=
    (coClosed C).orthogonalProjectionOnto_mem_subspace_eq_self μ
  rw [hproj]
  rfl

@[expose] noncomputable def finiteComplexCovarianceMatrix
    (C : ExactOneComplex V E P) (β : ℝ) : Matrix E E ℝ :=
  matrixOfLinearMap (β • finiteComplexAmbientCovariance C)

theorem finiteComplexCovarianceMatrix_posSemidef
    (C : ExactOneComplex V E P) {β : ℝ} (hβ : 0 ≤ β) :
    (finiteComplexCovarianceMatrix C β).PosSemidef := by
  apply matrixOfLinearMap_posSemidef
  · intro x y
    simp only [LinearMap.smul_apply]
    rw [real_inner_smul_left, real_inner_smul_right,
      finiteComplexAmbientCovariance_symmetric]
  · intro x
    simp only [LinearMap.smul_apply]
    rw [real_inner_smul_right]
    exact mul_nonneg hβ (finiteComplexAmbientCovariance_nonneg C x)

theorem finiteComplexAmbientGaussian_characteristic
    (C : ExactOneComplex V E P) {β : ℝ} (hβ : 0 ≤ β)
    (x : EuclideanSpace ℝ E) :
    MeasureTheory.charFun
      (ProbabilityTheory.multivariateGaussian 0
        (finiteComplexCovarianceMatrix C β)) x =
      Complex.exp (-↑(inner ℝ x
        ((β • finiteComplexAmbientCovariance C) x) / 2)) := by
  have hS := finiteComplexCovarianceMatrix_posSemidef C hβ
  rw [finiteGaussianAdapter_characteristic
    (finiteComplexCovarianceMatrix C β) hS x]
  have hquad : x.ofLp ⬝ᵥ
      (finiteComplexCovarianceMatrix C β).mulVec x.ofLp =
      inner ℝ x ((β • finiteComplexAmbientCovariance C) x) := by
    change x.ofLp ⬝ᵥ (matrixOfLinearMap
        (β • finiteComplexAmbientCovariance C)).mulVec x.ofLp = _
    rw [matrixOfLinearMap_mulVec]
    simp [dotProduct, PiLp.inner_apply, mul_comm, mul_left_comm]
  rw [hquad]
  simp [Complex.ofReal_div]

abbrev FiniteGaugeQuotient (C : ExactOneComplex V E P) :=
  EuclideanSpace ℝ E ⧸ C.d₁.ker

@[expose] noncomputable def finiteComplexQuotientMap
    (C : ExactOneComplex V E P) :
    EuclideanSpace ℝ E →L[ℝ] FiniteGaugeQuotient C :=
  C.d₁.ker.mkQL

theorem finiteComplexQuotientMap_measurable
    (C : ExactOneComplex V E P) :
    Measurable (finiteComplexQuotientMap C) := by
  change Measurable (Quotient.mk'' : EuclideanSpace ℝ E → FiniteGaugeQuotient C)
  exact measurable_quotient_mk''

@[expose] noncomputable def finiteComplexQuotientGaussian
    (C : ExactOneComplex V E P) (β : ℝ) (_hβ : 0 ≤ β) :
    MeasureTheory.Measure (FiniteGaugeQuotient C) := by
  letI : (finiteComplexCovarianceMatrix C β).PosSemidef :=
    finiteComplexCovarianceMatrix_posSemidef C _hβ
  exact MeasureTheory.Measure.map (finiteComplexQuotientMap C)
    (ProbabilityTheory.multivariateGaussian 0 (finiteComplexCovarianceMatrix C β))

theorem finiteComplexQuotientGaussian_is_probability
    (C : ExactOneComplex V E P) {β : ℝ} (hβ : 0 ≤ β) :
    MeasureTheory.IsProbabilityMeasure (finiteComplexQuotientGaussian C β hβ) := by
  unfold finiteComplexQuotientGaussian
  have hpsd : (finiteComplexCovarianceMatrix C β).PosSemidef :=
    finiteComplexCovarianceMatrix_posSemidef C hβ
  have hbase : MeasureTheory.IsProbabilityMeasure
      (ProbabilityTheory.multivariateGaussian 0 (finiteComplexCovarianceMatrix C β)) := by
    rw [ProbabilityTheory.multivariateGaussian]
    infer_instance
  change MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.Measure.map (finiteComplexQuotientMap C)
      (ProbabilityTheory.multivariateGaussian 0 (finiteComplexCovarianceMatrix C β)))
  constructor
  rw [MeasureTheory.Measure.map_apply (finiteComplexQuotientMap_measurable C)
    MeasurableSet.univ]
  simp [hbase.measure_univ]

theorem finiteComplexQuotientGaussian_is_gaussian
    (C : ExactOneComplex V E P) {β : ℝ} (hβ : 0 ≤ β) :
    ProbabilityTheory.IsGaussian (finiteComplexQuotientGaussian C β hβ) := by
  unfold finiteComplexQuotientGaussian
  have hpsd := finiteComplexCovarianceMatrix_posSemidef C hβ
  have hpsd' : (finiteComplexCovarianceMatrix C β).PosSemidef := hpsd
  have hbaseGaussian : ProbabilityTheory.IsGaussian
      (ProbabilityTheory.multivariateGaussian 0 (finiteComplexCovarianceMatrix C β)) :=
    inferInstance
  have hpsdInstance : (finiteComplexCovarianceMatrix C β).PosSemidef := hpsd'
  have hbaseGaussianInstance : ProbabilityTheory.IsGaussian
      (ProbabilityTheory.multivariateGaussian 0 (finiteComplexCovarianceMatrix C β)) :=
    hbaseGaussian
  have hquotientMeasurable : OpensMeasurableSpace (FiniteGaugeQuotient C) := ⟨by
    change MeasurableSpace.generateFrom
      {s : Set (FiniteGaugeQuotient C) | IsOpen s} ≤ _
    rw [MeasurableSpace.generateFrom_le_iff]
    intro s hs
    have hsopen : IsOpen s := by simpa only [Set.mem_ofPred_eq] using hs
    have hms : MeasurableSet s := by
      rw [measurableSet_quotient]
      have hcont : Continuous (finiteComplexQuotientMap C) :=
        (finiteComplexQuotientMap C).continuous
      exact (hcont.isOpen_preimage s hsopen).measurableSet
    simpa only [Set.mem_ofPred_eq] using hms
  ⟩
  exact ProbabilityTheory.isGaussian_map_of_measurable
    (μ := ProbabilityTheory.multivariateGaussian 0 (finiteComplexCovarianceMatrix C β))
    (L := finiteComplexQuotientMap C)
    (finiteComplexQuotientMap_measurable C)

theorem finiteComplexTestFunctional_vanishes_on_exact
    (C : ExactOneComplex V E P) (μ : coClosed C) :
    C.d₁.ker ≤ (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ E) (μ : _)).ker := by
  intro x hx
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (C.exactOne hx)
  have hadj : C.d₀.adjoint (μ : EuclideanSpace ℝ E) = 0 :=
    LinearMap.mem_ker.mp μ.property
  have hinner := LinearMap.adjoint_inner_right C.d₀ v
    (μ : EuclideanSpace ℝ E)
  apply LinearMap.mem_ker.mpr
  change (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ E) (μ :
    EuclideanSpace ℝ E)) x = 0
  rw [← hv]
  simp only [InnerProductSpace.toDualMap_apply_apply]
  calc
    inner ℝ (μ : EuclideanSpace ℝ E) (C.d₀ v) =
        inner ℝ (C.d₀ v) (μ : EuclideanSpace ℝ E) := real_inner_comm _ _
    _ = inner ℝ v (C.d₀.adjoint (μ : EuclideanSpace ℝ E)) := hinner.symm
    _ = 0 := by rw [hadj]; simp

@[expose] noncomputable def finiteComplexQuotientTestFunctional
    (C : ExactOneComplex V E P) (μ : coClosed C) :
    StrongDual ℝ (FiniteGaugeQuotient C) :=
  C.d₁.ker.liftQL
    (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ E) (μ : _))
    (finiteComplexTestFunctional_vanishes_on_exact C μ)

theorem finiteComplexQuotientTestFunctional_comp
    (C : ExactOneComplex V E P) (μ : coClosed C) :
    (finiteComplexQuotientTestFunctional C μ).comp (finiteComplexQuotientMap C) =
      InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ E) (μ : _) := by
  ext x
  simp [finiteComplexQuotientTestFunctional, finiteComplexQuotientMap,
    Submodule.liftQL_apply]

theorem finiteComplexCovarianceQuadratic (C : ExactOneComplex V E P) (β : ℝ)
    (x : EuclideanSpace ℝ E) :
    x.ofLp ⬝ᵥ (finiteComplexCovarianceMatrix C β).mulVec x.ofLp =
      inner ℝ x ((β • finiteComplexAmbientCovariance C) x) := by
  change x.ofLp ⬝ᵥ (matrixOfLinearMap
      (β • finiteComplexAmbientCovariance C)).mulVec x.ofLp = _
  rw [matrixOfLinearMap_mulVec]
  simp [dotProduct, PiLp.inner_apply, mul_comm, mul_left_comm]

theorem finiteComplexQuotientGaussian_charFunDual
    (C : ExactOneComplex V E P) {β : ℝ} (hβ : 0 ≤ β)
    (μ : coClosed C) :
    MeasureTheory.charFun
      (MeasureTheory.Measure.map (finiteComplexQuotientTestFunctional C μ)
        (finiteComplexQuotientGaussian C β hβ)) 1 =
      Complex.exp (-↑(inner ℝ (μ : EuclideanSpace ℝ E)
        ((β • finiteComplexAmbientCovariance C) μ) / 2)) := by
  let base := ProbabilityTheory.multivariateGaussian 0 (finiteComplexCovarianceMatrix C β)
  let L := InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ E)
    (μ : EuclideanSpace ℝ E)
  have hS := finiteComplexCovarianceMatrix_posSemidef C hβ
  have hmean : ∫ x, L x ∂base = 0 := by
    rw [ProbabilityTheory.IsGaussian.integral_dual]
    simp [base]
  have hvariance : ProbabilityTheory.variance (L : StrongDual ℝ
      (EuclideanSpace ℝ E)) base =
    inner ℝ (μ : EuclideanSpace ℝ E) ((β • finiteComplexAmbientCovariance C) μ) := by
    rw [← ProbabilityTheory.covarianceBilinDual_self_eq_variance
      (ProbabilityTheory.IsGaussian.memLp_two_id (μ := base)) L,
      ← ProbabilityTheory.covarianceBilin_eq_covarianceBilinDual
        (μ := base) (μ : EuclideanSpace ℝ E) (μ : EuclideanSpace ℝ E)]
    calc
      (ProbabilityTheory.covarianceBilin base)
          (μ : EuclideanSpace ℝ E) (μ : EuclideanSpace ℝ E) =
        (μ : EuclideanSpace ℝ E).ofLp ⬝ᵥ
          (finiteComplexCovarianceMatrix C β).mulVec
            (μ : EuclideanSpace ℝ E).ofLp := by
          simpa [base] using ProbabilityTheory.covarianceBilin_multivariateGaussian
            hS (μ : EuclideanSpace ℝ E) (μ : EuclideanSpace ℝ E)
      _ = inner ℝ (μ : EuclideanSpace ℝ E)
          ((β • finiteComplexAmbientCovariance C) μ) :=
        finiteComplexCovarianceQuadratic C β (μ : EuclideanSpace ℝ E)
  have hmeanComplex : ∫ x, (L x : ℂ) ∂base = 0 := by
    rw [integral_complex_ofReal]
    exact_mod_cast hmean
  have hpsdInstance : (finiteComplexCovarianceMatrix C β).PosSemidef := hS
  have hmap : MeasureTheory.Measure.map
      (finiteComplexQuotientTestFunctional C μ)
      (finiteComplexQuotientGaussian C β hβ) = MeasureTheory.Measure.map L base := by
    unfold finiteComplexQuotientGaussian
    have hquotientMeasurable : OpensMeasurableSpace (FiniteGaugeQuotient C) := ⟨by
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
    have hmeasTest : Measurable (finiteComplexQuotientTestFunctional C μ) :=
      (finiteComplexQuotientTestFunctional C μ).continuous.measurable
    have hmeasQuotient : Measurable (finiteComplexQuotientMap C) :=
      finiteComplexQuotientMap_measurable C
    rw [MeasureTheory.Measure.map_map hmeasTest hmeasQuotient]
    change MeasureTheory.Measure.map
      (⇑((finiteComplexQuotientTestFunctional C μ).comp
        (finiteComplexQuotientMap C))) base = MeasureTheory.Measure.map L base
    rw [finiteComplexQuotientTestFunctional_comp]
  rw [hmap]
  change MeasureTheory.charFun (MeasureTheory.Measure.map L base) 1 = _
  rw [MeasureTheory.charFun_map_eq_charFunDual_smul (μ := base) L 1]
  simp only [one_smul]
  rw [ProbabilityTheory.IsGaussian.charFunDual_eq, hmeanComplex, hvariance]
  simp

end FroehlichSpencer.FS82.Gaussian
end
