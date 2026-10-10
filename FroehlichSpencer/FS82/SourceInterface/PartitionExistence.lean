module
public import FroehlichSpencer.FS82.SourceInterface.SourceTheoremsBasic
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.Bases
public import FroehlichSpencer.FS82.Gaussian.FiniteQuotientGaussian
public import FroehlichSpencer.FS82.Poisson.TiltedPoisson
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
@[expose] public section
open scoped InnerProductSpace
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.SourceModels
open MeasureTheory
namespace FroehlichSpencer.FS82.QuotientGaussianBridge

open FroehlichSpencer.FS82


noncomputable def transportedFiniteLatticeHodgeInverse (R : RectBox4) :
    W R →ₗ[ℝ] W R :=
  let C := latticeExactOneComplex (B := R.side) R.origin
  let e := literalWEquivCoClosed R
  e.symm.toLinearMap.comp ((hodgeInverseOnCoClosed C).comp e.toLinearMap)

noncomputable def gateQuotientTestFunctional (R : RectBox4) (μ : W R) :
    StrongDual ℝ (LatticeGaugeQuotient R) :=
  (latticeCurl R).ker.liftQL
    (InnerProductSpace.toDualMap ℝ (RealDualField R) (μ : RealDualField R))
    (SourceInterfaceResults.latticeCurlKernel_annihilatesCoClosed_gate R μ)

noncomputable instance quotientGaussianModelInputs :
    SourceModels.HodgeGaussian.QuotientGaussianModelInputs where
  inverse := transportedFiniteLatticeHodgeInverse
  test := gateQuotientTestFunctional

local instance quotientCurlKernelClosed (R : RectBox4) :
    IsClosed ((latticeCurl R).ker : Set (RealDualField R)) :=
  Submodule.closed_of_finiteDimensional _

local instance quotientSecondCountable (R : RectBox4) :
    SecondCountableTopology (LatticeGaugeQuotient R) :=
  Topology.IsOpenQuotientMap.secondCountableTopology
    ((latticeCurl R).ker.isOpenQuotientMap_mkQL)

local instance quotientT0 (R : RectBox4) : T0Space (LatticeGaugeQuotient R) where
  t0 := by
    intro x y hxy
    by_contra hne
    obtain ⟨U, V, hU, hV, hx, hy, hdisj⟩ := t2_separation hne
    have hyU : y ∈ U :=
      (inseparable_iff_forall_isOpen.mp hxy) U hU |>.mp hx
    exact (Set.disjoint_left.mp hdisj) hyU hy

local instance quotientBorelSpace (R : RectBox4) :
    BorelSpace (LatticeGaugeQuotient R) := by
  refine ⟨?_⟩
  let q := (latticeCurl R).ker.mkQL
  have hq : Continuous q := q.continuous
  have hsurj : Function.Surjective q :=
    ((latticeCurl R).ker.isOpenQuotientMap_mkQL).surjective
  exact hq.map_eq_borel hsurj

noncomputable def literalInternalOneFormEquiv (R : RectBox4) :
    RealDualField R ≃ₗ[ℝ]
      EuclideanSpace ℝ (SourceDualOneCells R.side) :=
  LinearEquiv.refl ℝ (RealDualField R)

theorem literalToInternal_finsupp (R : RectBox4)
    (x : EuclideanSpace ℝ (SourceDualOneCells R.side)) :
    euclideanToFinsupp R ((literalInternalOneFormEquiv R).symm x) =
      Gaussian.euclideanToFinsupp x := by
  ext a
  change x a = x a
  rfl

theorem sourceD0_literalCurl_zero (R : RectBox4)
    (u : EuclideanSpace ℝ (SourceDualZeroCells R.side)) :
    latticeCurl R
      ((literalInternalOneFormEquiv R).symm
        ((latticeExactOneComplex (B := R.side) R.origin).d₀ u)) = 0 := by
  let C := latticeExactOneComplex (B := R.side) R.origin
  let lit : RealDualField R := (literalInternalOneFormEquiv R).symm (C.d₀ u)
  have hD1 : sourceDualD₁ (sourceDualD₀ u) = 0 := by
    have h := congrArg (fun f : EuclideanSpace ℝ (SourceDualZeroCells R.side) →ₗ[ℝ]
        EuclideanSpace ℝ (SourceDualTwoCells R.side) => f u)
      (sourceDualD₁_comp_D₀_zero (B := R.side))
    simpa [LinearMap.comp_apply] using h
  have hbridge := sourceDualD₁_physical_bridge R.origin (sourceDualD₀ u)
  have htwisted : latticeOrientationSignTwist
      (sourceRealLatticeCoboundary
        (sourcePhysicalDualZeroExtension R.origin
          (dualOrientationSignTwist (sourceDualOneToChain (sourceDualD₀ u))))) = 0 := by
    have hbridge0 := hbridge
    rw [hD1] at hbridge0
    simpa [sourceDualTwoToChain] using hbridge0.symm
  have hcurl0 : sourceRealLatticeCoboundary
      (sourcePhysicalDualZeroExtension R.origin
        (dualOrientationSignTwist (sourceDualOneToChain (sourceDualD₀ u)))) = 0 := by
    have h := congrArg latticeOrientationSignTwist htwisted
    simpa [latticeOrientationSignTwist_involutive] using h
  have hq0 := literalToInternal_finsupp R (C.d₀ u)
  have hq1 : Gaussian.euclideanToFinsupp (C.d₀ u) =
      sourceDualTMap (Gaussian.euclideanToFinsupp (sourceDualD₀ u)) := by
    change Gaussian.euclideanToFinsupp
      (sourceDualTLinear (sourceDualD₀ u)) = _
    ext e
    simp [sourceDualTLinear, sourceDualTMap_apply]
  have hq := hq0.trans hq1
  have hext := sourcePhysicalDualZeroExtension_sourceDualTMap R.origin
    (sourceDualD₀ u)
  have hreal : Cubical.realifyLatticeLinearMap Cubical.latticeCoboundary =
      sourceRealLatticeCoboundary := by
    apply LinearMap.ext
    intro q
    apply Finsupp.ext
    intro c
    simp [Cubical.realifyLatticeLinearMap, sourceRealLatticeCoboundary,
      Cubical.latticeCoboundary_basis]
  change latticeCurl R lit = 0
  rw [latticeCurl_bridge]
  rw [hreal]
  have hlit : (lit : EuclideanSpace ℝ (Cubical.LambdaStarLinks R.side)) = C.d₀ u := by
    change (literalInternalOneFormEquiv R).symm (C.d₀ u) = C.d₀ u
    rfl
  change sourceRealLatticeCoboundary
    (Cubical.lambdaStarRealZeroExtension R.origin
      (Gaussian.euclideanToFinsupp
        (lit : EuclideanSpace ℝ (Cubical.LambdaStarLinks R.side)))) = 0
  rw [hlit]
  rw [hq1]
  rw [← hext]
  exact hcurl0

theorem sourceQuotientDualExhaustion (R : RectBox4)
    (L : StrongDual ℝ (LatticeGaugeQuotient R)) :
    ∃ μ : W R, SourceModels.HodgeGaussian.latticeQuotientTestFunctional R μ = L := by
  classical
  let C := latticeExactOneComplex (B := R.side) R.origin
  let i : EuclideanSpace ℝ (SourceDualOneCells R.side) ≃L[ℝ] RealDualField R :=
    (literalInternalOneFormEquiv R).symm.toContinuousLinearEquiv
  let q0 : RealDualField R →L[ℝ] LatticeGaugeQuotient R :=
    (latticeCurl R).ker.mkQL
  let q : EuclideanSpace ℝ (SourceDualOneCells R.side) →L[ℝ]
      LatticeGaugeQuotient R := q0.comp i.toContinuousLinearMap
  have hqsurj : Function.Surjective q :=
    Function.Surjective.comp
      ((latticeCurl R).ker.isOpenQuotientMap_mkQL).surjective
      i.surjective
  let Lpull : StrongDual ℝ (EuclideanSpace ℝ (SourceDualOneCells R.side)) := L.comp q
  let x : EuclideanSpace ℝ (SourceDualOneCells R.side) :=
    (InnerProductSpace.toDual ℝ
      (EuclideanSpace ℝ (SourceDualOneCells R.side))).symm Lpull
  have hrepr : Lpull = InnerProductSpace.toDualMap ℝ
      (EuclideanSpace ℝ (SourceDualOneCells R.side)) x := by
    change Lpull = (InnerProductSpace.toDual ℝ
      (EuclideanSpace ℝ (SourceDualOneCells R.side))) x
    exact ((InnerProductSpace.toDual ℝ
      (EuclideanSpace ℝ (SourceDualOneCells R.side))).apply_symm_apply Lpull).symm
  have horth (u : EuclideanSpace ℝ (SourceDualZeroCells R.side)) :
      inner ℝ x (C.d₀ u) = 0 := by
    have hcurleq : latticeCurl R (i (C.d₀ u)) = 0 := by
      exact sourceD0_literalCurl_zero R u
    have hqzero : q (C.d₀ u) = 0 := by
      change (Submodule.Quotient.mk (i (C.d₀ u)) : LatticeGaugeQuotient R) = 0
      exact (Submodule.Quotient.mk_eq_zero (latticeCurl R).ker).2
        (LinearMap.mem_ker.mpr hcurleq)
    calc
      inner ℝ x (C.d₀ u) =
          InnerProductSpace.toDualMap ℝ
            (EuclideanSpace ℝ (SourceDualOneCells R.side)) x (C.d₀ u) := by simp
      _ = Lpull (C.d₀ u) := by rw [hrepr]
      _ = L (q (C.d₀ u)) := rfl
      _ = 0 := by rw [hqzero]; simp
  have hclosed : C.d₀.adjoint x = 0 := by
    have hz : inner ℝ (C.d₀.adjoint x) (C.d₀.adjoint x) = 0 := by
      calc
      inner ℝ (C.d₀.adjoint x) (C.d₀.adjoint x) =
          inner ℝ (C.d₀ (C.d₀.adjoint x)) x := by
            rw [LinearMap.adjoint_inner_right]
      _ = inner ℝ x (C.d₀ (C.d₀.adjoint x)) := real_inner_comm _ _
      _ = 0 := horth (C.d₀.adjoint x)
    exact inner_self_eq_zero.mp hz
  have hxclosed : x ∈ coClosed C := by
    change C.d₀.adjoint x = 0
    exact hclosed
  let μ : W R := (literalWEquivCoClosed R).symm ⟨x, hxclosed⟩
  have hμval : literalInternalOneFormEquiv R (μ : RealDualField R) = x := by
    have heq := (literalWEquivCoClosed R).apply_symm_apply ⟨x, hxclosed⟩
    have hval := congrArg Subtype.val heq
    rw [Surface.literalWEquivCoClosed_apply_val R μ] at hval
    exact hval
  have htestcomp :
      (gateQuotientTestFunctional R μ).comp q =
        InnerProductSpace.toDualMap ℝ
          (EuclideanSpace ℝ (SourceDualOneCells R.side)) x := by
    ext y
    change InnerProductSpace.toDualMap ℝ (RealDualField R)
        (μ : RealDualField R) (i y) =
      InnerProductSpace.toDualMap ℝ
        (EuclideanSpace ℝ (SourceDualOneCells R.side)) x y
    simp only [InnerProductSpace.toDualMap_apply_apply]
    change inner ℝ (literalInternalOneFormEquiv R (μ : RealDualField R)) y =
      inner ℝ x y
    rw [hμval]
  have hpull : Lpull = (gateQuotientTestFunctional R μ).comp q := by
    rw [hrepr, htestcomp]
  refine ⟨μ, ?_⟩
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨v, rfl⟩ := hqsurj y
  exact congrArg (fun F : StrongDual ℝ (RealDualField R) => F v) hpull.symm

noncomputable def sourceQuotientGaussianCandidate (R : RectBox4) (β : ℝ)
    (_hβ : 0 < β) : Measure (LatticeGaugeQuotient R) := by
  let C := latticeExactOneComplex (B := R.side) R.origin
  let i : EuclideanSpace ℝ (SourceDualOneCells R.side) ≃L[ℝ] RealDualField R :=
    (literalInternalOneFormEquiv R).symm.toContinuousLinearEquiv
  let q0 : RealDualField R →L[ℝ] LatticeGaugeQuotient R :=
    (latticeCurl R).ker.mkQL
  let q : EuclideanSpace ℝ (SourceDualOneCells R.side) →L[ℝ]
      LatticeGaugeQuotient R := q0.comp i.toContinuousLinearMap
  letI : (finiteComplexCovarianceMatrix C β).PosSemidef :=
    finiteComplexCovarianceMatrix_posSemidef C _hβ.le
  exact Measure.map q
    (ProbabilityTheory.multivariateGaussian 0 (finiteComplexCovarianceMatrix C β))

theorem sourceQuotientGaussianCandidate_isProbability (R : RectBox4) (β : ℝ)
    (hβ : 0 < β) :
    IsProbabilityMeasure (sourceQuotientGaussianCandidate R β hβ) := by
  let C := latticeExactOneComplex (B := R.side) R.origin
  let i : EuclideanSpace ℝ (SourceDualOneCells R.side) ≃L[ℝ] RealDualField R :=
    (literalInternalOneFormEquiv R).symm.toContinuousLinearEquiv
  let q0 : RealDualField R →L[ℝ] LatticeGaugeQuotient R :=
    (latticeCurl R).ker.mkQL
  let q : EuclideanSpace ℝ (SourceDualOneCells R.side) →L[ℝ]
      LatticeGaugeQuotient R := q0.comp i.toContinuousLinearMap
  let : (finiteComplexCovarianceMatrix C β).PosSemidef :=
    finiteComplexCovarianceMatrix_posSemidef C hβ.le
  have hbase : IsProbabilityMeasure
      (ProbabilityTheory.multivariateGaussian 0 (finiteComplexCovarianceMatrix C β)) := by
    rw [ProbabilityTheory.multivariateGaussian]
    infer_instance
  change IsProbabilityMeasure
    (Measure.map q
      (ProbabilityTheory.multivariateGaussian 0 (finiteComplexCovarianceMatrix C β)))
  constructor
  rw [Measure.map_apply q.continuous.measurable MeasurableSet.univ]
  simp [hbase.measure_univ]

theorem sourceQuotientGaussianCandidate_spec (R : RectBox4) (β : ℝ)
    (hβ : 0 < β) :
    SourceModels.HodgeGaussian.SourceQuotientGaussianSpec R β hβ
      (sourceQuotientGaussianCandidate R β hβ) := by
  constructor
  · exact sourceQuotientGaussianCandidate_isProbability R β hβ
  · intro μ
    let C := latticeExactOneComplex (B := R.side) R.origin
    let μint := literalWEquivCoClosed R μ
    let i : EuclideanSpace ℝ (SourceDualOneCells R.side) ≃L[ℝ] RealDualField R :=
      (literalInternalOneFormEquiv R).symm.toContinuousLinearEquiv
    let q0 : RealDualField R →L[ℝ] LatticeGaugeQuotient R :=
      (latticeCurl R).ker.mkQL
    let q : EuclideanSpace ℝ (SourceDualOneCells R.side) →L[ℝ]
        LatticeGaugeQuotient R := q0.comp i.toContinuousLinearMap
    let base := ProbabilityTheory.multivariateGaussian 0
      (finiteComplexCovarianceMatrix C β)
    let : (finiteComplexCovarianceMatrix C β).PosSemidef :=
      finiteComplexCovarianceMatrix_posSemidef C hβ.le
    have hμval : literalInternalOneFormEquiv R (μ : RealDualField R) =
        (μint : EuclideanSpace ℝ (SourceDualOneCells R.side)) := by
      exact (Surface.literalWEquivCoClosed_apply_val R μ).symm
    have htestcomp : (gateQuotientTestFunctional R μ).comp q =
        InnerProductSpace.toDualMap ℝ
          (EuclideanSpace ℝ (SourceDualOneCells R.side))
            (μint : EuclideanSpace ℝ (SourceDualOneCells R.side)) := by
      ext y
      change InnerProductSpace.toDualMap ℝ (RealDualField R)
          (μ : RealDualField R) (i y) =
        InnerProductSpace.toDualMap ℝ
          (EuclideanSpace ℝ (SourceDualOneCells R.side)) μint y
      simp only [InnerProductSpace.toDualMap_apply_apply]
      change inner ℝ (literalInternalOneFormEquiv R (μ : RealDualField R)) y =
        inner ℝ (μint : EuclideanSpace ℝ (SourceDualOneCells R.side)) y
      rw [hμval]
    have hsourceMap : Measure.map
        (SourceModels.HodgeGaussian.latticeQuotientTestFunctional R μ)
        (sourceQuotientGaussianCandidate R β hβ) =
        Measure.map
          (InnerProductSpace.toDualMap ℝ
            (EuclideanSpace ℝ (SourceDualOneCells R.side)) μint) base := by
      change Measure.map (gateQuotientTestFunctional R μ) (Measure.map q base) = _
      rw [Measure.map_map
        (gateQuotientTestFunctional R μ).continuous.measurable q.continuous.measurable]
      change Measure.map ((gateQuotientTestFunctional R μ).comp q) base = _
      rw [htestcomp]
    have hcharAmbient : MeasureTheory.charFun
        (Measure.map
          (InnerProductSpace.toDualMap ℝ
            (EuclideanSpace ℝ (SourceDualOneCells R.side)) μint) base) 1 =
        Complex.exp (-↑(inner ℝ (μint : EuclideanSpace ℝ (SourceDualOneCells R.side))
          ((β • finiteComplexAmbientCovariance C) μint) / 2)) := by
      calc
        _ = MeasureTheory.charFunDual base
            (InnerProductSpace.toDualMap ℝ
              (EuclideanSpace ℝ (SourceDualOneCells R.side)) μint) := by
          rw [MeasureTheory.charFun_map_eq_charFunDual_smul]
          simp
        _ = MeasureTheory.charFun base (μint :
            EuclideanSpace ℝ (SourceDualOneCells R.side)) :=
          (MeasureTheory.charFun_eq_charFunDual_toDualMap
            (μint : EuclideanSpace ℝ (SourceDualOneCells R.side))).symm
        _ = Complex.exp (-↑(inner ℝ (μint : EuclideanSpace ℝ
              (SourceDualOneCells R.side))
            ((β • finiteComplexAmbientCovariance C) μint) / 2)) :=
          finiteComplexAmbientGaussian_characteristic C hβ.le
            (μint : EuclideanSpace ℝ (SourceDualOneCells R.side))
    have hinvval : literalInternalOneFormEquiv R
        ((transportedFiniteLatticeHodgeInverse R μ : W R) : RealDualField R) =
          (hodgeInverseOnCoClosed C μint :
            EuclideanSpace ℝ (SourceDualOneCells R.side)) := by
      rfl
    have hcov : finiteComplexAmbientCovariance C μint =
        literalInternalOneFormEquiv R
          ((transportedFiniteLatticeHodgeInverse R μ : W R) : RealDualField R) := by
      rw [finiteComplexAmbientCovariance_coClosed_apply]
      exact hinvval.symm
    have hpair : inner ℝ (μint : EuclideanSpace ℝ (SourceDualOneCells R.side))
        ((β • finiteComplexAmbientCovariance C) μint) / 2 =
        (β / 2) * inner ℝ (μ : RealDualField R)
          ((transportedFiniteLatticeHodgeInverse R μ : W R) : RealDualField R) := by
      rw [LinearMap.smul_apply, hcov]
      rw [real_inner_smul_right]
      rw [← hμval]
      change β * inner ℝ (μ : RealDualField R)
          ((transportedFiniteLatticeHodgeInverse R μ : W R) : RealDualField R) / 2 = _
      ring
    rw [hsourceMap, hcharAmbient, hpair]
    change Complex.exp (-↑((β / 2) * inner ℝ (μ : RealDualField R)
        ((transportedFiniteLatticeHodgeInverse R μ : W R) : RealDualField R))) = _
    rfl

theorem existsUnique_sourceQuotientGaussian (R : RectBox4) (β : ℝ)
    (hβ : 0 < β) :
    ∃! P : Measure (LatticeGaugeQuotient R),
      SourceModels.HodgeGaussian.SourceQuotientGaussianSpec R β hβ P := by
  refine ⟨sourceQuotientGaussianCandidate R β hβ,
    sourceQuotientGaussianCandidate_spec R β hβ, ?_⟩
  intro P hP
  let : IsProbabilityMeasure P := hP.1
  let : IsProbabilityMeasure (sourceQuotientGaussianCandidate R β hβ) :=
    sourceQuotientGaussianCandidate_isProbability R β hβ
  have hchar (L : StrongDual ℝ (LatticeGaugeQuotient R)) :
      MeasureTheory.charFunDual P L =
        MeasureTheory.charFunDual (sourceQuotientGaussianCandidate R β hβ) L := by
    obtain ⟨μ, hL⟩ := sourceQuotientDualExhaustion R L
    rw [← hL]
    have hPμ := hP.2 μ
    have hCμ := (sourceQuotientGaussianCandidate_spec R β hβ).2 μ
    rw [MeasureTheory.charFun_map_eq_charFunDual_smul] at hPμ hCμ
    simpa using hPμ.trans hCμ.symm
  have hfun : MeasureTheory.charFunDual P =
      MeasureTheory.charFunDual (sourceQuotientGaussianCandidate R β hβ) := by
    funext L
    exact hchar L
  exact SourceInterfaceResults.finite_measure_characteristic_uniqueness_helper hfun

theorem summable_integerQuadraticGaussian_majorant {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ℝ) (ha : 0 < a) :
    Summable (fun x : ι → ℤ => Real.exp (-a * ∑ i, (x i : ℝ) ^ 2)) := by
  open FroehlichSpencer.FS82.Poisson in
  let A : Matrix ι ι ℝ := Matrix.diagonal (fun _ => a / Real.pi)
  have hA : A.PosDef := by
    dsimp [A]
    exact Matrix.PosDef.diagonal (by intro i; positivity)
  have hC := summable_primal_quadratic_exp A hA (0 : ι → ℂ)
  refine hC.norm.congr ?_
  intro x
  rw [primalQuadraticExp]
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, Complex.norm_exp]
  simp [A, Matrix.diagonal]
  have hpa : Real.pi * (a / Real.pi) = a := by
    field_simp [Real.pi_ne_zero]
  calc
    Real.pi * (∑ i, (x i : ℝ) * (a / Real.pi) * (x i : ℝ)) =
        ∑ i, Real.pi * ((x i : ℝ) * (a / Real.pi) * (x i : ℝ)) := by
      rw [Finset.mul_sum]
    _ = ∑ i, (Real.pi * (a / Real.pi)) * (x i : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (Real.pi * (a / Real.pi)) * ∑ i, (x i : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
    _ = a * ∑ i, (x i : ℝ) ^ 2 := by rw [hpa]

theorem summable_integerQuadraticExp_pullback_of_injective
    {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → ι → ℤ) (hf : Function.Injective f) (a : ℝ) (ha : 0 < a) :
    Summable (fun c : α => Real.exp (-a * ∑ i, (f c i : ℝ) ^ 2)) := by
  let w : (ι → ℤ) → NNReal := fun x =>
    ⟨Real.exp (-a * ∑ i, (x i : ℝ) ^ 2), Real.exp_nonneg _⟩
  have hwReal : Summable (fun x : ι → ℤ =>
      Real.exp (-a * ∑ i, (x i : ℝ) ^ 2)) :=
    summable_integerQuadraticGaussian_majorant a ha
  have hw : Summable w := by
    apply (NNReal.summable_coe).1
    change Summable (fun x : ι → ℤ => (w x : ℝ))
    exact hwReal
  have hpull := NNReal.summable_comp_injective hw hf
  apply (NNReal.summable_coe).2 hpull

end FroehlichSpencer.FS82.QuotientGaussianBridge
end
