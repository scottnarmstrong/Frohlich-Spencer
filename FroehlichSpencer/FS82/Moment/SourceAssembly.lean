module
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Analysis.Complex.Trigonometric
public import FroehlichSpencer.FS82.Currents.BranchEnvelope
public import FroehlichSpencer.FS82.Gaussian.SourceDualComplex

public import FroehlichSpencer.FS82.Moment.Comparison
public import FroehlichSpencer.FS82.Gaussian.LatticeComplex

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Moment.SourceAssembly

open FroehlichSpencer.FS82
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.Comparison

/--
The source's finite Hodge field, on the repository's dual two-cell carrier.

The complex and covariance inverse are physical-box lattice types.
-/
noncomputable def sourceHodgeField {B : Cubical.Box 4}
    (μ : Gaussian.coClosed (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero))
    (scale : ℝ) (p : Gaussian.SourceDualTwoCells B) : ℝ :=
  ((Gaussian.latticeExactOneComplex (B := B) Cubical.originZero).d₁ (scale •
    (Gaussian.latticeVΛ (B := B) Cubical.originZero μ : EuclideanSpace ℝ (Currents.Link B)))) p

theorem sourceHodgeField_energy {B : Cubical.Box 4}
    (μ : Gaussian.coClosed (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero)) (scale : ℝ) :
    (∑ p : Gaussian.SourceDualTwoCells B,
      (sourceHodgeField μ scale p)^2) =
      scale^2 * Gaussian.quotientCovarianceQuadratic
        (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero) μ := by
  classical
  let C := Gaussian.latticeExactOneComplex (B := B) Cubical.originZero
  let Vμ : EuclideanSpace ℝ (Currents.Link B) :=
    (Gaussian.latticeVΛ (B := B) Cubical.originZero μ : EuclideanSpace ℝ (Currents.Link B))
  let y : EuclideanSpace ℝ (Gaussian.SourceDualTwoCells B) :=
    (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero).d₁ (scale • Vμ)
  have hfield : ∀ p, sourceHodgeField μ scale p = y p := by
    intro p
    rfl
  have hsum : (∑ p : Gaussian.SourceDualTwoCells B,
      (sourceHodgeField μ scale p)^2) = inner ℝ y y := by
    rw [PiLp.inner_apply]
    simp only [hfield, y, Real.inner_apply]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hscale : inner ℝ y y = scale^2 *
      inner ℝ ((Gaussian.latticeExactOneComplex (B := B) Cubical.originZero).d₁ Vμ) ((Gaussian.latticeExactOneComplex (B := B) Cubical.originZero).d₁ Vμ) := by
    dsimp [y]
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  have hcurl : inner ℝ ((Gaussian.latticeExactOneComplex (B := B) Cubical.originZero).d₁ Vμ)
      ((Gaussian.latticeExactOneComplex (B := B) Cubical.originZero).d₁ Vμ) =
      inner ℝ Vμ (C.d₁.adjoint (C.d₁ Vμ)) := by
    change inner ℝ (C.d₁ Vμ) (C.d₁ Vμ) =
      inner ℝ Vμ (C.d₁.adjoint (C.d₁ Vμ))
    exact (LinearMap.adjoint_inner_right C.d₁ Vμ (C.d₁ Vμ)).symm
  have hVμ : Gaussian.formLaplacian C Vμ = μ := by
    have h := Gaussian.hodgeOnCoClosed_hodgeInverse C μ
    exact congrArg Subtype.val h
  have hcov : inner ℝ Vμ (C.d₁.adjoint (C.d₁ Vμ)) =
      Gaussian.quotientCovarianceQuadratic C μ := by
    change inner ℝ Vμ (Gaussian.formLaplacian C Vμ) =
      Gaussian.quotientCovarianceQuadratic C μ
    rw [hVμ]
    unfold Gaussian.quotientCovarianceQuadratic
    exact real_inner_comm _ _
  rw [hsum, hscale, hcurl, hcov]


/--
Source-facing moment data on lattice co-closed carrier.

The current
and Fourier identities are constructor outputs or explicit source gates;
`P` uses the canonical finite co-closed, current, link, and plaquette types.
-/
structure SourceJointMomentData {B : Cubical.Box 4}
    {Ensemble Fourier : Type*}
    [Fintype Ensemble] [DecidableEq Ensemble] [Fintype Fourier]
    (P : Comparison.PackingBudget Unit
      (Gaussian.coClosed (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero)) Ensemble
      (Currents.IntegerCurrent B) (Gaussian.SourceDualTwoCells B)) where
  beta : ℝ
  moment : Gaussian.coClosed (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero) → ℝ → ℝ
  residual : Gaussian.coClosed (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero) → ℝ → ℝ
  fourierWeight : Gaussian.coClosed (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero) → Fourier → ℝ
  fourierVariance : Gaussian.coClosed (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero) → Fourier → ℝ
  fourierPhase : Gaussian.coClosed (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero) → Fourier → ℝ
  quotientGaussianFactor : Gaussian.coClosed (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero) → Fourier → ℝ
  ensembleWeight : Gaussian.coClosed (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero) → Ensemble → ℝ
  betaPos : 0 < beta
  fourierWeightNonneg : ∀ μ j, 0 ≤ fourierWeight μ j
  fourierVarianceNonneg : ∀ μ j, 0 ≤ fourierVariance μ j
  quotientGaussianCurrentMoment : ∀ μ j,
    quotientGaussianFactor μ j =
      Comparison.scalarGaussianFactor (beta * fourierVariance μ j)
  ensembleWeightNonneg : ∀ μ γ, 0 ≤ ensembleWeight μ γ
  ensembleWeightSum : ∀ μ, ∑ γ, ensembleWeight μ γ = 1
  currentExpansion : ∀ μ t, residual μ t = ∑ j,
    fourierWeight μ j * quotientGaussianFactor μ j *
      Real.cos (t * fourierPhase μ j)
  currentNormalization : ∀ μ,
    (∑ j, fourierWeight μ j * quotientGaussianFactor μ j) = 1
  momentFactorization : ∀ μ t,
    moment μ t = Real.exp ((t^2 * beta / 2) *
      Gaussian.quotientCovarianceQuadratic
        (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero) μ) * residual μ t
  A0_1 : ∀ μ t,
    (∑ γ, ensembleWeight μ γ *
      (∏ i ∈ P.currents () μ γ, Real.exp (-P.error () μ t γ i))) ≤ residual μ t


end FroehlichSpencer.FS82.Moment.SourceAssembly
