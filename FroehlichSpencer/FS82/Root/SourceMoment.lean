module

public import FroehlichSpencer.FS82.Poisson.SourceModel
public import FroehlichSpencer.FS82.Moment.SourceConstructor

/-!
# FS82 (2.93): the source dual moment and its Poisson factorization

The discrete dual law (2.26)–(2.29) on the source carrier is tree-gauge
chord model with matrix `A = K_CC/(2πβ)`.

Its real exponential moment
`⟨e^{t⟨τ,n⟩}⟩` is the ratio `dualMoment A τ t` of two real lattice sums.

The finite Poisson identity (/) factors it as the continuous Gaussian
moment times a real residual: for positive definite `A`,

`dualMoment A τ t = exp(t²/(4π) ⟨τ,A⁻¹τ⟩) · chordResidual A τ t`,

where `chordResidual` is the normalized dual-Gaussian average of
`cos(t·φ(k))`.

The residual is at most one, which is the upper half of (2.93).

On the source carrier, with `τ` the chord restriction of a co-closed test form
`μ`, the Gaussian exponent is `t²β/2 · (μ, V_Λ μ)`.
-/

@[expose] public section

open scoped BigOperators
open Matrix

namespace FroehlichSpencer.FS82.Root

open FroehlichSpencer.FS82
open FroehlichSpencer.FS82.Poisson

noncomputable section

section Finite

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real primal weight `exp(-π⟨n,An⟩ + t⟨τ,n⟩)` of the tree-gauge dual
law. -/
def dualPrimalWeight (A : Matrix ι ι ℝ) (τ : ι → ℝ) (t : ℝ) (n : ι → ℤ) : ℝ :=
  Real.exp (-Real.pi * (∑ i, ∑ j, (n i : ℝ) * A i j * (n j : ℝ)) +
    t * ∑ i, τ i * (n i : ℝ))

/-- The real exponential moment `⟨e^{t⟨τ,n⟩}⟩` of the discrete Gaussian law
with weight `exp(-π⟨n,An⟩)` on integer chord fields. -/
def dualMoment (A : Matrix ι ι ℝ) (τ : ι → ℝ) (t : ℝ) : ℝ :=
  (∑' n : ι → ℤ, dualPrimalWeight A τ t n) /
    (∑' n : ι → ℤ, dualPrimalWeight A τ 0 n)

omit [DecidableEq ι] in
theorem testedPrimalTerm_eq_ofReal (A : Matrix ι ι ℝ) (τ : ι → ℝ) (t : ℝ)
    (n : ι → ℤ) :
    testedPrimalTerm A τ t n = (dualPrimalWeight A τ t n : ℂ) := by
  unfold testedPrimalTerm dualPrimalWeight
  rw [Complex.ofReal_exp]
  push_cast
  ring_nf

omit [DecidableEq ι] in
/--
The complex tested expectation of is the real dual moment.
-/
theorem testedExpectation_eq_dualMoment (A : Matrix ι ι ℝ) (τ : ι → ℝ)
    (t : ℝ) :
    testedExpectation A τ t = (dualMoment A τ t : ℂ) := by
  unfold testedExpectation dualMoment
  simp only [testedPrimalTerm_eq_ofReal]
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_tsum, ← Complex.ofReal_div]

/-- The Gaussian quadratic form `⟨τ, A⁻¹ τ⟩` of the completed square. -/
def chordQuadratic (A : Matrix ι ι ℝ) (τ : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, τ i * A⁻¹ i j * τ j

/-- The symmetrized dual phase `⟨τ, A⁻¹ k⟩` of a dual integer field `k`. -/
def chordPhase (A : Matrix ι ι ℝ) (τ : ι → ℝ) (k : ι → ℤ) : ℝ :=
  ∑ i, ∑ j, (τ i * A⁻¹ i j * (k j : ℝ) + (k i : ℝ) * A⁻¹ i j * τ j) / 2

/-- The real part of one tilted dual Poisson term. -/
theorem dualQuadraticExp_realTilt_re (A : Matrix ι ι ℝ) (τ : ι → ℝ) (t : ℝ)
    (k : ι → ℤ) :
    (dualQuadraticExp A (realTiltParameter τ t) k).re =
      Real.exp (t ^ 2 / (4 * Real.pi) * chordQuadratic A τ) *
        dualGaussianWeight A k * Real.cos (t * chordPhase A τ k) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold dualQuadraticExp
  rw [Complex.exp_re]
  have hre : ((Real.pi : ℂ) * ∑ i, ∑ j,
      (realTiltParameter τ t i - Complex.I * (k i : ℂ)) * ((A⁻¹ i j : ℝ) : ℂ) *
        (realTiltParameter τ t j - Complex.I * (k j : ℂ))).re =
      t ^ 2 / (4 * Real.pi) * chordQuadratic A τ +
        (-Real.pi * ∑ i, ∑ j, (k i : ℝ) * A⁻¹ i j * (k j : ℝ)) := by
    simp only [Complex.re_sum, realTiltParameter,
      Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.intCast_re, Complex.intCast_im, chordQuadratic, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    field_simp
    ring
  have him : ((Real.pi : ℂ) * ∑ i, ∑ j,
      (realTiltParameter τ t i - Complex.I * (k i : ℂ)) * ((A⁻¹ i j : ℝ) : ℂ) *
        (realTiltParameter τ t j - Complex.I * (k j : ℂ))).im =
      -(t * chordPhase A τ k) := by
    simp only [Complex.im_sum, realTiltParameter,
      Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.intCast_re, Complex.intCast_im, chordPhase, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    field_simp
    ring
  rw [hre, him, Real.exp_add, Real.cos_neg]
  rfl

/-- The real cosine residual of the dual Poisson representation. -/
def chordResidual (A : Matrix ι ι ℝ) (τ : ι → ℝ) (t : ℝ) : ℝ :=
  (∑' k : ι → ℤ, dualGaussianWeight A k * Real.cos (t * chordPhase A τ k)) /
    xi A

theorem summable_dualQuadraticExp_re (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (τ : ι → ℝ) (t : ℝ) :
    Summable (fun k : ι → ℤ =>
      dualGaussianWeight A k * Real.cos (t * chordPhase A τ k)) := by
  have hS : Summable (fun k : ι → ℤ =>
      (dualQuadraticExp A (realTiltParameter τ t) k).re) :=
    Complex.reCLM.summable (summable_dual_quadratic_exp A hA _)
  simp only [dualQuadraticExp_realTilt_re, mul_assoc] at hS
  exact (summable_mul_left_iff (ne_of_gt (Real.exp_pos _))).mp hS

theorem summable_dualGaussianWeight' (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    Summable (dualGaussianWeight A) := by
  have h := summable_dualQuadraticExp_re A hA (fun _ => 0) 0
  simpa using h

/-- **Poisson factorization.** The dual moment is the continuous Gaussian
moment times the cosine residual. -/
theorem dualMoment_eq_gaussian_mul_residual (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (τ : ι → ℝ) (t : ℝ) :
    dualMoment A τ t =
      Real.exp (t ^ 2 / (4 * Real.pi) * chordQuadratic A τ) *
        chordResidual A τ t := by
  have h := congrArg Complex.re (tested_poisson_ratio A hA τ t)
  rw [testedExpectation_eq_dualMoment, Complex.ofReal_re, Complex.div_ofReal_re,
    Complex.re_tsum (summable_dual_quadratic_exp A hA _)] at h
  rw [h, chordResidual, mul_div_assoc', ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro k
  rw [dualQuadraticExp_realTilt_re]
  ring

theorem chordResidual_le_one (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (τ : ι → ℝ) (t : ℝ) : chordResidual A τ t ≤ 1 := by
  have hxi := xi_pos A hA
  rw [chordResidual, div_le_one hxi]
  apply Summable.tsum_le_tsum _ (summable_dualQuadraticExp_re A hA τ t)
    (summable_dualGaussianWeight' A hA)
  intro k
  have hw : 0 ≤ dualGaussianWeight A k := (Real.exp_pos _).le
  calc dualGaussianWeight A k * Real.cos (t * chordPhase A τ k)
      ≤ dualGaussianWeight A k * 1 :=
        mul_le_mul_of_nonneg_left (Real.cos_le_one _) hw
    _ = dualGaussianWeight A k := mul_one _


end Finite

section Source

open FroehlichSpencer.FS82.Moment.SourceConstructor

variable {B : Cubical.Box 4}

/--
source chord matrix `K_CC/(2πβ)` on the canonical carrier.
-/
abbrev sourceChordMatrix (β : ℝ) :
    Matrix (sourceRootedTree B).Chord (sourceRootedTree B).Chord ℝ :=
  scaledChordMatrix (sourceRootedTree B)
    (sourceFinitePoissonModel (B := B) Cubical.originZero) β

/-- The link values of a co-closed source test form. -/
def sourceLinkValues (μ : SourceW B) : SourcePoissonEdge B → ℝ :=
  fun e => (μ : EuclideanSpace ℝ (Gaussian.SourceDualOneCells B)) e

/-- The chord coordinates `τ = μ|_C` of a source test form. In tree gauge
`n|_tree = 0`, so `α(μ) = ⟨n, μ⟩ = ⟨n|_C, τ⟩`. -/
def sourceChordTest (μ : SourceW B) : (sourceRootedTree B).Chord → ℝ :=
  (sourceRootedTree B).restrictChord (sourceLinkValues μ)

/--
The source observable of (2.93): the exponential moment
`⟨e^{t α(μ)}⟩_Λ` of the discrete dual law (2.26)–(2.29), in tree
gauge with weight `exp(-⟨n, K n⟩/(2β))`.
-/
def sourceDualMoment (β : ℝ) (μ : SourceW B) (t : ℝ) : ℝ :=
  dualMoment (sourceChordMatrix (B := B) β) (sourceChordTest μ) t

/-- The cosine residual of the source dual moment. -/
def sourceResidual (β : ℝ) (μ : SourceW B) (t : ℝ) : ℝ :=
  chordResidual (sourceChordMatrix (B := B) β) (sourceChordTest μ) t

/--
complex tested expectation at the chord test of `μ` is the real
source dual moment.
-/
theorem sourceFiniteModelTestedExpectation_eq_sourceDualMoment (β : ℝ)
    (μ : SourceW B) (t : ℝ) :
    sourceFiniteModelTestedExpectation (B := B) Cubical.originZero β
      (sourceChordTest μ) t = (sourceDualMoment β μ t : ℂ) :=
  testedExpectation_eq_dualMoment _ _ _

/--
A lattice co-closed form is co-closed for rooted tree.
-/
theorem sourceLinkValues_coClosed (μ : SourceW B) :
    RootedTreeGauge.CoClosed (sourceRootedTree B) (sourceLinkValues μ) := by
  rw [RootedTreeGauge.coClosed_iff_orthogonalToCoboundaries]
  intro p
  change ∑ e, sourceLinkValues μ e * sourceTreeCoboundary B p e = 0
  obtain ⟨u, hu⟩ := (sourceLatticeD0_range_eq_treeCoboundary (B := B)
    Cubical.originZero
      (WithLp.toLp 2 (fun e => sourceTreeCoboundary B p e))).mpr
      ⟨p, fun _ => rfl⟩
  have hker : (Gaussian.latticeExactOneComplex (B := B)
      Cubical.originZero).d₀.adjoint
        (μ : EuclideanSpace ℝ (Gaussian.SourceDualOneCells B)) = 0 :=
    LinearMap.mem_ker.mp μ.2
  have hinner : inner ℝ ((Gaussian.latticeExactOneComplex (B := B)
      Cubical.originZero).d₀ u)
        (μ : EuclideanSpace ℝ (Gaussian.SourceDualOneCells B)) = 0 := by
    rw [← LinearMap.adjoint_inner_right, hker, inner_zero_right]
  rw [hu, PiLp.inner_apply] at hinner
  simpa [sourceLinkValues, mul_comm] using hinner

/--
The Hodge inverse solves matrix equation `K u = μ`.
-/
theorem sourcePoissonK_mulVec_hodgeInverse (μ : SourceW B) :
    (sourceFinitePoissonModel (B := B) Cubical.originZero).K *ᵥ
        (fun e => (Gaussian.hodgeInverseOnCoClosed
          (sourceLatticeComplex (B := B)) μ :
            EuclideanSpace ℝ (Gaussian.SourceDualOneCells B)) e) =
      sourceLinkValues μ := by
  change (sourcePoissonMatrix (B := B) Cubical.originZero).mulVec _ = _
  rw [sourcePoissonMatrix_mulVec, ← Gaussian.latticeFormLaplacian_eq_stencil]
  have h : Gaussian.formLaplacian (sourceLatticeComplex (B := B))
      (Gaussian.hodgeInverseOnCoClosed (sourceLatticeComplex (B := B)) μ :
        EuclideanSpace ℝ (Gaussian.SourceDualOneCells B)) =
      (μ : EuclideanSpace ℝ (Gaussian.SourceDualOneCells B)) :=
    congrArg Subtype.val
      (Gaussian.hodgeOnCoClosed_hodgeInverse (sourceLatticeComplex (B := B)) μ)
  funext e
  simp only [WithLp.toLp_ofLp]
  rw [h]
  rfl

/-- The completed-square exponent on the source carrier:
`⟨τ, A⁻¹ τ⟩ = 2πβ · (μ, V_Λ μ)`. -/
theorem sourceChordQuadratic_eq {β : ℝ} (hβ : 0 < β) (μ : SourceW B) :
    chordQuadratic (sourceChordMatrix (B := B) β) (sourceChordTest μ) =
      2 * Real.pi * β *
        Gaussian.quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ := by
  classical
  let T := sourceRootedTree B
  let M := sourceFinitePoissonModel (B := B) Cubical.originZero
  let K := reducedChordMatrix T M
  have hc : (2 * Real.pi * β)⁻¹ ≠ 0 := by positivity
  have hdet : IsUnit K.det :=
    (Matrix.isUnit_iff_isUnit_det K).mp (reducedChordMatrix_posDef T M).isUnit
  have hinv : (sourceChordMatrix (B := B) β)⁻¹ = (2 * Real.pi * β) • K⁻¹ := by
    change ((Units.mk0 _ hc : ℝˣ) • K)⁻¹ = _
    rw [Matrix.inv_smul' _ _ hdet, Units.smul_def, Units.val_inv_eq_inv_val,
      Units.val_mk0, inv_inv]
  let u : SourcePoissonEdge B → ℝ := fun e =>
    (Gaussian.hodgeInverseOnCoClosed (sourceLatticeComplex (B := B)) μ :
      EuclideanSpace ℝ (Gaussian.SourceDualOneCells B)) e
  have hvar := finiteModel_variational_identity_of_solution T M
    (sourceLinkValues_coClosed μ) (sourceLinkValues_coClosed μ) u
    (sourcePoissonK_mulVec_hodgeInverse μ)
  have hQ : Gaussian.quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ =
      dotProduct (sourceLinkValues μ) u := by
    rw [Gaussian.quotientCovarianceQuadratic, PiLp.inner_apply]
    simp [dotProduct, sourceLinkValues, u, mul_comm]
  rw [hQ, hvar, chordQuadratic, hinv]
  simp only [Matrix.smul_apply, smul_eq_mul, dotProduct, Matrix.mulVec,
    Finset.mul_sum, sourceChordTest]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Poisson factorization on the source carrier.**
`⟨e^{tα(μ)}⟩_Λ = exp(t²β/2 · (μ, V_Λ μ)) · R(t)`. -/
theorem sourceDualMoment_eq_gaussian_mul_residual {β : ℝ} (hβ : 0 < β)
    (μ : SourceW B) (t : ℝ) :
    sourceDualMoment β μ t =
      Real.exp ((t ^ 2 * β / 2) *
        Gaussian.quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ) *
        sourceResidual β μ t := by
  rw [sourceDualMoment, dualMoment_eq_gaussian_mul_residual _
    (scaledChordMatrix_posDef _ _ hβ), sourceChordQuadratic_eq hβ]
  congr 2
  field_simp
  ring

theorem sourceResidual_le_one {β : ℝ} (hβ : 0 < β) (μ : SourceW B) (t : ℝ) :
    sourceResidual β μ t ≤ 1 :=
  chordResidual_le_one _ (scaledChordMatrix_posDef _ _ hβ) _ _

/-- **The upper half of (2.93)** on the source carrier, with no hypothesis:
`⟨e^{tα(μ)}⟩_Λ ≤ exp(t²β/2 · (μ, V_Λ μ))`. -/
theorem sourceDualMoment_le_gaussian {β : ℝ} (hβ : 0 < β) (μ : SourceW B)
    (t : ℝ) :
    sourceDualMoment β μ t ≤
      Real.exp ((t ^ 2 * β / 2) *
        Gaussian.quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ) := by
  rw [sourceDualMoment_eq_gaussian_mul_residual hβ]
  calc _ ≤ Real.exp ((t ^ 2 * β / 2) *
        Gaussian.quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ) * 1 :=
        mul_le_mul_of_nonneg_left (sourceResidual_le_one hβ μ t)
          (Real.exp_pos _).le
    _ = _ := mul_one _

end Source

end

end FroehlichSpencer.FS82.Root
