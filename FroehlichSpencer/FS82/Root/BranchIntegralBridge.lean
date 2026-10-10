/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Root.SignedCurrent
public import FroehlichSpencer.FS82.Root.SourceCovariance
public import FroehlichSpencer.FS82.Root.JensenBudget

/-!
# the gauge-averaged branch integral on the source quotient Gaussian

For a family of integer currents whose non-co-closed modes vanish, the real-tilted gauge-averaged
integral of `∏ᵢ (1 + Kᵢ cos α(ϱᵢ))` equals the completed square `exp(t²β/2 · ⟨τ, V_Λ τ⟩)` times the
source quotient Gaussian integral of the product over the co-closed currents, with each phase
translated by `θᵢ = ⟨ϱᵢ, tβ V_Λ τ⟩`.

This combines FS82 (2.47) (non-co-closed currents drop) with
the translation (2.97)–(2.98).

Both sides are evaluated as the same finite sum over sign assignments.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace FroehlichSpencer.FS82.Root.MomentComparisonAssembly

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.GaugeAveraged
open FroehlichSpencer.FS82.Gaussian.RenormalizedFamily.RenormalizedCharacters
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.SourceCoercivity
open FroehlichSpencer.FS82.Moment.SourceConstructor

variable {B : Box 4}

/-! ## Products of mode terms -/

theorem charTerm_prod {ι : Type*} [Fintype ι] (K u : ι → ℝ) (σ : ι → Sign) :
    ∏ i, charTerm (K i) (u i) (σ i) =
      (∏ i, signCoeff (K i) (σ i)) *
        Complex.exp (Complex.I * ((∑ i, signValue (σ i) * u i : ℝ) : ℂ)) := by
  unfold charTerm
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 2
  push_cast
  rw [Finset.mul_sum]

/-! ## The gauge-averaged side -/

theorem inner_two_pi_mode_signedCurrent {ι : Type*} [Fintype ι]
    (J : ι → IntegerCurrent B) (σ : ι → Sign)
    (α : EuclideanSpace ℝ (SourceDualOneCells B)) :
    inner ℝ ((2 * Real.pi) • latticeIntegerModeVector (B := B) (signedCurrent J σ)) α =
      ∑ i, signValue (σ i) *
        inner ℝ ((2 * Real.pi) • latticeIntegerModeVector (B := B) (J i)) α := by
  rw [latticeIntegerModeVector_signedCurrent, Finset.smul_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm, real_inner_smul_left, signValue_eq_signInt]

/-- The tilted gauge-averaged integral of a cosine product, as a sum over sign assignments of the
completed-square factors of the signed sums. -/
theorem gaugeAveraged_cosineProduct_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ℝ) (hβ : 0 ≤ β) (t : ℝ) (τ : SourceW B) (K : ι → ℝ)
    (J : ι → IntegerCurrent B) :
    ∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
      Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ (SourceDualOneCells B)) α : ℝ) : ℂ) *
        ((∏ i, (1 + K i * Real.cos (inner ℝ
          ((2 * Real.pi) • latticeIntegerModeVector (B := B) (J i)) α)) : ℝ) : ℂ)
      ∂gaugeAveragedRealGaussian (B := B) β hβ =
    ∑ σ : ι → Sign, (∏ i, signCoeff (K i) (σ i)) *
      physicalGaussianTiltCompletedSquareFactor (B := B) β hβ t τ (signedCurrent J σ) := by
  classical
  have hpt : ∀ α : EuclideanSpace ℝ (SourceDualOneCells B),
      ((∏ i, (1 + K i * Real.cos (inner ℝ
          ((2 * Real.pi) • latticeIntegerModeVector (B := B) (J i)) α)) : ℝ) : ℂ) =
        physicalRealTrigPolynomial (B := B) Finset.univ
          (fun σ : ι → Sign => ∏ i, signCoeff (K i) (σ i)) (signedCurrent J) α := by
    intro α
    simp only [Complex.ofReal_prod, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul]
    refine (familyCosineExpansion K (fun i => inner ℝ
      ((2 * Real.pi) • latticeIntegerModeVector (B := B) (J i)) α)).trans ?_
    unfold physicalRealTrigPolynomial
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [charTerm_prod, inner_two_pi_mode_signedCurrent, mul_comm Complex.I]
  simp_rw [hpt]
  exact gaugeAveragedRealGaussian_tiltedTrigPolynomial_integral_completedSquare
    β hβ t τ Finset.univ _ _

/-! ## The source quotient side -/

theorem sourceDualQuotientTestFunctional_mk (x : coClosed (sourceDualComplex B))
    (a : EuclideanSpace ℝ (SourceDualOneCells B)) :
    sourceDualQuotientTestFunctional x (sourceDualQuotientMap (B := B) a) =
      inner ℝ (x : EuclideanSpace ℝ (SourceDualOneCells B)) a := by
  have h := congrArg (fun F : StrongDual ℝ (EuclideanSpace ℝ (SourceDualOneCells B)) => F a)
    (sourceDualQuotientTestFunctional_comp x)
  simpa using h

theorem sourceDualQuotientMap_surjective :
    Function.Surjective (sourceDualQuotientMap (B := B)) := by
  intro q
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨a, rfl⟩

theorem testFunctional_latticeToSource_sum {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (m : ι → SourceW B) (q : FiniteGaugeQuotient (sourceDualComplex B)) :
    sourceDualQuotientTestFunctional
        (latticeToSourceCoClosed Cubical.originZero (∑ i, c i • m i)) q =
      ∑ i, c i * sourceDualQuotientTestFunctional
        (latticeToSourceCoClosed Cubical.originZero (m i)) q := by
  obtain ⟨a, rfl⟩ := sourceDualQuotientMap_surjective q
  simp only [sourceDualQuotientTestFunctional_mk, latticeToSourceCoClosed_coe]
  rw [Submodule.coe_sum, map_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul, map_smul, real_inner_smul_left]

/-- The source quotient Gaussian integral of a translated cosine product of twisted lattice
co-closed tests, as a sum over sign assignments. -/
theorem sourceQuotient_cosineProduct_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ℝ} (hβ : 0 ≤ β) (K θ : ι → ℝ) (m : ι → SourceW B) :
    ((∫ q, ∏ i, (1 + K i * Real.cos
        (sourceDualQuotientTestFunctional
          (latticeToSourceCoClosed Cubical.originZero (m i)) q + θ i))
        ∂sourceDualQuotientGaussian (B := B) β hβ : ℝ) : ℂ) =
      ∑ σ : ι → Sign, (∏ i, signCoeff (K i) (σ i)) *
        Complex.exp (Complex.I * ((∑ i, signValue (σ i) * θ i : ℝ) : ℂ)) *
        Complex.exp (-(((β / 2) * quotientCovarianceQuadratic
          (latticeExactOneComplex (B := B) Cubical.originZero)
          (∑ i, signValue (σ i) • m i) : ℝ) : ℂ)) := by
  classical
  have hG : IsProbabilityMeasure (sourceDualQuotientGaussian (B := B) β hβ) :=
    sourceDualQuotientGaussian_is_probability hβ
  let L : (ι → Sign) → FiniteGaugeQuotient (sourceDualComplex B) → ℝ := fun σ q =>
    sourceDualQuotientTestFunctional
      (latticeToSourceCoClosed Cubical.originZero (∑ i, signValue (σ i) • m i)) q
  have hLmeas : ∀ σ, Measurable (L σ) := fun σ =>
    measurable_sourceDualQuotientTestFunctional _
  have hpt : ∀ q : FiniteGaugeQuotient (sourceDualComplex B),
      ((∏ i, (1 + K i * Real.cos
        (sourceDualQuotientTestFunctional
          (latticeToSourceCoClosed Cubical.originZero (m i)) q + θ i)) : ℝ) : ℂ) =
      ∑ σ : ι → Sign, ((∏ i, signCoeff (K i) (σ i)) *
        Complex.exp (Complex.I * ((∑ i, signValue (σ i) * θ i : ℝ) : ℂ))) *
        Complex.exp (Complex.I * ((L σ q : ℝ) : ℂ)) := by
    intro q
    simp only [Complex.ofReal_prod, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul]
    refine (familyCosineExpansion K (fun i => sourceDualQuotientTestFunctional
      (latticeToSourceCoClosed Cubical.originZero (m i)) q + θ i)).trans ?_
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [charTerm_prod, mul_assoc, ← Complex.exp_add, ← mul_add]
    congr 3
    have hsum : (∑ i, signValue (σ i) * (sourceDualQuotientTestFunctional
        (latticeToSourceCoClosed Cubical.originZero (m i)) q + θ i)) =
        (∑ i, signValue (σ i) * θ i) + L σ q := by
      simp only [L]
      rw [testFunctional_latticeToSource_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hsum
  rw [← integral_complex_ofReal]
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    rw [integral_const_mul, sourceDualQuotientGaussian_integral_cexp hβ]
  · intro σ _
    refine Integrable.const_mul ?_ _
    refine Integrable.of_bound (by have := hLmeas σ; fun_prop : Measurable _).aestronglyMeasurable
      1 (ae_of_all _ fun q => ?_)
    simp [Complex.norm_exp]

/-! ## The bridge -/

/-- The lattice co-closed mode of an integer current, and zero when the current is not
co-closed. -/
noncomputable def closedMode (J : IntegerCurrent B) : SourceW B := by
  classical
  exact if h : currentDivergence J = 0 then
    sourcePhysicalCurrentCoClosed Cubical.originZero J h else 0

/-- The activity of a current, and zero when the current is not co-closed. -/
noncomputable def closedActivity (K : ℝ) (J : IntegerCurrent B) : ℝ := by
  classical
  exact if currentDivergence J = 0 then K else 0

theorem closedMode_of_closed (J : IntegerCurrent B) (h : currentDivergence J = 0) :
    closedMode J = sourcePhysicalCurrentCoClosed Cubical.originZero J h := by
  simp [closedMode, h]

theorem closedActivity_of_closed (K : ℝ) (J : IntegerCurrent B)
    (h : currentDivergence J = 0) : closedActivity K J = K := by
  simp [closedActivity, h]

theorem closedActivity_of_not_closed (K : ℝ) (J : IntegerCurrent B)
    (h : currentDivergence J ≠ 0) : closedActivity K J = 0 := by
  simp [closedActivity, h]

/-- **The branch bridge.** Under the vanishing of non-co-closed modes, the real-tilted
gauge-averaged integral of the raw cosine product is the completed square times the source
quotient Gaussian integral of the co-closed product with translated phases. -/
theorem branch_bridge {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ℝ) (hβ : 0 ≤ β) (t : ℝ) (τ : SourceW B) (K : ι → ℝ)
    (J : ι → IntegerCurrent B)
    (hVD : ∀ σ : ι → Sign, (∃ i, σ i ≠ 0 ∧ currentDivergence (J i) ≠ 0) →
      currentDivergence (signedCurrent J σ) ≠ 0) :
    ∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
      Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ (SourceDualOneCells B)) α : ℝ) : ℂ) *
        ((∏ i, (1 + K i * Real.cos (inner ℝ
          ((2 * Real.pi) • latticeIntegerModeVector (B := B) (J i)) α)) : ℝ) : ℂ)
      ∂gaugeAveragedRealGaussian (B := B) β hβ =
    Complex.exp ((((t ^ 2 * β / 2) *
        quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) τ : ℝ)) : ℂ) *
      ((∫ q, ∏ i, (1 + closedActivity (K i) (J i) * Real.cos
        (sourceDualQuotientTestFunctional
            (latticeToSourceCoClosed Cubical.originZero (closedMode (J i))) q +
          sourcePhysicalTheta β τ t (J i)))
        ∂sourceDualQuotientGaussian (B := B) β hβ : ℝ) : ℂ) := by
  classical
  rw [gaugeAveraged_cosineProduct_integral, sourceQuotient_cosineProduct_integral,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hσ : ∃ i, σ i ≠ 0 ∧ currentDivergence (J i) ≠ 0
  · obtain ⟨i, hi, hdiv⟩ := hσ
    have h1 : physicalGaussianTiltCompletedSquareFactor (B := B) β hβ t τ
        (signedCurrent J σ) = 0 := by
      simp [physicalGaussianTiltCompletedSquareFactor, hVD σ ⟨i, hi, hdiv⟩]
    have h2 : ∏ j, signCoeff (closedActivity (K j) (J j)) (σ j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by
        rw [closedActivity_of_not_closed _ _ hdiv]
        exact signCoeff_zero_of_ne _ hi)
    rw [h1, h2]
    simp
  · push Not at hσ
    have hdivσ : currentDivergence (signedCurrent J σ) = 0 :=
      signedCurrent_divergence_eq_zero J σ hσ
    have hcoef : ∏ i, signCoeff (closedActivity (K i) (J i)) (σ i) =
        ∏ i, signCoeff (K i) (σ i) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases h0 : σ i = 0
      · rw [h0]
        exact signCoeff_eq_of_zero _ _
      · rw [closedActivity_of_closed _ _ (hσ i h0)]
    have hmodeCoe : ∀ i, σ i ≠ 0 →
        (closedMode (J i) : EuclideanSpace ℝ (SourceDualOneCells B)) =
          sourceDualTLinear (sourcePhysicalCurrentVector (J i)) := by
      intro i h0
      rw [closedMode_of_closed _ (hσ i h0)]
      rfl
    have hsv0 : ∀ i, σ i = 0 → signValue (σ i) = 0 := by
      intro i h0
      rw [h0]
      simp [signValue]
    have hmode : (∑ i, signValue (σ i) • closedMode (J i) : SourceW B) =
        sourcePhysicalCurrentCoClosed Cubical.originZero (signedCurrent J σ) hdivσ := by
      apply Subtype.ext
      rw [sourcePhysicalCurrentCoClosed_eq_two_pi_mode, latticeIntegerModeVector_signedCurrent,
        Submodule.coe_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Submodule.coe_smul]
      by_cases h0 : σ i = 0
      · rw [hsv0 i h0, (signInt_eq_zero_iff (σ i)).mpr h0]
        simp
      · rw [closedMode_of_closed _ (hσ i h0), sourcePhysicalCurrentCoClosed_eq_two_pi_mode,
          signValue_eq_signInt, smul_comm]
    have hθ : (∑ i, signValue (σ i) * sourcePhysicalTheta β τ t (J i)) =
        β * t * inner ℝ τ (latticeVΛ (B := B) Cubical.originZero
          (sourcePhysicalCurrentCoClosed Cubical.originZero (signedCurrent J σ) hdivσ)) := by
      have hsymm : inner ℝ τ (latticeVΛ (B := B) Cubical.originZero
            (sourcePhysicalCurrentCoClosed Cubical.originZero (signedCurrent J σ) hdivσ)) =
          inner ℝ (latticeVΛ (B := B) Cubical.originZero τ :
              EuclideanSpace ℝ (SourceDualOneCells B))
            ((sourcePhysicalCurrentCoClosed Cubical.originZero (signedCurrent J σ) hdivσ :
              SourceW B) : EuclideanSpace ℝ (SourceDualOneCells B)) := by
        rw [Submodule.coe_inner]
        exact (hodgeInverseOnCoClosed_symmetric _ τ _).symm
      rw [hsymm, ← hmode, Submodule.coe_sum, inner_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Submodule.coe_smul, real_inner_smul_right]
      by_cases h0 : σ i = 0
      · rw [hsv0 i h0]
        simp
      · rw [hmodeCoe i h0, sourcePhysicalTheta, sourceGaussianTranslation,
          real_inner_smul_right, real_inner_comm]
        ring
    have hQτ : quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) τ =
        inner ℝ τ (latticeVΛ (B := B) Cubical.originZero τ) := by
      rw [Submodule.coe_inner]
      rfl
    have hR : ∀ a p e1 e2 : ℂ, a * (p * e1 * e2) = p * (a * e1 * e2) :=
      fun _ _ _ _ => by ring
    rw [hcoef, hmode, hθ, hQτ, hR (Complex.exp _) (∏ i, signCoeff (K i) (σ i))]
    congr 1
    simp only [physicalGaussianTiltCompletedSquareFactor, hdivσ, dite_true,
      FroehlichSpencer.FS82.Moment.QuotientGaussian.sourcePhysicalGaussianCharacter]
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring

end FroehlichSpencer.FS82.Root.MomentComparisonAssembly

end
