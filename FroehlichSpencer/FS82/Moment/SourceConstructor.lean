/-
The source-carrier Gaussian and Lemma 2 expansion assembly.
-/
module

public import FroehlichSpencer.FS82.Moment.SourceAssembly
public import FroehlichSpencer.FS82.Moment.SourceJensen
public import FroehlichSpencer.FS82.Currents.Expansion
public import FroehlichSpencer.FS82.Gaussian.LatticeComplex
import Mathlib.Probability.Moments.Basic

/-!
# Source-carrier Gaussian factors and finite-current Fourier expansion

The Gaussian formulas below use lattice complex.

The finite Fourier
expansion is the algebraic step that turns product over a terminal
current state into a finite sum over signed current combinations.
-/

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Moment.SourceConstructor

open FroehlichSpencer.FS82
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian

variable {B : Box 4}

noncomputable abbrev SourceW (B : Box 4) :=
  Gaussian.coClosed (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero)

noncomputable abbrev sourceLatticeComplex :=
  Gaussian.latticeExactOneComplex (B := B) Cubical.originZero


/-- The tilt direction in the finite-volume completing-the-square argument. -/
noncomputable def sourceGaussianTranslation (β t : ℝ) (μ : SourceW B) :
    EuclideanSpace ℝ (Link B) :=
  (t * β) • (Gaussian.latticeVΛ (B := B) Cubical.originZero μ :
    EuclideanSpace ℝ (Link B))


theorem sourceLatticeQuotientGaussian_characteristic
    (β : ℝ) (hβ : 0 ≤ β)
    (j : Gaussian.coClosed (sourceLatticeComplex (B := B))) :
    MeasureTheory.charFun
        (MeasureTheory.Measure.map
          (Gaussian.finiteComplexQuotientTestFunctional
            (sourceLatticeComplex (B := B)) j)
          (Gaussian.latticeQuotientGaussian (B := B)
            Cubical.originZero β hβ)) 1 =
      Complex.ofReal (Real.exp
        (-(β / 2) * Gaussian.quotientCovarianceQuadratic
          (sourceLatticeComplex (B := B)) j)) := by
  rw [Gaussian.latticeQuotientGaussian_characteristic_VΛ]
  rw [Complex.ofReal_exp]
  congr 1
  unfold Gaussian.quotientCovarianceQuadratic
  simp [Gaussian.latticeVΛ]

/-- One term in the real Fourier expansion of a finite product of cosine
factors. `current` is the signed sum of the currents selected so far. -/
structure CurrentFourierTerm (B : Box 4) where
  weight : ℝ
  current : Link B → ℤ

noncomputable def currentFourierSum
    (φ : Link B → ℝ) (terms : List (CurrentFourierTerm B)) : ℝ :=
  (terms.map fun a => a.weight *
    Real.cos (Currents.currentPhase φ a.current)).sum

noncomputable def extendCurrentFourierTerm
    (q : Link B → ℤ) (z : ℤ → ℝ) (h : ExpansionLineage B)
    (a : CurrentFourierTerm B) : List (CurrentFourierTerm B) :=
  let j := lineageCurrent q h
  let c := lineageCoefficient q z h
  [a, ⟨(c / 2) * a.weight, a.current + j⟩,
    ⟨(c / 2) * a.weight, a.current - j⟩]

noncomputable def extendCurrentFourierExpansion
    (q : Link B → ℤ) (z : ℤ → ℝ) (h : ExpansionLineage B)
    (terms : List (CurrentFourierTerm B)) : List (CurrentFourierTerm B) :=
  terms.flatMap (extendCurrentFourierTerm q z h)

private theorem currentFourierSum_extend_single
    (q : Link B → ℤ) (z : ℤ → ℝ) (h : ExpansionLineage B)
    (φ : Link B → ℝ) (a : CurrentFourierTerm B) :
    currentFourierSum φ (extendCurrentFourierTerm q z h a) =
      (a.weight * Real.cos (Currents.currentPhase φ a.current)) *
        (1 + lineageCoefficient q z h *
          Real.cos (Currents.currentPhase φ (lineageCurrent q h))) := by
  simp only [extendCurrentFourierTerm, currentFourierSum, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  rw [Currents.currentPhase_add, Currents.currentPhase_sub]
  rw [Real.cos_add, Real.cos_sub]
  ring

theorem currentFourierSum_extend
    (q : Link B → ℤ) (z : ℤ → ℝ) (h : ExpansionLineage B)
    (φ : Link B → ℝ) (terms : List (CurrentFourierTerm B)) :
    currentFourierSum φ (extendCurrentFourierExpansion q z h terms) =
      currentFourierSum φ terms *
        (1 + lineageCoefficient q z h *
          Real.cos (Currents.currentPhase φ (lineageCurrent q h))) := by
  induction terms with
  | nil => simp [extendCurrentFourierExpansion, currentFourierSum]
  | cons a rest ih =>
      change currentFourierSum φ
          (extendCurrentFourierTerm q z h a ++
            extendCurrentFourierExpansion q z h rest) = _
      have happend {xs ys : List (CurrentFourierTerm B)} :
          currentFourierSum φ (xs ++ ys) =
            currentFourierSum φ xs + currentFourierSum φ ys := by
        simp [currentFourierSum, List.map_append]
      rw [happend, currentFourierSum_extend_single, ih]
      simp only [currentFourierSum, List.map_cons, List.sum_cons]
      ring


/-! ## Source-gated finite expansion and constructor -/

/--
The real part of the tested characteristic of the quotient Gaussian
at one source co-closed current.
-/
noncomputable def sourceModeCharacter (β : ℝ) (hβ : 0 ≤ β)
    (j : SourceW B) : ℝ :=
  Complex.re (MeasureTheory.charFun
    (MeasureTheory.Measure.map
      (Gaussian.finiteComplexQuotientTestFunctional
        (sourceLatticeComplex (B := B)) j)
      (Gaussian.latticeQuotientGaussian (B := B) Cubical.originZero β hβ)) 1)

theorem sourceModeCharacter_eq_scalarGaussianFactor
    (β : ℝ) (hβ : 0 ≤ β) (j : SourceW B) :
    sourceModeCharacter (B := B) β hβ j =
      Comparison.scalarGaussianFactor
        (β * Gaussian.quotientCovarianceQuadratic
          (sourceLatticeComplex (B := B)) j) := by
  rw [sourceModeCharacter,
    sourceLatticeQuotientGaussian_characteristic β hβ j]
  simp only [Complex.ofReal_re]
  rw [Comparison.scalarGaussianFactor_eq_exp]
  · congr 1
    ring
  · exact mul_nonneg hβ
      (Gaussian.quotientCovarianceQuadratic_nonneg
        (sourceLatticeComplex (B := B)) j)

private theorem sum_univ_prod_eq {A K R : Type*} [Fintype A] [Fintype K]
    [AddCommMonoid R] (f : A × K → R) :
    (∑ x : A × K, f x) = ∑ a, ∑ k, f (a, k) := by
  classical
  rw [← Finset.sum_product]
  simp

/--
The two source inputs to the constructor.

`testedIdentity` is the exact
tested outer-moment identity after the Gaussian square has been completed.

`lemma2Expansion` is the finite /Lemma 2 expansion for each source ensemble,
with its current factors already evaluated against the quotient character.

It is intentionally a named gate: supplies the tested identity on the
source carrier, while the fixed-frequency construction supplies the local
finite expansion.
-/
structure SourceTestedExpansionInput
    {B : Box 4} {Ensemble Mode : Type*}
    [Fintype Ensemble] [DecidableEq Ensemble]
    [Fintype Mode] [DecidableEq Mode]
    (P : Comparison.PackingBudget Unit (SourceW B) Ensemble
      (Currents.IntegerCurrent B) (Gaussian.SourceDualTwoCells B)) where
  beta : ℝ
  moment : SourceW B → ℝ → ℝ
  localMoment : SourceW B → ℝ → Ensemble → ℝ
  outerCoefficient : SourceW B → Ensemble → ℝ
  normalizer : SourceW B → ℝ
  ensembleNormalizer : SourceW B → Ensemble → ℝ
  modeCoefficient : SourceW B → Ensemble → Mode → ℝ
  modeCurrent : SourceW B → Ensemble → Mode → SourceW B
  modePhase : SourceW B → Ensemble → Mode → ℝ
  betaPos : 0 < beta
  outerCoefficientNonneg : ∀ μ γ, 0 ≤ outerCoefficient μ γ
  normalizerPos : ∀ μ, 0 < normalizer μ
  ensembleNormalizerNonneg : ∀ μ γ, 0 ≤ ensembleNormalizer μ γ
  partitionNormalization : ∀ μ,
    normalizer μ = ∑ γ, outerCoefficient μ γ * ensembleNormalizer μ γ
  zeroShift : ∀ μ γ, localMoment μ 0 γ = ensembleNormalizer μ γ
  modeCoefficientNonneg : ∀ μ γ k, 0 ≤ modeCoefficient μ γ k
  /--
tested source identity, with the completed-square prefactor made
  explicit.
-/
  hOuterMoment_of_model : ∀ μ t,
    moment μ t = Real.exp ((t ^ 2 * beta / 2) *
      Gaussian.quotientCovarianceQuadratic
        (sourceLatticeComplex (B := B)) μ) *
      ((∑ γ, outerCoefficient μ γ * localMoment μ t γ) / normalizer μ)
  /--
finite Lemma 2 expansion, with each frequency tested against the
  actual lattice quotient Gaussian.
-/
  lemma2Expansion : ∀ μ t γ,
    localMoment μ t γ = ∑ k,
      modeCoefficient μ γ k *
        sourceModeCharacter (B := B) beta (le_of_lt betaPos)
          (modeCurrent μ γ k) * Real.cos (t * modePhase μ γ k)

/-- The logarithmic convexity witness for one source ensemble. `budget_eq_error`
is the source packing bridge from the cosine curvature budget to maximum-plaquette packing's exact
product of per-current errors. -/
structure SourceEnsembleJensenData
    {B : Box 4} {Ensemble Mode I V : Type*}
    [Fintype Ensemble] [DecidableEq Ensemble]
    [Fintype Mode] [DecidableEq Mode] [Fintype I]
    [MeasurableSpace V] [Neg V]
    {P : Comparison.PackingBudget Unit (SourceW B) Ensemble
      (Currents.IntegerCurrent B) (Gaussian.SourceDualTwoCells B)}
    (D : SourceTestedExpansionInput (B := B) (Ensemble := Ensemble)
      (Mode := Mode) P) where
  law : SourceW B → Ensemble → MeasureTheory.Measure V
  probability : ∀ μ γ, MeasureTheory.IsProbabilityMeasure (law μ γ)
  negMeas : Measurable (fun φ : V => -φ)
  even : ∀ μ γ,
    MeasureTheory.Measure.map (fun φ : V => -φ) (law μ γ) =
      law μ γ
  z : SourceW B → Ensemble → I → ℝ
  theta : SourceW B → ℝ → Ensemble → I → ℝ
  angle : SourceW B → Ensemble → I → V → ℝ
  zNonneg : ∀ μ γ i, 0 ≤ z μ γ i
  zLtOne : ∀ μ γ i, z μ γ i < 1
  angleOdd : ∀ μ γ i φ, angle μ γ i (-φ) = -angle μ γ i φ
  logIntegrable : ∀ μ t γ,
    MeasureTheory.Integrable
      (SourceJensen.ensembleLogShift (z μ γ) (theta μ t γ) (angle μ γ) 1)
      (law μ γ)
  expIntegrable : ∀ μ t γ,
    MeasureTheory.Integrable
      (fun φ => Real.exp (SourceJensen.ensembleLogShift
        (z μ γ) (theta μ t γ) (angle μ γ) 1 φ)) (law μ γ)
  localMoment_eq_integral : ∀ μ t γ,
    D.localMoment μ t γ = D.ensembleNormalizer μ γ *
      ∫ φ, Real.exp (SourceJensen.ensembleLogShift
        (z μ γ) (theta μ t γ) (angle μ γ) 1 φ) ∂ law μ γ
  budget_eq_error : ∀ μ t γ,
    SourceJensen.ensembleJensenBudget (z μ γ) (theta μ t γ) =
      ∑ i ∈ P.currents () μ γ, P.error () μ t γ i

theorem sourcePerEnsembleJensen
    {B : Box 4} {Ensemble Mode I V : Type*}
    [Fintype Ensemble] [DecidableEq Ensemble]
    [Fintype Mode] [DecidableEq Mode] [Fintype I]
    [MeasurableSpace V] [Neg V]
    {P : Comparison.PackingBudget Unit (SourceW B) Ensemble
      (Currents.IntegerCurrent B) (Gaussian.SourceDualTwoCells B)}
    (D : SourceTestedExpansionInput (B := B) (Ensemble := Ensemble)
      (Mode := Mode) P)
    (J : SourceEnsembleJensenData (I := I) (V := V) D)
    (μ : SourceW B) (t : ℝ) (γ : Ensemble) :
    D.ensembleNormalizer μ γ *
      (∏ i ∈ P.currents () μ γ, Real.exp (-P.error () μ t γ i)) ≤
        D.localMoment μ t γ := by
  let ν := J.law μ γ
  have hJ := @SourceJensen.perEnsembleJensen_279 I V
    inferInstance inferInstance inferInstance ν (J.probability μ γ)
    (J.even μ γ) J.negMeas (J.z μ γ) (J.theta μ t γ)
    (J.angle μ γ) (J.zNonneg μ γ) (J.zLtOne μ γ)
    (J.angleOdd μ γ) (J.logIntegrable μ t γ) (J.expIntegrable μ t γ)
  have hprod :
      (∏ i ∈ P.currents () μ γ, Real.exp (-P.error () μ t γ i)) =
        Real.exp (-SourceJensen.ensembleJensenBudget
          (J.z μ γ) (J.theta μ t γ)) := by
    calc
      _ = Real.exp (∑ i ∈ P.currents () μ γ, -P.error () μ t γ i) :=
        (SourceJensen.exp_finset_sum_eq_prod (P.currents () μ γ)
          (fun i => -P.error () μ t γ i)).symm
      _ = Real.exp (-(∑ i ∈ P.currents () μ γ, P.error () μ t γ i)) := by
        congr 1
        simp
      _ = _ := by rw [J.budget_eq_error μ t γ]
  calc
    _ = D.ensembleNormalizer μ γ *
        Real.exp (-SourceJensen.ensembleJensenBudget
          (J.z μ γ) (J.theta μ t γ)) := by rw [hprod]
    _ ≤ D.ensembleNormalizer μ γ *
        ∫ φ, Real.exp (SourceJensen.ensembleLogShift
          (J.z μ γ) (J.theta μ t γ) (J.angle μ γ) 1 φ) ∂ ν :=
      mul_le_mul_of_nonneg_left hJ (D.ensembleNormalizerNonneg μ γ)
    _ = D.localMoment μ t γ := by
      rw [J.localMoment_eq_integral μ t γ]

noncomputable def sourceResidualOfExpansion
    {B : Box 4} {Ensemble Mode : Type*}
    [Fintype Ensemble] [DecidableEq Ensemble]
    [Fintype Mode] [DecidableEq Mode]
    {P : Comparison.PackingBudget Unit (SourceW B) Ensemble
      (Currents.IntegerCurrent B) (Gaussian.SourceDualTwoCells B)}
    (D : SourceTestedExpansionInput (B := B) (Ensemble := Ensemble)
      (Mode := Mode) P) (μ : SourceW B) (t : ℝ) : ℝ :=
  (∑ γ, D.outerCoefficient μ γ * D.localMoment μ t γ) / D.normalizer μ

noncomputable def sourceEnsembleWeightOfExpansion
    {B : Box 4} {Ensemble Mode : Type*}
    [Fintype Ensemble] [DecidableEq Ensemble]
    [Fintype Mode] [DecidableEq Mode]
    {P : Comparison.PackingBudget Unit (SourceW B) Ensemble
      (Currents.IntegerCurrent B) (Gaussian.SourceDualTwoCells B)}
    (D : SourceTestedExpansionInput (B := B) (Ensemble := Ensemble)
      (Mode := Mode) P) (μ : SourceW B) (γ : Ensemble) : ℝ :=
  D.outerCoefficient μ γ * D.ensembleNormalizer μ γ / D.normalizer μ

/--
Construct all fields of `SourceJointMomentData` from the tested source
identity, finite local expansion, the lattice quotient character,
and the source cosine-Jensen witnesses.
-/
noncomputable def sourceJointMomentData_of_expansion
    {B : Box 4} {Ensemble Mode I V : Type*}
    [Fintype Ensemble] [DecidableEq Ensemble]
    [Fintype Mode] [DecidableEq Mode] [Fintype I]
    [MeasurableSpace V] [Neg V]
    {P : Comparison.PackingBudget Unit (SourceW B) Ensemble
      (Currents.IntegerCurrent B) (Gaussian.SourceDualTwoCells B)}
    (D : SourceTestedExpansionInput (B := B) (Ensemble := Ensemble)
      (Mode := Mode) P)
    (J : SourceEnsembleJensenData (I := I) (V := V) D) :
    SourceAssembly.SourceJointMomentData (B := B) (Ensemble := Ensemble)
      (Fourier := Ensemble × Mode) P := by
  classical
  refine {
    beta := D.beta
    moment := D.moment
    residual := sourceResidualOfExpansion D
    fourierWeight := fun μ jk =>
      D.outerCoefficient μ jk.1 * D.modeCoefficient μ jk.1 jk.2 / D.normalizer μ
    fourierVariance := fun μ jk => Gaussian.quotientCovarianceQuadratic
      (sourceLatticeComplex (B := B)) (D.modeCurrent μ jk.1 jk.2)
    fourierPhase := fun μ jk => D.modePhase μ jk.1 jk.2
    quotientGaussianFactor := fun μ jk => sourceModeCharacter
      (B := B) D.beta (le_of_lt D.betaPos) (D.modeCurrent μ jk.1 jk.2)
    ensembleWeight := sourceEnsembleWeightOfExpansion D
    betaPos := D.betaPos
    fourierWeightNonneg := by
      intro μ jk
      exact div_nonneg
        (mul_nonneg (D.outerCoefficientNonneg μ jk.1)
          (D.modeCoefficientNonneg μ jk.1 jk.2))
        (le_of_lt (D.normalizerPos μ))
    fourierVarianceNonneg := by
      intro μ jk
      exact Gaussian.quotientCovarianceQuadratic_nonneg
        (sourceLatticeComplex (B := B)) (D.modeCurrent μ jk.1 jk.2)
    quotientGaussianCurrentMoment := by
      intro μ jk
      exact sourceModeCharacter_eq_scalarGaussianFactor
        D.beta (le_of_lt D.betaPos) (D.modeCurrent μ jk.1 jk.2)
    ensembleWeightNonneg := by
      intro μ γ
      exact div_nonneg
        (mul_nonneg (D.outerCoefficientNonneg μ γ)
          (D.ensembleNormalizerNonneg μ γ))
        (le_of_lt (D.normalizerPos μ))
    ensembleWeightSum := by
      intro μ
      unfold sourceEnsembleWeightOfExpansion
      have hden : 0 < ∑ γ,
          D.outerCoefficient μ γ * D.ensembleNormalizer μ γ := by
        rw [← D.partitionNormalization μ]
        exact D.normalizerPos μ
      rw [← Finset.sum_div, D.partitionNormalization μ]
      exact div_self (ne_of_gt hden)
    currentExpansion := by
      intro μ t
      unfold sourceResidualOfExpansion
      calc
        _ = ∑ γ, (D.outerCoefficient μ γ * D.localMoment μ t γ) /
            D.normalizer μ := by rw [Finset.sum_div]
        _ = ∑ γ, ∑ k,
            (D.outerCoefficient μ γ * D.modeCoefficient μ γ k /
              D.normalizer μ) *
              sourceModeCharacter (B := B) D.beta (le_of_lt D.betaPos)
                (D.modeCurrent μ γ k) * Real.cos (t * D.modePhase μ γ k) := by
          apply Finset.sum_congr rfl
          intro γ hγ
          rw [D.lemma2Expansion μ t γ, Finset.mul_sum, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = ∑ jk : Ensemble × Mode,
            (D.outerCoefficient μ jk.1 * D.modeCoefficient μ jk.1 jk.2 /
              D.normalizer μ) *
              sourceModeCharacter (B := B) D.beta (le_of_lt D.betaPos)
                (D.modeCurrent μ jk.1 jk.2) * Real.cos (t * D.modePhase μ jk.1 jk.2) :=
          (sum_univ_prod_eq (fun jk : Ensemble × Mode =>
            (D.outerCoefficient μ jk.1 * D.modeCoefficient μ jk.1 jk.2 /
              D.normalizer μ) *
              sourceModeCharacter (B := B) D.beta (le_of_lt D.betaPos)
                (D.modeCurrent μ jk.1 jk.2) *
              Real.cos (t * D.modePhase μ jk.1 jk.2))).symm
    currentNormalization := by
      intro μ
      have hlocal : ∀ γ,
          D.ensembleNormalizer μ γ = ∑ k,
            D.modeCoefficient μ γ k *
              sourceModeCharacter (B := B) D.beta (le_of_lt D.betaPos)
                (D.modeCurrent μ γ k) := by
        intro γ
        have h := D.lemma2Expansion μ 0 γ
        rw [D.zeroShift μ γ] at h
        simpa using h
      have hden : 0 < ∑ γ,
          D.outerCoefficient μ γ * D.ensembleNormalizer μ γ := by
        rw [← D.partitionNormalization μ]
        exact D.normalizerPos μ
      calc
        _ = ∑ γ, ∑ k,
            (D.outerCoefficient μ γ * D.modeCoefficient μ γ k /
              D.normalizer μ) *
              sourceModeCharacter (B := B) D.beta (le_of_lt D.betaPos)
                (D.modeCurrent μ γ k) :=
          sum_univ_prod_eq (fun jk : Ensemble × Mode =>
            (D.outerCoefficient μ jk.1 * D.modeCoefficient μ jk.1 jk.2 /
              D.normalizer μ) *
              sourceModeCharacter (B := B) D.beta (le_of_lt D.betaPos)
                (D.modeCurrent μ jk.1 jk.2))
        _ = ∑ γ, D.outerCoefficient μ γ * D.ensembleNormalizer μ γ /
            D.normalizer μ := by
          apply Finset.sum_congr rfl
          intro γ hγ
          calc
            _ = (D.outerCoefficient μ γ / D.normalizer μ) *
                ∑ k, D.modeCoefficient μ γ k *
                  sourceModeCharacter (B := B) D.beta (le_of_lt D.betaPos)
                    (D.modeCurrent μ γ k) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k hk
              ring
            _ = D.outerCoefficient μ γ * D.ensembleNormalizer μ γ /
                D.normalizer μ := by rw [hlocal γ]; ring
        _ = 1 := by
          rw [← Finset.sum_div, D.partitionNormalization μ]
          exact div_self (ne_of_gt hden)
    momentFactorization := by
      intro μ t
      simpa [sourceResidualOfExpansion] using D.hOuterMoment_of_model μ t
    A0_1 := by
      intro μ t
      have hPoint : ∀ γ,
          D.ensembleNormalizer μ γ *
            (∏ i ∈ P.currents () μ γ,
              Real.exp (-P.error () μ t γ i)) ≤ D.localMoment μ t γ := by
        intro γ
        exact sourcePerEnsembleJensen D J μ t γ
      have hden : 0 < ∑ γ,
          D.outerCoefficient μ γ * D.ensembleNormalizer μ γ := by
        rw [← D.partitionNormalization μ]
        exact D.normalizerPos μ
      have hagg := SourceJensen.weightedEnsembleAggregate
        (d := fun γ => D.outerCoefficient μ γ)
        (Z := fun γ => D.ensembleNormalizer μ γ)
        (J := fun γ => D.localMoment μ t γ)
        (P := fun γ => ∏ i ∈ P.currents () μ γ,
          Real.exp (-P.error () μ t γ i))
        (fun γ => D.outerCoefficientNonneg μ γ) hPoint hden
      simpa [sourceResidualOfExpansion, sourceEnsembleWeightOfExpansion,
        D.partitionNormalization μ] using hagg
  }

end FroehlichSpencer.FS82.Moment.SourceConstructor
