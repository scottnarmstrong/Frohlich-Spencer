/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Root.BranchExpansionData

/-!
# the packing budget, the tested expansion and the Jensen package of a branch

Targets 1 and 2 of the root assembly for one terminal state: `branchExpansion` is the
`SourceTestedExpansionInput` (the object `D`), and `branchJensen` is the corrected
`RenormalizedSourceEnsembleJensenData` (the object `K`) over the ShortComponentPhase budget `branchBudget`.
-/

open MeasureTheory
open scoped BigOperators InnerProductSpace
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.GaugeAveraged
open FroehlichSpencer.FS82.Gaussian.RenormalizedFamily.RenormalizedCharacters
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Currents.LongCurrentEstimate
open FroehlichSpencer.FS82.Currents.AdaptiveTree
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Moment.SourceEnsembleConstructor
open FroehlichSpencer.FS82.Moment.SourceAssembly
open FroehlichSpencer.FS82.Root.RenormalizedInterface

@[expose] public section

namespace FroehlichSpencer.FS82.Root.MomentComparisonAssembly

variable {B : Cubical.Box 4}

section Package

variable {β β₁ : ℝ} {q : Link B → ℤ} {z : ℤ → ℝ} {s : CurrentState B}

/-- The selected links of the branch are plaquette independent. -/
theorem branch_plaquetteIndependent (H : BranchHyp β β₁ q z s) :
    PlaquetteIndependent
      (familySelected (stateCurrent q s) (branchColor β q z s)) :=
  familySelected_plaquetteIndependent _ _ (state_hplaq H.separated)

/-- The retained chord space of the branch. -/
abbrev BranchRetained (H : BranchHyp β β₁ q z s) :=
  FamilyRetained (stateCurrent q s) (branchColor β q z s) (branch_plaquetteIndependent H)

/-- The reduced Gaussian of the branch. -/
noncomputable abbrev branchReducedLaw (H : BranchHyp β β₁ q z s) :
    Measure (BranchRetained H) :=
  familyReducedLaw (stateCurrent q s) (branchColor β q z s) (branch_plaquetteIndependent H) β

/-- The renormalized angles of the branch. -/
noncomputable abbrev branchAngle (H : BranchHyp β β₁ q z s)
    (i : {h : ExpansionLineage B // h ∈ s}) : BranchRetained H → ℝ :=
  familyAngle (stateCurrent q s) (branchColor β q z s) (branch_plaquetteIndependent H) i

/-- **The reduced identity of a branch.** -/
theorem branch_reduced_identity (H : BranchHyp β β₁ q z s) (τ : SourceW B) (t : ℝ) :
    (gaugeBranchIntegral β H.beta_pos.le t τ (stateActivity q z s) (stateCurrent q s)).re =
      Real.exp ((t ^ 2 * β / 2) *
          quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) τ) *
        ∫ y, ∏ i, (1 + branchAmp β q z s i *
          Real.cos (branchAngle H i y + sourcePhysicalTheta β τ t (stateCurrent q s i)))
          ∂branchReducedLaw H :=
  family_reduced_identity _ _ (branch_plaquetteIndependent H) H.beta_pos τ _
    (state_hdisjoint H.separated) (state_hvert H.separated) t

theorem sourcePhysicalTheta_zero (β : ℝ) (τ : SourceW B) (J : IntegerCurrent B) :
    sourcePhysicalTheta β τ 0 J = 0 := by
  simp [sourcePhysicalTheta, sourceGaussianTranslation]

/-- The zero-tilt branch integral is the reduced integral of the unshifted product. -/
theorem branch_zero_identity (H : BranchHyp β β₁ q z s) (τ : SourceW B) :
    (gaugeBranchIntegral β H.beta_pos.le 0 τ (stateActivity q z s) (stateCurrent q s)).re =
      ∫ y, ensembleCosineDensity (branchAmp β q z s) (branchAngle H) y ∂branchReducedLaw H := by
  rw [branch_reduced_identity H τ 0]
  simp [sourcePhysicalTheta_zero, ensembleCosineDensity]

/-- The zero-tilt branch mass is positive. -/
theorem branch_zero_pos (H : BranchHyp β β₁ q z s) (τ : SourceW B) :
    0 < (gaugeBranchIntegral β H.beta_pos.le 0 τ (stateActivity q z s)
      (stateCurrent q s)).re := by
  classical
  rw [branch_zero_identity H τ]
  have hprob : IsProbabilityMeasure (branchReducedLaw H) :=
    familyReducedLaw_isProbability _ _ (branch_plaquetteIndependent H) H.beta_pos
      (state_hdisjoint H.separated)
  have hmeas : Measurable (ensembleCosineLogDensity (branchAmp β q z s) (branchAngle H)) :=
    measurable_ensembleCosineLogDensity _ _ fun i => measurable_familyAngle _ _ _ i
  have hexp : ∀ y, Real.exp (ensembleCosineLogDensity (branchAmp β q z s) (branchAngle H) y) =
      ensembleCosineDensity (branchAmp β q z s) (branchAngle H) y := fun y =>
    exp_logDensity_eq_cosineDensity _ _ (branchAmp_nonneg H) (branchAmp_lt_one H) y
  have hint : Integrable (fun y => Real.exp
      (ensembleCosineLogDensity (branchAmp β q z s) (branchAngle H) y)) (branchReducedLaw H) := by
    refine Integrable.of_bound (hmeas.exp).aestronglyMeasurable
      (∏ i, (1 + branchAmp β q z s i)) (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, hexp]
    exact (sourceDensity_nonneg_le _ _ (branchAmp_nonneg H) (branchAmp_lt_one H) y).2
  have hpos := integral_exp_pos hint
  simp_rw [hexp] at hpos
  exact hpos

variable (N m : ℕ) (hN : 1 ≤ N) (hm : Real.log (N + 1 : ℝ) ≤ (m : ℝ))
  (hRate : 8 ≤ sourceRenormalizedRate β β₁)
  (hmin : ∀ i : Fin 4, m ≤ B i) (hBmax : ∀ i : Fin 4, B i ≤ N)
  (H : BranchHyp β β₁ q z s)

/-- The ShortComponentPhase packing budget of the branch: the closed family with the renormalized amplitudes. -/
noncomputable def branchBudget : SourcePackingBudget B Unit :=
  renormalizedFamilyPackingBudget β β₁ N m hN hm hRate hmin hBmax
    (fun _ _ => branchFamily q s) (fun _ _ => branchZ β q z s)
    (fun _ _ => branchFamily_pairwiseDisjoint H) (fun _ _ j => branchZ_envelope H j)


noncomputable def branchExpansion :
    SourceTestedExpansionInput (B := B) (Ensemble := Unit)
      (Mode := ({h : ExpansionLineage B // h ∈ s} → Sign))
      (branchBudget N m hN hm hRate hmin hBmax H) where
  beta := β
  moment := fun μ t =>
    (gaugeBranchIntegral β H.beta_pos.le t μ (stateActivity q z s) (stateCurrent q s)).re /
      (gaugeBranchIntegral β H.beta_pos.le 0 μ (stateActivity q z s) (stateCurrent q s)).re
  localMoment := fun μ t _ =>
    (gaugeBranchIntegral β H.beta_pos.le t μ (stateActivity q z s) (stateCurrent q s)).re /
      Real.exp ((t ^ 2 * β / 2) *
        quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ)
  outerCoefficient := fun _ _ => 1
  normalizer := fun μ =>
    (gaugeBranchIntegral β H.beta_pos.le 0 μ (stateActivity q z s) (stateCurrent q s)).re
  ensembleNormalizer := fun μ _ =>
    (gaugeBranchIntegral β H.beta_pos.le 0 μ (stateActivity q z s) (stateCurrent q s)).re
  modeCoefficient := fun _ _ σ => modeCoeff (stateActivity q z s) (stateCurrent q s) σ
  modeCurrent := fun _ _ σ => closedMode (signedCurrent (stateCurrent q s) σ)
  modePhase := fun μ _ σ => β * inner ℝ μ
    (latticeVΛ (B := B) Cubical.originZero (closedMode (signedCurrent (stateCurrent q s) σ)))
  betaPos := H.beta_pos
  outerCoefficientNonneg := fun _ _ => zero_le_one
  normalizerPos := fun μ => branch_zero_pos H μ
  ensembleNormalizerNonneg := fun μ _ => (branch_zero_pos H μ).le
  partitionNormalization := by
    intro μ
    simp
  zeroShift := by
    intro μ γ
    simp
  modeCoefficientNonneg := fun _ _ σ =>
    modeCoeff_nonneg (stateActivity q z s) (fun i => (H.coeff_pos i.1 i.2).le)
      (stateCurrent q s) σ
  hOuterMoment_of_model := by
    intro μ t
    have hpos := branch_zero_pos H μ
    simp only [Finset.univ_unique, Finset.sum_singleton, one_mul]
    field_simp
  lemma2Expansion := by
    intro μ t γ
    rw [gaugeBranchIntegral_re, mul_div_cancel_left₀ _ (Real.exp_pos _).ne']
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [sourceModeCharacter_eq_scalarGaussianFactor,
      Comparison.scalarGaussianFactor_eq_exp _ (mul_nonneg H.beta_pos.le
        (quotientCovarianceQuadratic_nonneg _ _))]

theorem branchExpansion_beta : (branchExpansion N m hN hm hRate hmin hBmax H).beta = β := rfl

/--
The
bridge fields are the reduced identity of the branch at zero tilt and at tilt `t`.
-/
noncomputable def branchJensen :
    RenormalizedSourceEnsembleJensenData (I := {h : ExpansionLineage B // h ∈ s})
      (V := BranchRetained H) (branchExpansion N m hN hm hRate hmin hBmax H)
      (fun _ _ => branchZ β q z s) β β₁ where
  reducedGaussian := fun _ _ => branchReducedLaw H
  reducedProbability := fun _ _ =>
    familyReducedLaw_isProbability _ _ (branch_plaquetteIndependent H) H.beta_pos
      (state_hdisjoint H.separated)
  reducedEven := fun _ _ => familyReducedLaw_map_neg _ _ (branch_plaquetteIndependent H) β
  currentIndex := stateCurrent q s
  currentIndex_ne_zero := stateCurrent_ne_zero H.valid
  angle := fun _ _ i => branchAngle H i
  angleMeasurable := fun _ _ i => measurable_familyAngle _ _ _ i
  angleOdd := fun _ _ i y => familyAngle_neg _ _ _ i y
  theta := fun μ t _ i => -sourcePhysicalTheta β μ t (stateCurrent q s i)
  sourceActivity_envelope := fun _ _ j => branchZ_envelope H j
  sourceBranchMass := fun μ _ =>
    (gaugeBranchIntegral β H.beta_pos.le 0 μ (stateActivity q z s) (stateCurrent q s)).re
  branchMass_eq_normalizer := fun _ _ => rfl
  branchMass_eq_reducedDensity := by
    intro μ γ
    rw [branch_zero_identity H μ]
    simp only [branchZ_stateCurrent H]
  localMoment_eq_reducedDensity := by
    intro μ t γ
    change (gaugeBranchIntegral β H.beta_pos.le t μ (stateActivity q z s)
        (stateCurrent q s)).re / Real.exp ((t ^ 2 * β / 2) *
          quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ) = _
    rw [branch_reduced_identity H μ t, mul_div_cancel_left₀ _ (Real.exp_pos _).ne']
    simp only [branchZ_stateCurrent H, ensembleShiftedCosineDensity, sub_neg_eq_add]
  budget_eq_error := by
    classical
    intro μ t γ
    change SourceJensen.ensembleJensenBudget
        (fun i => branchZ β q z s (stateCurrent q s i))
        (fun i => -sourcePhysicalTheta β μ t (stateCurrent q s i)) =
      ∑ j ∈ (branchFamily q s).image (fun j : ClosedIntegerCurrent B => j.1),
        genericSourceJensenError β (fun _ _ => branchZ β q z s) μ t γ j
    rw [branchFamily_image, Finset.sum_image
      (fun i _ j _ hij => stateCurrent_injective H.separated H.valid hij), Finset.sum_filter]
    unfold SourceJensen.ensembleJensenBudget genericSourceJensenError
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [branchZ_stateCurrent H, neg_sq]
    by_cases hdiv : currentDivergence (stateCurrent q s i) = 0
    · simp [hdiv]
    · have h0 : branchAmp β q z s i = 0 := branchAmplitude_of_not_closed _ _ _ _ hdiv
      simp [hdiv, h0, SourceJensen.sourceJensenGamma]

end Package

end FroehlichSpencer.FS82.Root.MomentComparisonAssembly

end
