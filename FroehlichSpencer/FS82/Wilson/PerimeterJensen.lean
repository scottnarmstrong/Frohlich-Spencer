/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Root.FiniteMomentComparison

/-!
# Jensen on the root branches with phase representatives

The first root bounds the residual of `sourceDualMoment β μ t` below by Jensen on every terminal
branch, with the translated phases `θ_ρ = sourcePhysicalTheta β μ t ρ` (FS82 (2.98)–(2.101)).

The
cosine of a phase depends on it only modulo `2π`.

So the same Jensen step holds with any
representatives `θ'_ρ` such that `θ_ρ + θ'_ρ ∈ 2πℤ`, and its error is `Σ_ρ γ(z_ρ) θ'_ρ²`.

This is
the form used for the Wilson loop, FS82 (2.57) and (2.79)–(2.80): there `θ'_ρ` is the pairing of
the loop field with a filling of `ρ`, which is of perimeter size, while `θ_ρ` is of area size.

* `branch_jensen_of_phaseRepresentative`: the estimate for one branch.
* `sourceDualMoment_lower_of_phaseRepresentatives`: the outer mixture over the root branches.
-/

open MeasureTheory
open scoped BigOperators
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Moment.ExpansionIntegral
open FroehlichSpencer.FS82.Moment.SourceEnsembleConstructor
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Root.MomentComparisonAssembly

@[expose] public section

namespace FroehlichSpencer.FS82.Wilson

variable {B : Cubical.Box 4}

/-- **Jensen on a branch with phase representatives.** If every lineage with a nonzero amplitude
has a representative `θ' i` with `θ_i + θ' i ∈ 2πℤ`, then the tilted branch integral is at least
the Gaussian factor times `exp(−Σ γ(z_i) θ'_i²)` times the untilted one. -/
theorem branch_jensen_of_phaseRepresentative {β β₁ : ℝ} {q : Link B → ℤ} {z : ℤ → ℝ}
    {s : CurrentState B} (H : BranchHyp β β₁ q z s) (τ : SourceW B) (t : ℝ)
    (θ' : {h : ExpansionLineage B // h ∈ s} → ℝ)
    (hθ : ∀ i, branchAmp β q z s i ≠ 0 → ∃ n : ℤ,
      sourcePhysicalTheta β τ t (stateCurrent q s i) + θ' i = 2 * Real.pi * (n : ℝ)) :
    Real.exp ((t ^ 2 * β / 2) *
          quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) τ) *
        Real.exp (-∑ i, SourceJensen.sourceJensenGamma (branchAmp β q z s i) * θ' i ^ 2) *
        (gaugeBranchIntegral β H.beta_pos.le 0 τ (stateActivity q z s) (stateCurrent q s)).re ≤
      (gaugeBranchIntegral β H.beta_pos.le t τ (stateActivity q z s) (stateCurrent q s)).re := by
  classical
  have hprob : IsProbabilityMeasure (branchReducedLaw H) :=
    familyReducedLaw_isProbability _ _ (branch_plaquetteIndependent H) H.beta_pos
      (state_hdisjoint H.separated)
  have hJ := cosineProduct_jensen (branchReducedLaw H)
    (familyReducedLaw_map_neg _ _ (branch_plaquetteIndependent H) β)
    (branchAmp β q z s) θ' (branchAngle H) (branchAmp_nonneg H) (branchAmp_lt_one H)
    (fun i => measurable_familyAngle _ _ _ i) (fun i y => familyAngle_neg _ _ _ i y)
  have hshift : ∀ y, (∏ i, (1 + branchAmp β q z s i *
      Real.cos (branchAngle H i y + sourcePhysicalTheta β τ t (stateCurrent q s i)))) =
      ensembleShiftedCosineDensity (branchAmp β q z s) θ' (branchAngle H) y := by
    intro y
    unfold ensembleShiftedCosineDensity
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h0 : branchAmp β q z s i = 0
    · simp [h0]
    · obtain ⟨n, hn⟩ := hθ i h0
      have harg : branchAngle H i y + sourcePhysicalTheta β τ t (stateCurrent q s i) =
          (branchAngle H i y - θ' i) + (n : ℝ) * (2 * Real.pi) := by linarith
      rw [harg, Real.cos_add_int_mul_two_pi]
  rw [branch_reduced_identity H τ t, branch_zero_identity H τ, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  simp_rw [hshift]
  exact hJ

/-- **The source dual moment with phase representatives.** Above the root threshold, if on every
root branch the translated phases of the lineages with nonzero amplitude have representatives
modulo `2π` whose Jensen budget is at most `E`, then

`exp(t²β/2 · ⟨μ, V_Λ μ⟩) · exp(−E) ≤ ⟨e^{tα(μ)}⟩`.

No condition on the box is needed here; the box enters only through the bound `E`. -/
theorem sourceDualMoment_lower_of_phaseRepresentatives {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (μ : SourceW B) (t E : ℝ)
    (hE : ∀ ω : RootBranch B, ∃ θ' : RootBranchIndex ω → ℝ,
      (∀ i, branchAmp β (rootBranchFrequency ω) (sourceAssignmentIntegerActivity rootActivity)
          (rootBranchState ω) i ≠ 0 → ∃ n : ℤ,
        sourcePhysicalTheta β μ t (stateCurrent (rootBranchFrequency ω) (rootBranchState ω) i) +
          θ' i = 2 * Real.pi * (n : ℝ)) ∧
      ∑ i, SourceJensen.sourceJensenGamma
          (branchAmp β (rootBranchFrequency ω) (sourceAssignmentIntegerActivity rootActivity)
            (rootBranchState ω) i) * θ' i ^ 2 ≤ E) :
    Real.exp ((t ^ 2 * β / 2) *
        quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ) * Real.exp (-E) ≤
      sourceDualMoment β μ t := by
  obtain ⟨hw0, hw1, hOuter⟩ := sourceDualMoment_hasSum_branch_of_positiveType (rootBeta_pos hβ)
    rootActivity hasSum_inactiveWeight_rootActivity inactiveWeight_rootActivity_nonneg
    (fun q => rootActivity_pos _) μ (rootTerms (B := B)) rootTerms_spec
  set G := Real.exp ((t ^ 2 * β / 2) *
    quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ) with hG
  have hbranch : ∀ ω : RootBranch B, G * Real.exp (-E) ≤
      sourceExpansionBranchMoment β t (rootBeta_pos hβ).le μ rootActivity rootTerms ω := by
    intro ω
    obtain ⟨θ', hθ, hsum⟩ := hE ω
    have H := rootHyp hβ ω
    rw [sourceExpansionBranchMoment_eq_gaugeBranch (rootBeta_pos hβ).le t μ ω]
    have hpos := branch_zero_pos H μ
    have hJ := branch_jensen_of_phaseRepresentative H μ t θ' hθ
    rw [le_div_iff₀ hpos]
    refine le_trans ?_ hJ
    refine mul_le_mul_of_nonneg_right ?_ hpos.le
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hsum)) (Real.exp_pos _).le
  have hconst : HasSum (fun ω : RootBranch B =>
      sourceExpansionBranchWeight β (rootBeta_pos hβ) rootActivity rootTerms ω *
        (G * Real.exp (-E))) (1 * (G * Real.exp (-E))) := hw1.mul_right _
  rw [one_mul] at hconst
  exact hasSum_le (fun ω => mul_le_mul_of_nonneg_left (hbranch ω) (hw0 ω)) hconst (hOuter t)

end FroehlichSpencer.FS82.Wilson

end
