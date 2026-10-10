/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Root.BranchLineage

/-!
# the tested expansion `D` and the renormalized Jensen package `K` of a branch

For one terminal state of the fixed-frequency expansion (a separated, valid set of lineages with
positive coefficients under the activity envelope), this file constructs

* the closed family `branchFamily` and its renormalized amplitudes `branchZ`, with pairwise
  disjoint supports and the envelope consumed by the ShortComponentPhase packing budget;
* the tested source expansion `branchExpansion : SourceTestedExpansionInput`, whose local moment
  is the real-tilted gauge-averaged branch integral divided by the completed square, with its
  finite Lemma 2 mode expansion over sign assignments;
* the renormalized Jensen package `branchJensen : RenormalizedSourceEnsembleJensenData`, whose
  reduced Gaussian is the retained marginal of the adaptive-tree chart law and whose bridge
  fields are the reduced identity `family_reduced_identity`.
-/

open MeasureTheory
open scoped BigOperators InnerProductSpace
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.GaugeAveraged
open FroehlichSpencer.FS82.Gaussian.RenormalizedFamily.RenormalizedCharacters
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Currents.LongCurrentEstimate
open FroehlichSpencer.FS82.Currents.AdaptiveTree
open FroehlichSpencer.FS82.Currents.SourceLinkColoring
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.SourceCoercivity
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Moment.SourceEnsembleConstructor
open FroehlichSpencer.FS82.Moment.SourceAssembly
open FroehlichSpencer.FS82.Root.RenormalizedInterface

@[expose] public section

namespace FroehlichSpencer.FS82.Root.MomentComparisonAssembly

variable {B : Cubical.Box 4}

/-! ## The real Lemma 2 expansion of the gauge-averaged branch integral -/

/-- The real coefficient of one sign in the cosine expansion. -/
noncomputable def signCoeffReal (K : ℝ) (σ : Sign) : ℝ := if σ.val = 0 then 1 else K / 2

theorem signCoeff_eq_ofReal (K : ℝ) (σ : Sign) : signCoeff K σ = (signCoeffReal K σ : ℂ) := by
  unfold signCoeff signCoeffReal
  split_ifs <;> simp

theorem signCoeffReal_nonneg (K : ℝ) (hK : 0 ≤ K) (σ : Sign) : 0 ≤ signCoeffReal K σ := by
  unfold signCoeffReal
  split_ifs <;> positivity

/-- The coefficient of one mode: the product of the sign coefficients, and zero when the signed
sum is not co-closed. -/
noncomputable def modeCoeff {ι : Type*} [Fintype ι] (K : ι → ℝ) (J : ι → IntegerCurrent B)
    (σ : ι → Sign) : ℝ := by
  classical
  exact (∏ i, signCoeffReal (K i) (σ i)) *
    (if currentDivergence (signedCurrent J σ) = 0 then 1 else 0)

theorem modeCoeff_nonneg {ι : Type*} [Fintype ι] (K : ι → ℝ) (hK : ∀ i, 0 ≤ K i)
    (J : ι → IntegerCurrent B) (σ : ι → Sign) : 0 ≤ modeCoeff K J σ := by
  unfold modeCoeff
  refine mul_nonneg (Finset.prod_nonneg fun i _ => signCoeffReal_nonneg _ (hK i) _) ?_
  split_ifs <;> norm_num

/-- The real part of the tilted branch integral as a finite positive-type sum (Lemma 2 after the
Gaussian integration): the completed square times a nonnegative combination of Gaussian
characters and cosines. -/
theorem gaugeBranchIntegral_re {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ℝ) (hβ : 0 ≤ β) (t : ℝ) (τ : SourceW B) (K : ι → ℝ) (J : ι → IntegerCurrent B) :
    (gaugeBranchIntegral β hβ t τ K J).re =
      Real.exp ((t ^ 2 * β / 2) *
          quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) τ) *
        ∑ σ : ι → Sign, modeCoeff K J σ *
          Real.exp (-(β * quotientCovarianceQuadratic (sourceLatticeComplex (B := B))
            (closedMode (signedCurrent J σ))) / 2) *
          Real.cos (t * (β * inner ℝ τ
            (latticeVΛ (B := B) Cubical.originZero (closedMode (signedCurrent J σ))))) := by
  classical
  unfold gaugeBranchIntegral
  rw [gaugeAveraged_cosineProduct_integral, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hcoef : (∏ i, signCoeff (K i) (σ i)) = ((∏ i, signCoeffReal (K i) (σ i) : ℝ) : ℂ) := by
    push_cast
    exact Finset.prod_congr rfl fun i _ => signCoeff_eq_ofReal _ _
  rw [hcoef, Complex.re_ofReal_mul]
  by_cases hdiv : currentDivergence (signedCurrent J σ) = 0
  · have hQτ : quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) τ =
        inner ℝ τ (latticeVΛ (B := B) Cubical.originZero τ) := by
      rw [Submodule.coe_inner]
      rfl
    have hX : ((β : ℂ) / 2 * ((t : ℂ) ^ 2 * (inner ℝ τ
          (latticeVΛ (B := B) Cubical.originZero τ) : ℝ)) +
        Complex.I * ((β : ℂ) * t * (inner ℝ τ (latticeVΛ (B := B) Cubical.originZero
          (sourcePhysicalCurrentCoClosed Cubical.originZero (signedCurrent J σ) hdiv)) : ℝ))) =
        (((t ^ 2 * β / 2) * inner ℝ τ (latticeVΛ (B := B) Cubical.originZero τ) : ℝ) : ℂ) +
          ((t * (β * inner ℝ τ (latticeVΛ (B := B) Cubical.originZero
            (sourcePhysicalCurrentCoClosed Cubical.originZero (signedCurrent J σ) hdiv))) :
              ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    simp only [physicalGaussianTiltCompletedSquareFactor, hdiv, dite_true,
      FroehlichSpencer.FS82.Moment.QuotientGaussian.sourcePhysicalGaussianCharacter,
      modeCoeff, ite_true, mul_one, closedMode_of_closed _ hdiv]
    rw [hX, Complex.exp_add, ← Complex.ofReal_exp, Complex.re_mul_ofReal, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re, hQτ]
    have hexp : Real.exp (-(β / 2) * quotientCovarianceQuadratic
          (latticeExactOneComplex (B := B) Cubical.originZero)
          (sourcePhysicalCurrentCoClosed Cubical.originZero (signedCurrent J σ) hdiv)) =
        Real.exp (-(β * quotientCovarianceQuadratic (sourceLatticeComplex (B := B))
          (sourcePhysicalCurrentCoClosed Cubical.originZero (signedCurrent J σ) hdiv)) / 2) := by
      congr 1
      ring
    rw [hexp]
    ring
  · simp [physicalGaussianTiltCompletedSquareFactor, hdiv, modeCoeff]

/-! ## The hypotheses on a branch -/

/-- The properties of one terminal state used by the branch construction. -/
structure BranchHyp (β β₁ : ℝ) (q : Link B → ℤ) (z : ℤ → ℝ) (s : CurrentState B) : Prop where
  beta_pos : 0 < β
  rate_pos : 0 < sourceRenormalizedRate β β₁
  separated : IsSeparatedCurrentState q s
  valid : IsValidCurrentState q s
  coeff_pos : ∀ h ∈ s, 0 < lineageCoefficient q z h
  coeff_le : ∀ h ∈ s, lineageCoefficient q z h ≤
    Real.exp (β₁ * integerCurrentNormSq (lineageCurrent q h))

section Branch

variable (β : ℝ) (q : Link B → ℤ) (z : ℤ → ℝ) (s : CurrentState B)

/-- The selected colour of each lineage of the state. -/
noncomputable def branchColor (i : {h : ExpansionLineage B // h ∈ s}) : Fin 8 :=
  stateColor β (stateActivity q z s i) (stateCurrent q s i)

/-- The renormalized amplitude of each lineage of the state. -/
noncomputable def branchAmp (i : {h : ExpansionLineage B // h ∈ s}) : ℝ :=
  branchAmplitude β (stateActivity q z s i) (stateCurrent q s i) (branchColor β q z s i)

/-- The renormalized amplitude as a function of the current: the amplitude of the lineage with
that current, and zero on every other current. -/
noncomputable def branchZ (j : IntegerCurrent B) : ℝ := by
  classical
  exact if h : ∃ i : {h : ExpansionLineage B // h ∈ s}, stateCurrent q s i = j then
    branchAmp β q z s (Classical.choose h) else 0

/-- The closed family of the branch: the physical currents of its co-closed lineages. -/
noncomputable def branchFamily : Finset (ClosedIntegerCurrent B) := by
  classical
  exact (Finset.univ : Finset {i : {h : ExpansionLineage B // h ∈ s} //
      currentDivergence (stateCurrent q s i) = 0}).image
    fun i => ⟨stateCurrent q s i.1, i.2⟩

variable {β q z s} {β₁ : ℝ}

theorem branchAmp_nonneg (H : BranchHyp β β₁ q z s) (i : {h : ExpansionLineage B // h ∈ s}) :
    0 ≤ branchAmp β q z s i :=
  branchAmplitude_nonneg _ _ (H.coeff_pos i.1 i.2).le _ _

theorem branchAmp_le_envelope (H : BranchHyp β β₁ q z s) (i : {h : ExpansionLineage B // h ∈ s}) :
    branchAmp β q z s i ≤ Real.exp (-(sourceRenormalizedRate β β₁ *
      (integerCurrentNormSq (fun e : Link B => stateCurrent q s i e) +
        ((currentSupport (fun e : Link B => stateCurrent q s i e)).card : ℝ)))) := by
  have hrate : β₁ ≤ β / 216 := by
    have := H.rate_pos
    unfold sourceRenormalizedRate at this
    linarith
  refine branchAmplitude_le_envelope β β₁ _ H.beta_pos.le (H.coeff_pos i.1 i.2).le _ ?_ hrate
  have hnorm : integerCurrentNormSq (fun e : Link B => stateCurrent q s i e) =
      integerCurrentNormSq (lineageCurrent q i.1) := sourceBranchModeCurrent_normSq _
  rw [hnorm]
  exact H.coeff_le i.1 i.2

theorem branchAmp_lt_one (H : BranchHyp β β₁ q z s) (i : {h : ExpansionLineage B // h ∈ s}) :
    branchAmp β q z s i < 1 := by
  refine lt_of_le_of_lt (branchAmp_le_envelope H i) ?_
  rw [← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  have hne := stateCurrent_support_nonempty H.valid i
  have hcard : (1 : ℝ) ≤ ((currentSupport (fun e : Link B => stateCurrent q s i e)).card : ℝ) := by
    rw [Currents.ShortComponentPhase.currentSupport_eq_support]
    exact_mod_cast Finset.card_pos.mpr hne
  have hnorm : (0 : ℝ) ≤ integerCurrentNormSq (fun e : Link B => stateCurrent q s i e) := by
    unfold integerCurrentNormSq
    exact Finset.sum_nonneg fun e _ => by positivity
  nlinarith [H.rate_pos]

theorem branchZ_stateCurrent (H : BranchHyp β β₁ q z s) (i : {h : ExpansionLineage B // h ∈ s}) :
    branchZ β q z s (stateCurrent q s i) = branchAmp β q z s i := by
  classical
  have hex : ∃ i' : {h : ExpansionLineage B // h ∈ s}, stateCurrent q s i' = stateCurrent q s i :=
    ⟨i, rfl⟩
  simp only [branchZ, hex, dite_true]
  rw [stateCurrent_injective H.separated H.valid (Classical.choose_spec hex)]

/-- The envelope of the renormalized amplitude, on every current. -/
theorem branchZ_envelope (H : BranchHyp β β₁ q z s) (j : IntegerCurrent B) :
    0 ≤ branchZ β q z s j ∧
      branchZ β q z s j ≤ Real.exp (-(sourceRenormalizedRate β β₁ *
        (integerCurrentNormSq (fun e : Link B => j e) +
          ((currentSupport (fun e : Link B => j e)).card : ℝ)))) := by
  classical
  by_cases hex : ∃ i : {h : ExpansionLineage B // h ∈ s}, stateCurrent q s i = j
  · obtain ⟨i, rfl⟩ := hex
    rw [branchZ_stateCurrent H i]
    exact ⟨branchAmp_nonneg H i, branchAmp_le_envelope H i⟩
  · simp only [branchZ, hex, dite_false]
    exact ⟨le_rfl, (Real.exp_pos _).le⟩

theorem mem_branchFamily_iff (j : ClosedIntegerCurrent B) :
    j ∈ branchFamily q s ↔ ∃ i : {h : ExpansionLineage B // h ∈ s}, stateCurrent q s i = j.1 := by
  classical
  unfold branchFamily
  rw [Finset.mem_image]
  constructor
  · rintro ⟨i, -, rfl⟩
    exact ⟨i.1, rfl⟩
  · rintro ⟨i, hi⟩
    exact ⟨⟨i, hi ▸ j.2⟩, Finset.mem_univ _, Subtype.ext hi⟩

/-- Distinct members of the closed family have disjoint supports. -/
theorem branchFamily_pairwiseDisjoint (H : BranchHyp β β₁ q z s) :
    (↑(branchFamily q s) : Set (ClosedIntegerCurrent B)).PairwiseDisjoint
      (fun j => currentSupport (fun e : Link B => j.1 e)) := by
  intro j hj j' hj' hne
  obtain ⟨i, hi⟩ := (mem_branchFamily_iff j).mp hj
  obtain ⟨i', hi'⟩ := (mem_branchFamily_iff j').mp hj'
  have hii : i ≠ i' := by
    rintro rfl
    exact hne (Subtype.ext (hi.symm.trans hi'))
  change Disjoint (currentSupport (fun e : Link B => j.1 e))
    (currentSupport (fun e : Link B => j'.1 e))
  rw [Currents.ShortComponentPhase.currentSupport_eq_support, Currents.ShortComponentPhase.currentSupport_eq_support,
    ← hi, ← hi']
  exact state_hdisjoint H.separated i i' hii

/-- The image of the closed family in the integer currents is the image of the co-closed
lineages. -/
theorem branchFamily_image (q : Link B → ℤ) (s : CurrentState B)
    [DecidableEq (IntegerCurrent B)]
    [DecidablePred fun i : {h : ExpansionLineage B // h ∈ s} =>
      currentDivergence (stateCurrent q s i) = 0] :
    (branchFamily q s).image (fun j : ClosedIntegerCurrent B => j.1) =
      (Finset.univ.filter fun i : {h : ExpansionLineage B // h ∈ s} =>
        currentDivergence (stateCurrent q s i) = 0).image (stateCurrent q s) := by
  classical
  ext j
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j', hj', rfl⟩
    obtain ⟨i, hi⟩ := (mem_branchFamily_iff j').mp hj'
    exact ⟨i, hi ▸ j'.2, hi⟩
  · rintro ⟨i, hdiv, rfl⟩
    exact ⟨⟨stateCurrent q s i, hdiv⟩, (mem_branchFamily_iff _).mpr ⟨i, rfl⟩, rfl⟩

end Branch

end FroehlichSpencer.FS82.Root.MomentComparisonAssembly

end
