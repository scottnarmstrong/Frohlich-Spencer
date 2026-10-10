/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Root.RenormalizedJensen

/-!
# the reduced law is an even probability measure

The retained marginal of is a centred Gaussian density, so it is invariant under `y ↦ −y`,
and every renormalized functional is odd and measurable.

For the adaptive-tree chart the
normalized retained marginal is a probability measure; this is read off translate-then-zero-tilt identity at zero activity.

These are the hypotheses of Jensen's
inequality (2.101) on the reduced Gaussian.
-/

open MeasureTheory
open scoped BigOperators
open FroehlichSpencer.FS82.Gaussian.ConditionalGaussian
open FroehlichSpencer.FS82.Gaussian.RenormalizedFamily
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.SourceTreeChart
open FroehlichSpencer.FS82.Currents.AdaptiveTree
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.SourceEnsembleConstructor
open FroehlichSpencer.FS82.Root.RenormalizedInterface

@[expose] public section

namespace FroehlichSpencer.FS82.Root.MomentComparisonAssembly

variable {C P : Type*} [Fintype C] [DecidableEq C] [Fintype P] [DecidableEq P]

local instance (priority := 2000) retainedCoordFintype (B : Finset C) :
    Fintype {c : C // c ∉ B} := Subtype.fintype _

/-! ## Parity of the retained marginal -/

omit [Fintype C] [Fintype P] [DecidableEq P] in
theorem retainedField_neg (B : Finset C) (y : {c : C // c ∉ B} → ℝ) :
    retainedField B (-y) = -retainedField B y := by
  funext c
  by_cases hc : c ∈ B <;> simp [retainedField, hc]

omit [DecidableEq C] [Fintype P] [DecidableEq P] in
theorem curlField_neg (s : P → C → ℝ) (a : C → ℝ) (p : P) :
    SelectedLinkQuadratic.curlField s (-a) p = -SelectedLinkQuadratic.curlField s a p := by
  simp [SelectedLinkQuadratic.curlField, Finset.sum_neg_distrib]

omit [DecidableEq P] in
theorem linkOffset_neg (s : P → C → ℝ) (B : Finset C) (y : {c : C // c ∉ B} → ℝ) (b : C) :
    linkOffset s B (-y) b = -linkOffset s B y b := by
  simp [linkOffset, retainedField_neg, curlField_neg, Finset.sum_neg_distrib]

omit [DecidableEq P] in
theorem reducedWeight_neg (β : ℝ) (s : P → C → ℝ) (B : Finset C)
    (y : {c : C // c ∉ B} → ℝ) :
    reducedWeight β s B (-y) = reducedWeight β s B y := by
  simp [reducedWeight, reducedEnergy, SelectedLinkQuadratic.curlEnergy, retainedField_neg,
    curlField_neg, linkOffset_neg]

/-- A density invariant under a measure-preserving involution gives an invariant measure. -/
theorem map_withDensity_of_invariant {X : Type*} [MeasurableSpace X] (e : X ≃ᵐ X)
    (μ : Measure X) (f : X → ENNReal) (hμ : μ.map e = μ) (hinv : ∀ x, e (e x) = x)
    (hf : ∀ x, f (e x) = f x) :
    (μ.withDensity f).map e = μ.withDensity f := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  rw [← lintegral_indicator (e.measurable hs), ← lintegral_indicator hs]
  calc
    ∫⁻ x, (e ⁻¹' s).indicator f x ∂μ = ∫⁻ x, (e ⁻¹' s).indicator f x ∂(μ.map e) := by rw [hμ]
    _ = ∫⁻ x, (e ⁻¹' s).indicator f (e x) ∂μ := by rw [lintegral_map_equiv]
    _ = ∫⁻ x, s.indicator f x ∂μ := by
      congr 1
      funext x
      by_cases hx : x ∈ s <;> simp [hinv x, hf x, hx]

omit [DecidableEq P] in
/-- The retained marginal is invariant under the sign flip. -/
theorem reducedMeasure_map_neg (β : ℝ) (s : P → C → ℝ) (B : Finset C) :
    Measure.map (fun y : {c : C // c ∉ B} → ℝ => -y) (reducedMeasure β s B) =
      reducedMeasure β s B := by
  have h := map_withDensity_of_invariant (MeasurableEquiv.neg ({c : C // c ∉ B} → ℝ))
    (volume : Measure ({c : C // c ∉ B} → ℝ))
    (fun y => ENNReal.ofReal (reducedWeight β s B y))
    (Measure.map_neg_eq_self (volume : Measure ({c : C // c ∉ B} → ℝ)))
    (fun x => by simp) (fun y => by simp [reducedWeight_neg])
  simpa [reducedMeasure] using h

omit [DecidableEq P] in
theorem normalizedReducedMeasure_map_neg (β : ℝ) (s : P → C → ℝ) (B : Finset C) :
    Measure.map (fun y : {c : C // c ∉ B} → ℝ => -y)
        (normalizedMeasure (reducedMeasure β s B)) =
      normalizedMeasure (reducedMeasure β s B) := by
  unfold normalizedMeasure
  rw [Measure.map_smul _ measurable_neg.aemeasurable, reducedMeasure_map_neg]

/-! ## Parity and measurability of the renormalized functional -/

omit [DecidableEq P] in
theorem selectedMean_neg (s : P → C → ℝ) (B : Finset C) (y : {c : C // c ∉ B} → ℝ) :
    selectedMean s B (-y) = -selectedMean s B y := by
  funext b
  simp [selectedMean, linkOffset_neg, neg_div]

omit [Fintype C] [Fintype P] [DecidableEq P] in
theorem assemble_neg (B : Finset C) (y : {c : C // c ∉ B} → ℝ) (x : {c : C // c ∈ B} → ℝ) :
    assemble B (-y) (-x) = -assemble B y x := by
  funext c
  by_cases hc : c ∈ B <;> simp [assemble, retainedField, selectedField, hc]

omit [DecidableEq P] in
/-- The renormalized functional is odd in the retained coordinates. -/
theorem renormalizedFunctional_neg (s : P → C → ℝ) (B : Finset C) (f : C → ℝ)
    (y : {c : C // c ∉ B} → ℝ) :
    renormalizedFunctional s B f (-y) = -renormalizedFunctional s B f y := by
  simp [renormalizedFunctional, selectedMean_neg, assemble_neg, chartPairing,
    Finset.sum_neg_distrib]

omit [DecidableEq P] in
theorem measurable_renormalizedFunctional (s : P → C → ℝ) (B : Finset C) (f : C → ℝ) :
    Measurable (renormalizedFunctional s B f) := by
  unfold renormalizedFunctional chartPairing assemble retainedField selectedField selectedMean
    linkOffset SelectedLinkQuadratic.curlField retainedField
  refine Finset.measurable_sum _ fun c _ => ?_
  refine measurable_const.mul ?_
  by_cases hc : c ∈ B
  · simp only [Pi.add_apply, hc, dite_true, zero_add]
    refine (Measurable.neg ?_).div_const _
    refine Finset.measurable_sum _ fun p _ => measurable_const.mul ?_
    refine Finset.measurable_sum _ fun e _ => measurable_const.mul ?_
    by_cases he : e ∈ B
    · simp only [he, dite_true]
      exact measurable_const
    · simp only [he, dite_false]
      exact measurable_pi_apply _
  · simp only [Pi.add_apply, hc, dite_false, add_zero]
    exact measurable_pi_apply _

/-! ## The reduced law of the adaptive-tree chart -/

/--
The normalized retained marginal of the adaptive-tree chart is a probability measure.

It is
read off identity at zero activity.
-/
theorem adaptiveTree_reducedLaw_isProbability
    {Λ : Gaussian.SourceBox} {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (hβ : 0 < β)
    (selected : Finset (SourceDualOneCells Λ))
    (hselected : PlaquetteIndependent selected)
    (Bsel : Finset (renormalizedAdaptiveTree selected hselected).Chord)
    (Bᵢ : I → Finset (renormalizedAdaptiveTree selected hselected).Chord)
    (ρ : I → (renormalizedAdaptiveTree selected hselected).Chord → ℝ)
    (hsep : ∀ p, ∀ b₁ ∈ Bsel, ∀ b₂ ∈ Bsel, b₁ ≠ b₂ →
      renormalizedAdaptiveCurlMatrix selected hselected p b₁ = 0 ∨
      renormalizedAdaptiveCurlMatrix selected hselected p b₂ = 0)
    (hn : ∀ b ∈ Bsel,
      0 < linkMass (renormalizedAdaptiveCurlMatrix selected hselected) b)
    (hsub : ∀ i, Bᵢ i ⊆ Bsel)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bᵢ i) (Bᵢ j))
    (hcover : ∀ b ∈ Bsel, ∃ i, b ∈ Bᵢ i)
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0) :
    IsProbabilityMeasure (normalizedMeasure
      (reducedMeasure β (renormalizedAdaptiveCurlMatrix selected hselected) Bsel)) := by
  have h := adaptiveTree_translateThenZeroTilt_familyIdentity β hβ selected hselected
    Bsel Bᵢ ρ (fun _ => (0 : ℝ)) 0 hsep hn hsub hdisj hcover hcross
  have hG : IsProbabilityMeasure (sourceDualQuotientGaussian (B := Λ) β (le_of_lt hβ)) :=
    sourceDualQuotientGaussian_is_probability (B := Λ) (le_of_lt hβ)
  simp only [zero_mul, add_zero, Finset.prod_const_one, renormalizedActivity, integral_const,
    smul_eq_mul, mul_one, measureReal_def, measure_univ, ENNReal.toReal_one] at h
  exact ⟨(ENNReal.toReal_eq_one_iff _).mp h.symm⟩

end FroehlichSpencer.FS82.Root.MomentComparisonAssembly

end
