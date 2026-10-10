/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import FroehlichSpencer.FS82.Currents.ActivityRate
public import FroehlichSpencer.FS82.Currents.SelectedCurrentLinks
public import FroehlichSpencer.FS82.Gaussian.SelectedLinkActivity
public import FroehlichSpencer.FS82.Moment.CurrentDecay
public import FroehlichSpencer.FS82.Currents.SourceLinkColoring
public import Mathlib.Analysis.Real.Pi.Bounds
public import FroehlichSpencer.FS82.Root.MomentComparison
public import FroehlichSpencer.FS82.Root.JensenBudget

public import FroehlichSpencer.FS82.Gaussian.RenormalizedFamily
public import FroehlichSpencer.FS82.Gaussian.SourceTreeChartLaw
public import FroehlichSpencer.FS82.Currents.AdaptiveTree
public import FroehlichSpencer.FS82.Root.ShortAggregateEstimate
public import FroehlichSpencer.FS82.Moment.SourceAssembly

open MeasureTheory
open scoped BigOperators
open FroehlichSpencer.FS82.Gaussian.ConditionalGaussian
open FroehlichSpencer.FS82.Gaussian.RenormalizedFamily
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.SourceTreeChart
open FroehlichSpencer.FS82.Currents.AdaptiveTree
open FroehlichSpencer.FS82.Currents.SelectedLinkSelection
open FroehlichSpencer.FS82.Currents.SelectedCurrentLinks
open FroehlichSpencer.FS82.Currents.SourceLinkColoring
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Moment.SourceEnsembleConstructor
open FroehlichSpencer.FS82.Moment.SourceJensen
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Currents.LongCurrentEstimate
open FroehlichSpencer.FS82.Moment.SourceAssembly
open FroehlichSpencer.FS82.Moment.CurrentDecay
open FroehlichSpencer.FS82.Moment.Comparison
open FroehlichSpencer.FS82.Moment
open Filter

set_option linter.style.haveILetI false

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Root.RenormalizedInterface

variable {C P : Type*} [Fintype C] [DecidableEq C] [Fintype P] [DecidableEq P]

local instance (priority := 2000) selectedCoordFintype (B : Finset C) :
    Fintype {c : C // c ∈ B} := Subtype.fintype _
local instance (priority := 2000) retainedCoordFintype (B : Finset C) :
    Fintype {c : C // c ∉ B} := Subtype.fintype _

omit [DecidableEq C] [DecidableEq P] in
private theorem chartPartitionFunction_eq_toReal_mass (β : ℝ) (s : P → C → ℝ) :
    chartPartitionFunction β s = (chartMeasure β s Set.univ).toReal := by
  have h := chartMeasure_integral_eq β s (fun _ => (1 : ℝ))
  rw [integral_const] at h
  simp only [chartPartitionFunction] at h ⊢
  simpa [Measure.real] using h.symm

omit [DecidableEq P] in
private theorem chartFamilyIntegrable_zeroTilt
    {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (s : P → C → ℝ) (B : Finset C)
    (ρ : I → C → ℝ) (K θ : I → ℝ)
    (hfinite : chartMeasure β s Set.univ ≠ ⊤) :
    Integrable
      (fun z : ({c : C // c ∉ B} → ℝ) × ({c : C // c ∈ B} → ℝ) =>
        chartWeight β s (assemble B z.1 z.2) *
          ∏ i, (1 + K i * Real.cos
            (chartPairing (ρ i) (assemble B z.1 z.2) + θ i)))
      ((Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ))).prod
        (Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ)))) ∧
    Integrable
      (fun z : ({c : C // c ∉ B} → ℝ) × ({c : C // c ∈ B} → ℝ) =>
        chartWeight β s (assemble B z.1 z.2))
      ((Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ))).prod
        (Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ)))) := by
  classical
  let μc := chartMeasure β s
  have hfinite' : μc Set.univ < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    simpa [μc] using hfinite
  haveI : IsFiniteMeasure μc := (isFiniteMeasure_iff μc).2 hfinite'
  have hconst : Integrable (fun _ : C → ℝ => (1 : ℝ)) μc := integrable_const 1
  have hdensityMeas : Measurable (fun x : C → ℝ =>
      ENNReal.ofReal (chartWeight β s x)) := by
    fun_prop [chartWeight,
      FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.curlEnergy,
      FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.curlField]
  have hdensityLt : ∀ᵐ x : C → ℝ ∂(volume : Measure (C → ℝ)),
      ENNReal.ofReal (chartWeight β s x) < ⊤ := by
    filter_upwards [] with x
    exact ENNReal.ofReal_lt_top
  have hweightFull' := (integrable_withDensity_iff hdensityMeas hdensityLt).mp
    (show Integrable (fun x : C → ℝ => (1 : ℝ))
      ((volume : Measure (C → ℝ)).withDensity
        (fun x => ENNReal.ofReal (chartWeight β s x))) from hconst)
  have hweightFull : Integrable (chartWeight β s) (volume : Measure (C → ℝ)) := by
    have heq : (fun x : C → ℝ => (1 : ℝ) *
        (ENNReal.ofReal (chartWeight β s x)).toReal) = chartWeight β s := by
      funext x
      simp [chartWeight, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    simpa only [heq] using hweightFull'
  let split := chartSplitEquiv B
  have hsplit := chartSplitEquiv_measurePreserving B
  have hweightPair : Integrable
      (fun z : ({c : C // c ∉ B} → ℝ) × ({c : C // c ∈ B} → ℝ) =>
        chartWeight β s (assemble B z.1 z.2))
      ((Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ))).prod
        (Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ)))) := by
    have hcomp : Integrable (chartWeight β s ∘ split.symm)
        ((Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ))).prod
          (Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ)))) :=
      (hsplit.symm.integrable_comp (by fun_prop : AEStronglyMeasurable
        (chartWeight β s) (volume : Measure (C → ℝ)))).2 hweightFull
    convert hcomp using 1
    funext z
    rw [Function.comp_apply, chartSplitEquiv_symm_apply]
  let g : (C → ℝ) → ℝ := fun x =>
    ∏ i, (1 + K i * Real.cos (chartPairing (ρ i) x + θ i))
  have hgmeas : Measurable g := by
    dsimp [g, chartPairing]
    fun_prop
  let Cbound : ℝ := ∏ i, (1 + |K i|)
  have hgbound : ∀ x, ‖g x‖ ≤ Cbound := by
    intro x
    dsimp [g, Cbound]
    rw [Finset.abs_prod]
    apply Finset.prod_le_prod₀
    · intro i hi
      positivity
    · intro i hi
      calc
        |1 + K i * Real.cos (chartPairing (ρ i) x + θ i)| ≤
            |(1 : ℝ)| + |K i * Real.cos (chartPairing (ρ i) x + θ i)| := abs_add_le _ _
        _ = 1 + |K i| * |Real.cos (chartPairing (ρ i) x + θ i)| := by simp [abs_mul]
        _ ≤ 1 + |K i| := by
          have hc := Real.abs_cos_le_one (chartPairing (ρ i) x + θ i)
          nlinarith [abs_nonneg (K i)]
  have hgInt : Integrable g μc :=
    Integrable.of_bound hgmeas.aestronglyMeasurable Cbound
      (ae_of_all μc hgbound)
  have hdensityF := (integrable_withDensity_iff hdensityMeas hdensityLt).mp hgInt
  have hweighted : Integrable (fun x : C → ℝ =>
      chartWeight β s x * g x) (volume : Measure (C → ℝ)) := by
    have hEq : (fun x : C → ℝ => g x * (ENNReal.ofReal (chartWeight β s x)).toReal) =
        fun x => chartWeight β s x * g x := by
      funext x
      simp [chartWeight, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
      ring
    simpa only [hEq] using hdensityF
  let pairVol :=
    (Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ))).prod
      (Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ)))
  have hweightPair' : Integrable
      (fun z : ({c : C // c ∉ B} → ℝ) × ({c : C // c ∈ B} → ℝ) =>
        chartWeight β s (assemble B z.1 z.2) * g (assemble B z.1 z.2)) pairVol := by
    have hcomp : Integrable ((fun x : C → ℝ => chartWeight β s x * g x) ∘ split.symm)
        pairVol :=
      (hsplit.symm.integrable_comp (by fun_prop : AEStronglyMeasurable
        (fun x : C → ℝ => chartWeight β s x * g x)
        (volume : Measure (C → ℝ)))).2 hweighted
    convert hcomp using 1
    funext z
    rw [Function.comp_apply, chartSplitEquiv_symm_apply]
  have hboundPair : ∀ᵐ z : ({c : C // c ∉ B} → ℝ) × ({c : C // c ∈ B} → ℝ)
      ∂pairVol, ‖g (assemble B z.1 z.2)‖ ≤ Cbound := by
    filter_upwards [] with z
    exact hgbound (assemble B z.1 z.2)
  have hassemble : Measurable
      (fun z : ({c : C // c ∉ B} → ℝ) × ({c : C // c ∈ B} → ℝ) =>
        assemble B z.1 z.2) := by
    have h := (chartSplitEquiv B).symm.measurable
    convert h using 1
    funext z
    exact (chartSplitEquiv_symm_apply B z.1 z.2).symm
  have hmul := hweightPair.mul_bdd
    ((hgmeas.comp hassemble).aestronglyMeasurable) hboundPair
  refine ⟨?_, hweightPair⟩
  convert hmul using 1
  funext z
  simp [g]


omit [DecidableEq P] in
theorem chartFamilyIdentity_zeroTilt_normalizedMeasures
    {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (s : P → C → ℝ) (B : Finset C)
    (Bᵢ : I → Finset C) (ρ : I → C → ℝ) (K θ : I → ℝ)
    (hβ : 0 < β)
    (hsep : ∀ p, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ →
      s p b₁ = 0 ∨ s p b₂ = 0)
    (hn : ∀ b ∈ B, 0 < linkMass s b)
    (hsub : ∀ i, Bᵢ i ⊆ B)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bᵢ i) (Bᵢ j))
    (hcover : ∀ b ∈ B, ∃ i, b ∈ Bᵢ i)
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0)
    (hfinite : chartMeasure β s Set.univ ≠ ⊤)
    (_hpositive : chartMeasure β s Set.univ ≠ 0) :
    (∫ x : C → ℝ, ∏ i, (1 + K i * Real.cos
      (chartPairing (ρ i) x + θ i)) ∂normalizedMeasure (chartMeasure β s)) =
      ∫ y : {c : C // c ∉ B} → ℝ,
        ∏ i, (1 + renormalizedActivity β (K i) s (Bᵢ i) (ρ i) *
          Real.cos (renormalizedFunctional s B (ρ i) y + θ i))
          ∂normalizedMeasure (reducedMeasure β s B) := by
  classical
  let f : (C → ℝ) → ℝ := fun x =>
    ∏ i, (1 + K i * Real.cos (chartPairing (ρ i) x + θ i))
  let g : ({c : C // c ∉ B} → ℝ) → ℝ := fun y =>
    ∏ i, (1 + renormalizedActivity β (K i) s (Bᵢ i) (ρ i) *
      Real.cos (renormalizedFunctional s B (ρ i) y + θ i))
  have hWeight := (chartFamilyIntegrable_zeroTilt β s B ρ K θ hfinite).2
  have hPart := chartPartitionFunction_eq_reducedMeasure_mass β s B hWeight hβ hsep hn
  have hRedToReal : (∫ _ : {c : C // c ∉ B} → ℝ, (1 : ℝ)
      ∂reducedMeasure β s B) = (reducedMeasure β s B Set.univ).toReal := by
    rw [integral_const]
    rw [Measure.real_def]
    simp
  have hMassRed : chartPartitionFunction β s =
      (reducedMeasure β s B Set.univ).toReal := hPart.trans hRedToReal
  have hMassChart : chartPartitionFunction β s =
      (chartMeasure β s Set.univ).toReal :=
    chartPartitionFunction_eq_toReal_mass β s
  have hChartIdentity := chartFamilyIdentity_zeroTilt β s B Bᵢ ρ K θ
    ((chartFamilyIntegrable_zeroTilt β s B ρ K θ hfinite).1)
    hβ hsep hn hsub hdisj hcover hcross
  have hNormChart :
      (∫ x, f x ∂normalizedMeasure (chartMeasure β s)) =
        (chartPartitionFunction β s)⁻¹ * ∫ x, f x ∂chartMeasure β s := by
    rw [normalizedMeasure, integral_smul_measure, ENNReal.toReal_inv, hMassChart]
    simp [smul_eq_mul, f]
  have hNormRed (g' : ({c : C // c ∉ B} → ℝ) → ℝ) :
      (chartPartitionFunction β s)⁻¹ *
          ∫ y, g' y ∂reducedMeasure β s B =
        ∫ y, g' y ∂normalizedMeasure (reducedMeasure β s B) := by
    rw [normalizedMeasure, integral_smul_measure, ENNReal.toReal_inv, hMassRed]
    simp [smul_eq_mul]
  calc
    _ = (chartPartitionFunction β s)⁻¹ * ∫ x, f x ∂chartMeasure β s := hNormChart
    _ = (chartPartitionFunction β s)⁻¹ * ∫ y, g y ∂reducedMeasure β s B := by
      rw [show (∫ x, f x ∂chartMeasure β s) =
        ∫ x, ∏ i, (1 + K i * Real.cos (chartPairing (ρ i) x + θ i))
          ∂chartMeasure β s by rfl]
      rw [hChartIdentity]
    _ = _ := hNormRed g


/--
The adaptive tree's literal chart density has the finite positive mass
required by normalized zero-tilt family identity.
-/
theorem adaptiveTree_chartMeasure_mass_finite_pos
    {B : Gaussian.SourceBox} (β : ℝ) (hβ : 0 < β)
    (selected : Finset (SourceDualOneCells B))
    (hselected : PlaquetteIndependent selected) :
    0 < chartMeasure β
        (fun p (e : (adaptiveRootedTree B selected hselected).Chord) =>
          sourceCurlCoefficient p e.1) Set.univ ∧
      chartMeasure β
        (fun p (e : (adaptiveRootedTree B selected hselected).Chord) =>
          sourceCurlCoefficient p e.1) Set.univ < ⊤ := by
  let T := adaptiveRootedTree B selected hselected
  let hT := adaptiveRootedTree_endpointMaps B selected hselected
  let s : SourceDualTwoCells B → T.Chord → ℝ := fun p e => sourceCurlCoefficient p e.1
  simpa [T, hT, s, chartMeasure, chartWeight,
    SelectedLinkQuadratic.curlEnergy, SelectedLinkQuadratic.curlField] using
      sourceTreeChartLiteralDensity_mass_finite_pos T hT hβ

/--
The endpoint-compatible adaptive tree used by the branch.
-/
noncomputable abbrev renormalizedAdaptiveTree {Λ : Gaussian.SourceBox}
    (selected : Finset (SourceDualOneCells Λ))
    (hselected : PlaquetteIndependent selected) :=
  adaptiveRootedTree Λ selected hselected

/-- The source curl matrix in adaptive chord coordinates. -/
noncomputable def renormalizedAdaptiveCurlMatrix {Λ : Gaussian.SourceBox}
    (selected : Finset (SourceDualOneCells Λ))
    (hselected : PlaquetteIndependent selected) :
    SourceDualTwoCells Λ → (renormalizedAdaptiveTree selected hselected).Chord → ℝ :=
  fun p e => sourceCurlCoefficient p e.1

/--
The chart map for the adaptive tree.
-/
noncomputable def renormalizedAdaptiveChartMap {Λ : Gaussian.SourceBox}
    (selected : Finset (SourceDualOneCells Λ))
    (hselected : PlaquetteIndependent selected) :
    FroehlichSpencer.FS82.Gaussian.FiniteGaugeQuotient
      (sourceDualComplex Λ) → (renormalizedAdaptiveTree selected hselected).Chord → ℝ :=
  sourceGaussianQuotientChordEquiv (renormalizedAdaptiveTree selected hselected)
    (adaptiveRootedTree_endpointMaps Λ selected hselected)

private theorem adaptiveTree_sourceProduct_integrable
    {Λ : Gaussian.SourceBox} {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (hβ : 0 < β)
    (selected : Finset (SourceDualOneCells Λ))
    (hselected : PlaquetteIndependent selected)
    (ρ : I → (renormalizedAdaptiveTree selected hselected).Chord → ℝ)
    (K θ : I → ℝ) :
    Integrable
      (fun q : FroehlichSpencer.FS82.Gaussian.FiniteGaugeQuotient
        (sourceDualComplex Λ) =>
        ∏ i, (1 + K i * Real.cos
          (chartPairing (ρ i) (renormalizedAdaptiveChartMap selected hselected q) + θ i)))
      (sourceDualQuotientGaussian (B := Λ) β (le_of_lt hβ)) := by
  classical
  let chart := renormalizedAdaptiveChartMap selected hselected
  let T := renormalizedAdaptiveTree selected hselected
  let hT := adaptiveRootedTree_endpointMaps Λ selected hselected
  let f := fun q : FroehlichSpencer.FS82.Gaussian.FiniteGaugeQuotient
      (sourceDualComplex Λ) =>
    ∏ i, (1 + K i * Real.cos (chartPairing (ρ i) (chart q) + θ i))
  have hchartMeas : Measurable chart :=
    sourceGaussianQuotientChordEquiv_measurable T hT
  have hcoord (e : T.Chord) : Measurable (fun q => chart q e) :=
    (measurable_pi_apply e).comp hchartMeas
  have hpair (i : I) :
      Measurable (fun q => chartPairing (ρ i) (chart q)) := by
    unfold chartPairing
    apply Finset.measurable_sum
    intro e he
    exact (hcoord e).const_mul (ρ i e)
  have hf : Measurable f := by
    dsimp [f]
    fun_prop (disch := aesop)
  let Cbound : ℝ := ∏ i, (1 + |K i|)
  have hbound : ∀ q, ‖f q‖ ≤ Cbound := by
    intro q
    dsimp [f, Cbound]
    rw [Finset.abs_prod]
    apply Finset.prod_le_prod₀
    · intro i hi
      positivity
    · intro i hi
      calc
        |1 + K i * Real.cos (chartPairing (ρ i) (chart q) + θ i)| ≤
            |(1 : ℝ)| + |K i * Real.cos (chartPairing (ρ i) (chart q) + θ i)| :=
          abs_add_le _ _
        _ = 1 + |K i| * |Real.cos (chartPairing (ρ i) (chart q) + θ i)| := by
          simp [abs_mul]
        _ ≤ 1 + |K i| := by
          have hc := Real.abs_cos_le_one (chartPairing (ρ i) (chart q) + θ i)
          nlinarith [abs_nonneg (K i)]
  let μ := sourceDualQuotientGaussian (B := Λ) β (le_of_lt hβ)
  letI : IsProbabilityMeasure μ :=
    sourceDualQuotientGaussian_is_probability (B := Λ) (le_of_lt hβ)
  exact Integrable.of_bound hf.aestronglyMeasurable Cbound (ae_of_all μ hbound)

/--
transports a bounded family observable through the adaptive-tree
chart.

Both the chart law and the integral corollary are used below, so the
endpoint compatibility is the adaptive tree's proved `hT`.
-/
theorem adaptiveTree_zeroTilt_integralTransport
    {Λ : Gaussian.SourceBox} {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (hβ : 0 < β)
    (selected : Finset (SourceDualOneCells Λ))
    (hselected : PlaquetteIndependent selected)
    (ρ : I → (renormalizedAdaptiveTree selected hselected).Chord → ℝ)
    (K θ : I → ℝ) :
    (∫ q, ∏ i, (1 + K i * Real.cos
      (chartPairing (ρ i) (renormalizedAdaptiveChartMap selected hselected q) + θ i))
        ∂sourceDualQuotientGaussian (B := Λ) β (le_of_lt hβ)) =
      ∫ x, ∏ i, (1 + K i * Real.cos (chartPairing (ρ i) x + θ i))
        ∂normalizedMeasure (chartMeasure β
          (renormalizedAdaptiveCurlMatrix selected hselected)) := by
  classical
  let T := renormalizedAdaptiveTree selected hselected
  let hT := adaptiveRootedTree_endpointMaps Λ selected hselected
  let s := renormalizedAdaptiveCurlMatrix selected hselected
  let chartEquiv := sourceGaussianQuotientChordEquiv T hT
  let chart := fun q => chartEquiv q
  let μ := sourceDualQuotientGaussian (B := Λ) β (le_of_lt hβ)
  let f := fun q : FroehlichSpencer.FS82.Gaussian.FiniteGaugeQuotient
      (sourceDualComplex Λ) =>
    ∏ i, (1 + K i * Real.cos (chartPairing (ρ i) (chart q) + θ i))
  have hF : Integrable f μ := by
    simpa [f, μ, chart, renormalizedAdaptiveChartMap] using
      adaptiveTree_sourceProduct_integrable β hβ selected hselected ρ K θ
  have hChart := sourceDualQuotientGaussian_treeChart_law T hT hβ
  have hChartNormalized :
      Measure.map chartEquiv μ = normalizedMeasure (chartMeasure β s) := by
    simpa [normalizedMeasure, chartMeasure, chartWeight, s, μ,
      renormalizedAdaptiveCurlMatrix, SelectedLinkQuadratic.curlEnergy,
      SelectedLinkQuadratic.curlField] using hChart
  have hRN := sourceDualQuotientGaussian_treeChart_integral T hT hβ f hF
  have hRNMap :
      (∫ q, f q ∂μ) =
        ∫ x, f (chartEquiv.symm x) ∂Measure.map chartEquiv μ := by
    rw [hChart]
    exact hRN
  have hRNChart :
      (∫ q, f q ∂μ) =
        ∫ x, f (chartEquiv.symm x) ∂normalizedMeasure (chartMeasure β s) := by
    simpa [hChartNormalized] using hRNMap
  have hcomp : ∀ x, f (chartEquiv.symm x) =
      ∏ i, (1 + K i * Real.cos (chartPairing (ρ i) x + θ i)) := by
    intro x
    simp [f, chart, chartEquiv, chartPairing]
  calc
    _ = ∫ x, f (chartEquiv.symm x) ∂normalizedMeasure (chartMeasure β s) := by
      exact hRNChart
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hcomp x

/--
A branch identity with chart law discharged.

The phase is the
original current paired with the Cameron--Martin translate `h`; conditioning
then applies the zero-tilt identity, so neither the common `c_B` nor a local
test-phase term appears.
-/
theorem adaptiveTree_translateThenZeroTilt_familyIdentity
    {Λ : Gaussian.SourceBox} {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (hβ : 0 < β)
    (selected : Finset (SourceDualOneCells Λ))
    (hselected : PlaquetteIndependent selected)
    (Bsel : Finset (renormalizedAdaptiveTree selected hselected).Chord)
    (Bᵢ : I → Finset (renormalizedAdaptiveTree selected hselected).Chord)
    (ρ : I → (renormalizedAdaptiveTree selected hselected).Chord → ℝ)
    (K : I → ℝ)
    (h : (renormalizedAdaptiveTree selected hselected).Chord → ℝ)
    (hsep : ∀ p, ∀ b₁ ∈ Bsel, ∀ b₂ ∈ Bsel, b₁ ≠ b₂ →
      renormalizedAdaptiveCurlMatrix selected hselected p b₁ = 0 ∨
      renormalizedAdaptiveCurlMatrix selected hselected p b₂ = 0)
    (hn : ∀ b ∈ Bsel,
      0 < linkMass (renormalizedAdaptiveCurlMatrix selected hselected) b)
    (hsub : ∀ i, Bᵢ i ⊆ Bsel)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bᵢ i) (Bᵢ j))
    (hcover : ∀ b ∈ Bsel, ∃ i, b ∈ Bᵢ i)
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0) :
    (∫ q, ∏ i, (1 + K i * Real.cos
      (chartPairing (ρ i) (renormalizedAdaptiveChartMap selected hselected q) +
        chartPairing (ρ i) h))
        ∂sourceDualQuotientGaussian (B := Λ) β (le_of_lt hβ)) =
      ∫ y, ∏ i, (1 + renormalizedActivity β (K i)
            (renormalizedAdaptiveCurlMatrix selected hselected) (Bᵢ i) (ρ i) *
          Real.cos (renormalizedFunctional (renormalizedAdaptiveCurlMatrix selected hselected)
            Bsel (ρ i) y + chartPairing (ρ i) h))
            ∂normalizedMeasure
              (reducedMeasure β (renormalizedAdaptiveCurlMatrix selected hselected) Bsel) := by
  let s := renormalizedAdaptiveCurlMatrix selected hselected
  have hMass := adaptiveTree_chartMeasure_mass_finite_pos β hβ selected hselected
  have hfinite : chartMeasure β s Set.univ ≠ ⊤ := ne_of_lt (by
    simpa [s, renormalizedAdaptiveTree, renormalizedAdaptiveCurlMatrix, chartMeasure, chartWeight,
      SelectedLinkQuadratic.curlEnergy,
      SelectedLinkQuadratic.curlField] using hMass.2)
  have hpositive : chartMeasure β s Set.univ ≠ 0 := ne_of_gt (by
    simpa [s, renormalizedAdaptiveTree, renormalizedAdaptiveCurlMatrix, chartMeasure, chartWeight,
      SelectedLinkQuadratic.curlEnergy,
      SelectedLinkQuadratic.curlField] using hMass.1)
  have hTransport := adaptiveTree_zeroTilt_integralTransport β hβ selected hselected
    ρ K (fun i => chartPairing (ρ i) h)
  have hReduced := chartFamilyIdentity_zeroTilt_normalizedMeasures β s Bsel Bᵢ ρ K
    (fun i => chartPairing (ρ i) h) hβ hsep hn hsub hdisj hcover hcross hfinite hpositive
  simpa [s, renormalizedAdaptiveTree, renormalizedAdaptiveCurlMatrix,
    renormalizedAdaptiveChartMap] using hTransport.trans hReduced


variable {B : Cubical.Box 4}

/--
The root packing budget with the renormalized amplitude.

Its budget is
proved by ShortComponentPhase from the actual family of closed currents; `hAmplitude` is the
/attenuation envelope consumed by that proof.
-/
noncomputable def renormalizedFamilyPackingBudget
    {B : Cubical.Box 4} {Ensemble : Type*}
    [Fintype Ensemble] [DecidableEq Ensemble]
    [DecidableEq (IntegerCurrent B)]
    (beta beta₁ : ℝ) (N m : ℕ) (hN : 1 ≤ N)
    (hmLog : Real.log (N + 1 : ℝ) ≤ (m : ℝ))
    (hRate : 8 ≤ sourceRenormalizedRate beta beta₁)
    (hmin : ∀ i : Fin 4, m ≤ B i) (hBmax : ∀ i : Fin 4, B i ≤ N)
    (F : SourceW B → Ensemble → Finset (ClosedIntegerCurrent B))
    (z : SourceW B → Ensemble → IntegerCurrent B → ℝ)
    (hDisjoint : ∀ μ γ,
      (↑(F μ γ) : Set (ClosedIntegerCurrent B)).PairwiseDisjoint
        (fun j => currentSupport (fun e : Link B => j.1 e)))
    (hAmplitude : ∀ μ γ i, 0 ≤ z μ γ i ∧
      z μ γ i ≤ Real.exp (-(sourceRenormalizedRate beta beta₁ *
        (integerCurrentNormSq (fun e : Link B => i e) +
          ((currentSupport (fun e : Link B => i e)).card : ℝ))))) :
    SourcePackingBudget B Ensemble := by
  let hPacking : ∀ μ t γ,
      (∑ i ∈ (F μ γ).image (fun j : ClosedIntegerCurrent B => j.1),
        genericSourceJensenError beta z μ t γ i) ≤
          sourceCoefficient beta₁ N m beta *
            ∑ p, (sourceHodgeField μ (t * beta) p) ^ 2 := by
    intro μ t γ
    exact sourcePacking_logThick_family beta beta₁ N m hN hmLog hRate hmin hBmax
      F z hDisjoint hAmplitude μ t γ
  exact {
    currents := fun _ μ γ => (F μ γ).image (fun j : ClosedIntegerCurrent B => j.1)
    error := fun _ μ t γ i => genericSourceJensenError beta z μ t γ i
    field := fun _ μ t p => sourceHodgeField μ (t * beta) p
    coefficient := sourceCoefficient beta₁ N m beta
    budget := fun _ => hPacking
  }

/--
A branch Jensen package after one-link renormalization (FS82 (2.97)–(2.101)).

`reducedGaussian` is the even probability law of the retained coordinates, `angle` the odd
renormalized phases and `z μ γ (currentIndex i)` the renormalized amplitudes, the same `z` as in
the ShortComponentPhase packing family.

The three bridge fields identify the source data with integrals against
the reduced Gaussian:

* `branchMass_eq_reducedDensity`: the zero-tilt branch mass is the integral of the unshifted
  product `∏ (1 + z cos(angle))` (the normalizer `Z` of (2.101));
* `localMoment_eq_reducedDensity`: the translated local moment is the integral of the shifted
  product `∏ (1 + z cos(angle − θ))` ((2.98) after renormalization);
* `budget_eq_error`: the Jensen budget `Σ γ(z) θ²` is the packing error sum.

The Jensen law itself, the Gibbs tilt of the reduced Gaussian by the unshifted product, is not a
field: `RenormalizedSourceEnsembleJensenData.jensen` derives the whole `SourceEnsembleJensenData`
from these fields.

correction.

The earlier form of this structure carried a `jensen` field with
`jensen.law = reducedGaussian`.
-/
structure RenormalizedSourceEnsembleJensenData
    {B : Cubical.Box 4} {Ensemble Mode I V : Type*}
    [Fintype Ensemble] [DecidableEq Ensemble]
    [Fintype Mode] [DecidableEq Mode] [Fintype I] [DecidableEq I]
    [MeasurableSpace V] [InvolutiveNeg V] [MeasurableNeg V]
    {P : Comparison.PackingBudget Unit
      (SourceW B) Ensemble (IntegerCurrent B) (Gaussian.SourceDualTwoCells B)}
    (D : SourceTestedExpansionInput (B := B) (Ensemble := Ensemble)
      (Mode := Mode) P)
    (z : SourceW B → Ensemble → IntegerCurrent B → ℝ)
    (beta beta₁ : ℝ) where
  reducedGaussian : SourceW B → Ensemble → MeasureTheory.Measure V
  reducedProbability : ∀ μ γ, IsProbabilityMeasure (reducedGaussian μ γ)
  reducedEven : ∀ μ γ,
    Measure.map (fun φ : V => -φ) (reducedGaussian μ γ) = reducedGaussian μ γ
  currentIndex : I → IntegerCurrent B
  currentIndex_ne_zero : ∀ i, currentIndex i ≠ 0
  angle : SourceW B → Ensemble → I → V → ℝ
  angleMeasurable : ∀ μ γ i, Measurable (angle μ γ i)
  angleOdd : ∀ μ γ i φ, angle μ γ i (-φ) = -angle μ γ i φ
  theta : SourceW B → ℝ → Ensemble → I → ℝ
  sourceActivity_envelope : ∀ μ γ i,
    0 ≤ z μ γ i ∧ z μ γ i ≤ Real.exp (-(sourceRenormalizedRate beta beta₁ *
      (integerCurrentNormSq (fun e : Link B => i e) +
        ((currentSupport (fun e : Link B => i e)).card : ℝ))))
  sourceBranchMass : SourceW B → Ensemble → ℝ
  branchMass_eq_normalizer : ∀ μ γ,
    sourceBranchMass μ γ = D.ensembleNormalizer μ γ
  branchMass_eq_reducedDensity : ∀ μ γ,
    sourceBranchMass μ γ =
      ∫ φ, ensembleCosineDensity (fun i => z μ γ (currentIndex i)) (angle μ γ) φ
        ∂reducedGaussian μ γ
  localMoment_eq_reducedDensity : ∀ μ t γ,
    D.localMoment μ t γ =
      ∫ φ, ensembleShiftedCosineDensity (fun i => z μ γ (currentIndex i))
        (theta μ t γ) (angle μ γ) φ ∂reducedGaussian μ γ
  budget_eq_error : ∀ μ t γ,
    SourceJensen.ensembleJensenBudget (fun i => z μ γ (currentIndex i)) (theta μ t γ) =
      ∑ i ∈ P.currents () μ γ, P.error () μ t γ i

namespace RenormalizedSourceEnsembleJensenData

variable {B : Cubical.Box 4} {Ensemble Mode I V : Type*}
  [Fintype Ensemble] [DecidableEq Ensemble]
  [Fintype Mode] [DecidableEq Mode] [Fintype I] [DecidableEq I]
  [MeasurableSpace V] [InvolutiveNeg V] [MeasurableNeg V]
  {P : Comparison.PackingBudget Unit
    (SourceW B) Ensemble (IntegerCurrent B) (Gaussian.SourceDualTwoCells B)}
  {D : SourceTestedExpansionInput (B := B) (Ensemble := Ensemble) (Mode := Mode) P}
  {z : SourceW B → Ensemble → IntegerCurrent B → ℝ} {beta beta₁ : ℝ}

/-- The zero-tilt normalizer is the reduced-density integral. -/
theorem zeroTiltNormalizer
    (J : RenormalizedSourceEnsembleJensenData (I := I) (V := V) D z beta beta₁)
    (μ : SourceW B) (γ : Ensemble) :
    D.ensembleNormalizer μ γ =
      ∫ φ, ensembleCosineDensity (fun i => z μ γ (J.currentIndex i))
        (J.angle μ γ) φ ∂J.reducedGaussian μ γ :=
  (J.branchMass_eq_normalizer μ γ).symm.trans (J.branchMass_eq_reducedDensity μ γ)

/-- The envelope with a positive rate makes every indexed amplitude strictly less than one:
the positivity of the factors `1 + z cos(·)`. -/
theorem amplitude_lt_one
    (J : RenormalizedSourceEnsembleJensenData (I := I) (V := V) D z beta beta₁)
    (hRate : 0 < sourceRenormalizedRate beta beta₁) (μ : SourceW B) (γ : Ensemble) (i : I) :
    z μ γ (J.currentIndex i) < 1 := by
  refine lt_of_le_of_lt (J.sourceActivity_envelope μ γ (J.currentIndex i)).2 ?_
  rw [← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  have hne := J.currentIndex_ne_zero i
  obtain ⟨e, he⟩ : ∃ e, J.currentIndex i e ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (Finsupp.ext hall)
  have hterm : (1 : ℝ) ≤ ((J.currentIndex i e : ℤ) : ℝ) ^ 2 := by
    have h1 : (1 : ℤ) ≤ (J.currentIndex i e) ^ 2 := by
      have := sq_nonneg (J.currentIndex i e)
      have hpos : 0 < (J.currentIndex i e) ^ 2 := by positivity
      omega
    exact_mod_cast h1
  have hnorm : (1 : ℝ) ≤ integerCurrentNormSq (fun e : Link B => J.currentIndex i e) := by
    unfold integerCurrentNormSq
    exact hterm.trans (Finset.single_le_sum
      (f := fun e : Link B => ((J.currentIndex i e : ℤ) : ℝ) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ e))
  have hcard : (0 : ℝ) ≤
      ((currentSupport (fun e : Link B => J.currentIndex i e)).card : ℝ) := by positivity
  nlinarith [mul_pos hRate (lt_of_lt_of_le one_pos hnorm), mul_nonneg hRate.le hcard]

/-- **The Jensen witness from the bridge fields.** The law is the Gibbs tilt of the reduced
Gaussian by the unshifted product density; its normalization is the zero-tilt branch mass, and
the translated local moment is that mass times the tilted integral of the shifted ratio. -/
noncomputable def jensen
    (J : RenormalizedSourceEnsembleJensenData (I := I) (V := V) D z beta beta₁)
    (hRate : 0 < sourceRenormalizedRate beta beta₁) :
    SourceEnsembleJensenData (I := I) (V := V) D := by
  classical
  let zI : SourceW B → Ensemble → I → ℝ := fun μ γ i => z μ γ (J.currentIndex i)
  let f : SourceW B → Ensemble → V → ℝ := fun μ γ =>
    ensembleCosineLogDensity (zI μ γ) (J.angle μ γ)
  have hz0 : ∀ μ γ i, 0 ≤ zI μ γ i := fun μ γ i =>
    (J.sourceActivity_envelope μ γ (J.currentIndex i)).1
  have hz1 : ∀ μ γ i, zI μ γ i < 1 := fun μ γ i => J.amplitude_lt_one hRate μ γ i
  have hfmeas : ∀ μ γ, Measurable (f μ γ) := fun μ γ =>
    measurable_ensembleCosineLogDensity (zI μ γ) (J.angle μ γ) (J.angleMeasurable μ γ)
  have hexpf : ∀ μ γ φ, Real.exp (f μ γ φ) =
      ensembleCosineDensity (zI μ γ) (J.angle μ γ) φ := fun μ γ φ =>
    exp_logDensity_eq_cosineDensity (zI μ γ) (J.angle μ γ) (hz0 μ γ) (hz1 μ γ) φ
  have hIntExp : ∀ μ γ, Integrable (fun φ => Real.exp (f μ γ φ)) (J.reducedGaussian μ γ) := by
    intro μ γ
    have := J.reducedProbability μ γ
    refine Integrable.of_bound ((hfmeas μ γ).exp).aestronglyMeasurable (∏ i, (1 + zI μ γ i))
      (ae_of_all _ fun φ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, hexpf]
    exact (sourceDensity_nonneg_le (zI μ γ) (J.angle μ γ) (hz0 μ γ) (hz1 μ γ) φ).2
  have hprob : ∀ μ γ, IsProbabilityMeasure ((J.reducedGaussian μ γ).tilted (f μ γ)) := by
    intro μ γ
    have := J.reducedProbability μ γ
    exact isProbabilityMeasure_tilted (hIntExp μ γ)
  have hshiftMeas : ∀ μ t γ, Measurable
      (SourceJensen.ensembleLogShift (zI μ γ) (J.theta μ t γ) (J.angle μ γ) 1) := by
    intro μ t γ
    have hangle := J.angleMeasurable μ γ
    unfold SourceJensen.ensembleLogShift SourceJensen.shiftedLogFactor
      SourceJensen.shiftedDenominator
    fun_prop
  exact {
    law := fun μ γ => (J.reducedGaussian μ γ).tilted (f μ γ)
    probability := hprob
    negMeas := measurable_neg
    even := by
      intro μ γ
      have h := tilted_map_invariant (MeasurableEquiv.neg V) (J.reducedGaussian μ γ) (f μ γ)
        (by simpa using J.reducedEven μ γ) (fun x => by simp)
        (fun x => by
          change ensembleCosineLogDensity (zI μ γ) (J.angle μ γ) (-x) =
            ensembleCosineLogDensity (zI μ γ) (J.angle μ γ) x
          unfold ensembleCosineLogDensity
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [J.angleOdd, Real.cos_neg])
      simpa using h
    z := zI
    theta := J.theta
    angle := J.angle
    zNonneg := hz0
    zLtOne := hz1
    angleOdd := J.angleOdd
    logIntegrable := by
      intro μ t γ
      have := hprob μ γ
      refine Integrable.of_bound (hshiftMeas μ t γ).aestronglyMeasurable
        (∑ i, 2 * logEnvelope (zI μ γ i)) (ae_of_all _ fun φ => ?_)
      rw [Real.norm_eq_abs]
      exact ensembleLogShift_abs_bound (zI μ γ) (J.theta μ t γ) (J.angle μ γ)
        (hz0 μ γ) (hz1 μ γ) φ
    expIntegrable := by
      intro μ t γ
      have := hprob μ γ
      refine Integrable.of_bound ((hshiftMeas μ t γ).exp).aestronglyMeasurable
        (∏ i, ((1 + zI μ γ i) / (1 - zI μ γ i))) (ae_of_all _ fun φ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact (ensembleLogShift_exp_bound (zI μ γ) (J.theta μ t γ) (J.angle μ γ)
        (hz0 μ γ) (hz1 μ γ) φ).2
    localMoment_eq_integral := by
      intro μ t γ
      have := J.reducedProbability μ γ
      have hZ : D.ensembleNormalizer μ γ = ∫ φ, Real.exp (f μ γ φ) ∂J.reducedGaussian μ γ := by
        rw [J.zeroTiltNormalizer μ γ]
        exact integral_congr_ae (ae_of_all _ fun φ => (hexpf μ γ φ).symm)
      have hZpos : 0 < ∫ φ, Real.exp (f μ γ φ) ∂J.reducedGaussian μ γ :=
        integral_exp_pos (hIntExp μ γ)
      have hpt : ∀ φ, (Real.exp (f μ γ φ) / ∫ x, Real.exp (f μ γ x) ∂J.reducedGaussian μ γ) •
          Real.exp (SourceJensen.ensembleLogShift (zI μ γ) (J.theta μ t γ)
            (J.angle μ γ) 1 φ) =
          ensembleShiftedCosineDensity (zI μ γ) (J.theta μ t γ) (J.angle μ γ) φ /
            ∫ x, Real.exp (f μ γ x) ∂J.reducedGaussian μ γ := by
        intro φ
        rw [smul_eq_mul, div_mul_eq_mul_div, ← Real.exp_add,
          exp_logDensity_add_shift_eq_shiftedDensity (zI μ γ) (J.theta μ t γ)
            (J.angle μ γ) (hz0 μ γ) (hz1 μ γ) φ]
      rw [integral_tilted]
      simp_rw [hpt]
      rw [integral_div, hZ, mul_div_cancel₀ _ hZpos.ne']
      exact J.localMoment_eq_reducedDensity μ t γ
    budget_eq_error := J.budget_eq_error
  }

end RenormalizedSourceEnsembleJensenData

/-- The outer mixture of branch expansions with their renormalized Jensen packages, as a
residual Jensen aggregate. The mode set, the Jensen index and the retained space may depend on
the branch. The Jensen witness of every branch is derived from the bridge fields. -/
noncomputable def sourceResidualJensenAggregate_of_renormalized {B : Cubical.Box 4}
    {beta beta₁ : ℝ} (hbeta : 0 < beta)
    (hRate : 0 < sourceRenormalizedRate beta beta₁)
    {Ω Ensemble : Type*} {Mode I V : Ω → Type*}
    [Fintype Ensemble] [DecidableEq Ensemble]
    [∀ ω, Fintype (Mode ω)] [∀ ω, DecidableEq (Mode ω)]
    [∀ ω, Fintype (I ω)] [∀ ω, DecidableEq (I ω)]
    [∀ ω, MeasurableSpace (V ω)] [∀ ω, InvolutiveNeg (V ω)] [∀ ω, MeasurableNeg (V ω)]
    {P : Ω → SourcePackingBudget B Ensemble}
    (z : Ω → SourceW B → Ensemble → IntegerCurrent B → ℝ)
    (D : ∀ ω, SourceTestedExpansionInput (B := B) (Ensemble := Ensemble)
      (Mode := Mode ω) (P ω))
    (J : ∀ ω, RenormalizedSourceEnsembleJensenData
      (I := I ω) (V := V ω) (D ω) (z ω) beta beta₁)
    (hBeta : ∀ ω, (D ω).beta = beta) (μ : SourceW B)
    (w : Ω → ℝ) (hw0 : ∀ ω, 0 ≤ w ω) (hw1 : HasSum w 1)
    (hOuter : ∀ t,
      HasSum (fun ω => w ω * (D ω).moment μ t) (sourceDualMoment beta μ t)) :
    SourceResidualJensenAggregate beta P μ where
  outerWeight := w
  outerWeight_nonneg := hw0
  outerWeight_hasSum := hw1
  innerWeight := fun ω => sourceEnsembleWeightOfExpansion (D ω) μ
  innerWeight_nonneg := fun ω =>
    (sourceJointMomentData_of_expansion (D ω) ((J ω).jensen hRate)).ensembleWeightNonneg μ
  innerWeight_sum := fun ω =>
    (sourceJointMomentData_of_expansion (D ω) ((J ω).jensen hRate)).ensembleWeightSum μ
  innerResidual := fun t ω => sourceResidualOfExpansion (D ω) μ t
  inner_aggregate := fun t ω =>
    (sourceJointMomentData_of_expansion (D ω) ((J ω).jensen hRate)).A0_1 μ t
  outer_hasSum := by
    intro t
    set G := Real.exp ((t ^ 2 * beta / 2) *
      Gaussian.quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ)
    have hG : 0 < G := Real.exp_pos _
    have hMom : ∀ ω, (D ω).moment μ t = G * sourceResidualOfExpansion (D ω) μ t := by
      intro ω
      rw [(D ω).hOuterMoment_of_model μ t, hBeta ω]
      rfl
    have h := (hOuter t).mul_left G⁻¹
    rw [sourceDualMoment_eq_gaussian_mul_residual hbeta, ← mul_assoc,
      inv_mul_cancel₀ hG.ne', one_mul] at h
    convert h using 1
    funext ω
    rw [hMom ω]
    field_simp

/-- **FS82 (2.93) on a log-thick box from the renormalized branch data.** The family of each
branch consists of closed currents with pairwise disjoint supports and amplitudes under the
renormalized envelope; ShortComponentPhase supplies the packing estimate. The branch Jensen witnesses are built
inside the proof from the bridge fields of the renormalized packages (the reduced Gaussian, the
zero-tilt mass and the translated local moment), so those identities are consumed here. The lower
exponent is stated with any `c` above SourcePacking's coefficient of the box, so that a box-uniform
coefficient can be inserted. -/
theorem fs82_moment_comparison_logThick_of_renormalizedInputs {B : Cubical.Box 4}
    (beta₁ : ℝ) (N m : ℕ) (hN : 1 ≤ N)
    (hm : Real.log (N + 1 : ℝ) ≤ (m : ℝ))
    (hmin : ∀ i : Fin 4, m ≤ B i) (hBmax : ∀ i : Fin 4, B i ≤ N)
    {beta : ℝ} (hbeta : 0 < beta)
    (hRate : 8 ≤ sourceRenormalizedRate beta beta₁)
    {Ω Ensemble : Type*} {Mode I V : Ω → Type*}
    [Fintype Ensemble] [DecidableEq Ensemble]
    [∀ ω, Fintype (Mode ω)] [∀ ω, DecidableEq (Mode ω)]
    [∀ ω, Fintype (I ω)] [∀ ω, DecidableEq (I ω)]
    [∀ ω, MeasurableSpace (V ω)] [∀ ω, InvolutiveNeg (V ω)] [∀ ω, MeasurableNeg (V ω)]
    [DecidableEq (IntegerCurrent B)]
    (F : Ω → SourceW B → Ensemble → Finset (ClosedIntegerCurrent B))
    (z : Ω → SourceW B → Ensemble → IntegerCurrent B → ℝ)
    (hDisjoint : ∀ ω μ γ,
      (↑(F ω μ γ) : Set (ClosedIntegerCurrent B)).PairwiseDisjoint
        (fun j => currentSupport (fun e : Link B => j.1 e)))
    (hAmplitude : ∀ ω μ γ i, 0 ≤ z ω μ γ i ∧
      z ω μ γ i ≤ Real.exp (-(sourceRenormalizedRate beta beta₁ *
        (integerCurrentNormSq (fun e : Link B => i e) +
          ((currentSupport (fun e : Link B => i e)).card : ℝ)))))
    (D : ∀ ω, SourceTestedExpansionInput (B := B) (Ensemble := Ensemble)
      (Mode := Mode ω)
      (renormalizedFamilyPackingBudget beta beta₁ N m hN hm hRate hmin hBmax
        (F ω) (z ω) (hDisjoint ω) (hAmplitude ω)))
    (J : ∀ ω, RenormalizedSourceEnsembleJensenData
      (I := I ω) (V := V ω) (D ω) (z ω) beta beta₁)
    (hBeta : ∀ ω, (D ω).beta = beta) (μ : SourceW B)
    (w : Ω → ℝ) (hw0 : ∀ ω, 0 ≤ w ω) (hw1 : HasSum w 1)
    (hOuter : ∀ t,
      HasSum (fun ω => w ω * (D ω).moment μ t) (sourceDualMoment beta μ t))
    (c : ℝ) (hc : sourceCoefficient beta₁ N m beta ≤ c) (t : ℝ) :
    Real.exp ((t ^ 2 * (beta * (1 - 2 * beta * c)) / 2) *
        Gaussian.quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ) ≤
      sourceDualMoment beta μ t ∧
    sourceDualMoment beta μ t ≤
      Real.exp ((t ^ 2 * beta / 2) *
        Gaussian.quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ) := by
  have hRatePos : 0 < sourceRenormalizedRate beta beta₁ := by linarith
  let P : Ω → SourcePackingBudget B Ensemble := fun ω =>
    renormalizedFamilyPackingBudget beta beta₁ N m hN hm hRate hmin hBmax
      (F ω) (z ω) (hDisjoint ω) (hAmplitude ω)
  exact fs82_moment_comparison_of_packing hbeta P (fun _ => hc) (fun _ _ _ _ => rfl)
    (sourceResidualJensenAggregate_of_renormalized hbeta hRatePos z D J hBeta μ w hw0 hw1
      hOuter) t

end FroehlichSpencer.FS82.Root.RenormalizedInterface

end
