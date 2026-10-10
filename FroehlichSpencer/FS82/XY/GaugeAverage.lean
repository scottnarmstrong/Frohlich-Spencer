/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Poisson.IntegralDuality
public import FroehlichSpencer.FS82.Poisson.TiltedPoisson
public import FroehlichSpencer.FS82.Gaussian.RenormalizedFamily
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# the gauge-averaged chord Gaussian of a rooted tree

For a rooted tree gauge `T` on a finite graph and a positive definite chord matrix `A`, the dual
Poisson sum runs over the co-closed integer link currents `j` with weight
`exp(−π ⟨k, A⁻¹ k⟩)`, `k` the chord restriction of `j`.

This file realizes the linear functional

`e^{i⟨j, φ⟩} ↦ 1[j co-closed] · exp(−π ⟨k, A⁻¹ k⟩)`

on trigonometric polynomials of a real link field `φ` as integration against a probability
measure: `φ` is a centred Gaussian chord field with covariance `2π A⁻¹`, extended by zero on the
tree, plus `2π` times the coboundary of independent uniform vertex variables.

The uniform
variables remove every current that is not co-closed, FS82 (4.32) and the sentence after it.

* `gaugeMeasure`, `gaugeField`: the probability space and the link field.
* `integral_exp_linkPairing`: the character formula.
* `integral_cosineProduct`: the integral of a finite product `∏ (1 + K cos(⟨J, φ⟩ + θ))` as a
  finite sum over sign patterns.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.GaugeAverage

open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Gaussian.RenormalizedFamily.RenormalizedCharacters

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-! ## Pairings and signed sums -/

/-- The pairing of a real link field with an integer link current. -/
def linkPairing (φ : E → ℝ) (j : E → ℤ) : ℝ := ∑ e, φ e * (j e : ℝ)


/-- The integer value of a sign. -/
def signZ (σ : Sign) : ℤ := if σ.val = 0 then 0 else if σ.val = 1 then 1 else -1

theorem signValue_eq_signZ (σ : Sign) : signValue σ = (signZ σ : ℝ) := by
  unfold signValue signZ
  split_ifs <;> simp

/-- The signed sum of a finite family of integer currents. -/
def signedSum {ι : Type*} [Fintype ι] (J : ι → E → ℤ) (σ : ι → Sign) : E → ℤ :=
  fun e => ∑ i, signZ (σ i) * J i e

omit [DecidableEq E] in
theorem linkPairing_signedSum {ι : Type*} [Fintype ι] (φ : E → ℝ) (J : ι → E → ℤ)
    (σ : ι → Sign) :
    linkPairing φ (signedSum J σ) = ∑ i, signValue (σ i) * linkPairing φ (J i) := by
  simp only [linkPairing, signedSum, signValue_eq_signZ, Int.cast_sum, Int.cast_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun e _ => ?_
  ring

/-- The chord quadratic form `⟨k, A⁻¹ k⟩` of an integer link current. -/
noncomputable def chordQuadratic (T : RootedTreeGauge V E) (A : Matrix T.Chord T.Chord ℝ)
    (j : E → ℤ) : ℝ :=
  dotProduct (fun c : T.Chord => (j c.1 : ℝ))
    (Matrix.mulVec A⁻¹ fun c : T.Chord => (j c.1 : ℝ))

/-! ## The probability space -/

/-- The covariance of the chord field in radians. -/
noncomputable def chordCovariance (T : RootedTreeGauge V E) (A : Matrix T.Chord T.Chord ℝ) :
    Matrix T.Chord T.Chord ℝ := (2 * Real.pi) • A⁻¹

theorem chordCovariance_posSemidef (T : RootedTreeGauge V E) {A : Matrix T.Chord T.Chord ℝ}
    (hA : A.PosDef) : (chordCovariance T A).PosSemidef :=
  hA.inv.posSemidef.smul (by positivity)

/-- The uniform law of one vertex variable. -/
noncomputable def unitLaw : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance unitLaw_isProbability : IsProbabilityMeasure unitLaw :=
  ⟨by simp [unitLaw]⟩

/-- The gauge-averaged chord Gaussian: a centred Gaussian chord field and independent uniform
vertex variables. -/
noncomputable def gaugeMeasure (T : RootedTreeGauge V E) (A : Matrix T.Chord T.Chord ℝ) :
    Measure (EuclideanSpace ℝ T.Chord × (V → ℝ)) :=
  (multivariateGaussian 0 (chordCovariance T A)).prod (Measure.pi fun _ : V => unitLaw)

instance gaugeMeasure_isProbability (T : RootedTreeGauge V E)
    (A : Matrix T.Chord T.Chord ℝ) : IsProbabilityMeasure (gaugeMeasure T A) := by
  unfold gaugeMeasure
  infer_instance

/-- The vertex potential of the uniform variables; the root is grounded. -/
noncomputable def gaugePotential (T : RootedTreeGauge V E) (u : V → ℝ) : V → ℝ :=
  fun v => if v = T.root then 0 else u v

/-- The link field: the chord field extended by zero on the tree, plus `2π` times the
coboundary of the vertex potential. -/
noncomputable def gaugeField (T : RootedTreeGauge V E)
    (ω : EuclideanSpace ℝ T.Chord × (V → ℝ)) : E → ℝ :=
  fun e => T.extendChord (fun c => ω.1 c) e +
    2 * Real.pi * T.coboundary (gaugePotential T ω.2) e

omit [Fintype V] [Fintype E] in
theorem measurable_gaugePotential_apply (T : RootedTreeGauge V E) (v : V) :
    Measurable fun u : V → ℝ => gaugePotential T u v := by
  by_cases hv : v = T.root
  · simp only [gaugePotential, hv, ↓reduceIte]
    exact measurable_const
  · simp only [gaugePotential, hv, ↓reduceIte]
    exact measurable_pi_apply v

omit [Fintype E] in
theorem measurable_gaugeField_apply (T : RootedTreeGauge V E) (e : E) :
    Measurable fun ω : EuclideanSpace ℝ T.Chord × (V → ℝ) => gaugeField T ω e := by
  classical
  have hpot : ∀ v, Measurable fun ω : EuclideanSpace ℝ T.Chord × (V → ℝ) =>
      gaugePotential T ω.2 v := fun v =>
    (measurable_gaugePotential_apply T v).comp measurable_snd
  have hcob : Measurable fun ω : EuclideanSpace ℝ T.Chord × (V → ℝ) =>
      2 * Real.pi * T.coboundary (gaugePotential T ω.2) e := by
    unfold RootedTreeGauge.coboundary
    exact ((hpot _).sub (hpot _)).const_mul _
  unfold gaugeField RootedTreeGauge.extendChord
  by_cases he : e ∈ Set.range T.treeEdge
  · simp only [he, dite_true]
    exact measurable_const.add hcob
  · simp only [he, dite_false]
    refine Measurable.add ?_ hcob
    fun_prop

theorem measurable_linkPairing_gaugeField (T : RootedTreeGauge V E) (j : E → ℤ) :
    Measurable fun ω : EuclideanSpace ℝ T.Chord × (V → ℝ) =>
      linkPairing (gaugeField T ω) j := by
  unfold linkPairing
  exact Finset.measurable_sum _ fun e _ => (measurable_gaugeField_apply T e).mul_const _

/-! ## The pairing in chord and vertex variables -/

theorem sum_extendChord_mul (T : RootedTreeGauge V E) (x : T.Chord → ℝ) (a : E → ℝ) :
    ∑ e, T.extendChord x e * a e = ∑ c : T.Chord, x c * a c.1 := by
  classical
  have hf : ∀ c : T.Chord, x c * a c.1 = T.extendChord x c.1 * a c.1 := by
    intro c
    simp [RootedTreeGauge.extendChord, c.2]
  simp_rw [hf]
  rw [← Finset.sum_subtype (Finset.univ.filter fun e => e ∉ Set.range T.treeEdge) (by simp)
    (fun e => T.extendChord x e * a e)]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e _ he
  have he' : e ∈ Set.range T.treeEdge := by simpa using he
  simp [RootedTreeGauge.extendChord, he']

theorem linkPairing_gaugeField (T : RootedTreeGauge V E)
    (ω : EuclideanSpace ℝ T.Chord × (V → ℝ)) (j : E → ℤ) :
    linkPairing (gaugeField T ω) j =
      (∑ c : T.Chord, ω.1 c * (j c.1 : ℝ)) +
        2 * Real.pi * ∑ v, gaugePotential T ω.2 v *
          ((RootedTreeGauge.divergence T j v : ℤ) : ℝ) := by
  unfold linkPairing gaugeField
  simp only [add_mul, Finset.sum_add_distrib]
  rw [sum_extendChord_mul T (fun c => ω.1 c) (fun e => (j e : ℝ))]
  congr 1
  have h := RootedTreeGauge.pairing_coboundary_eq_sum_divergence T (fun e => (j e : ℝ))
    (gaugePotential T ω.2)
  have hdiv : ∀ v, RootedTreeGauge.divergence T (fun e => (j e : ℝ)) v =
      ((RootedTreeGauge.divergence T j v : ℤ) : ℝ) := by
    intro v
    simp [RootedTreeGauge.divergence]
  simp_rw [hdiv] at h
  rw [← h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => by ring

/-! ## The character formula -/

theorem integral_unitLaw_exp (n : ℤ) :
    ∫ u, Complex.exp (Complex.I * ((2 * Real.pi * (u * (n : ℝ)) : ℝ) : ℂ)) ∂unitLaw =
      if n = 0 then 1 else 0 := by
  unfold unitLaw
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ↓reduceIte]
    have hc : (2 * Real.pi * n * Complex.I : ℂ) ≠ 0 := by
      have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hn', hpi]
    have hint := integral_exp_mul_complex (a := 0) (b := 1) hc
    have hfun : (fun u : ℝ => Complex.exp (Complex.I * ((2 * Real.pi * (u * (n : ℝ)) : ℝ) : ℂ))) =
        fun u : ℝ => Complex.exp (2 * Real.pi * n * Complex.I * u) := by
      funext u
      congr 1
      push_cast
      ring
    rw [hfun, hint]
    have hexp : Complex.exp (2 * Real.pi * n * Complex.I * ((1 : ℝ) : ℂ)) = 1 := by
      have h := Complex.exp_int_mul_two_pi_mul_I n
      rw [← h]
      congr 1
      push_cast
      ring
    rw [hexp]
    simp

theorem integral_exp_linkPairing (T : RootedTreeGauge V E) {A : Matrix T.Chord T.Chord ℝ}
    (hA : A.PosDef) (j : E → ℤ) [Decidable (RootedTreeGauge.CoClosed T j)] :
    ∫ ω, Complex.exp (Complex.I * (linkPairing (gaugeField T ω) j : ℝ)) ∂gaugeMeasure T A =
      if RootedTreeGauge.CoClosed T j then
        Complex.exp (-(Real.pi * chordQuadratic T A j : ℝ)) else 0 := by
  classical
  let k : EuclideanSpace ℝ T.Chord := WithLp.toLp 2 (fun c => (j c.1 : ℝ))
  let g : V → ℝ → ℂ := fun v u => if v = T.root then (1 : ℂ) else
    Complex.exp (Complex.I *
      ((2 * Real.pi * (u * ((RootedTreeGauge.divergence T j v : ℤ) : ℝ)) : ℝ) : ℂ))
  have hpt : ∀ ω : EuclideanSpace ℝ T.Chord × (V → ℝ),
      Complex.exp (Complex.I * (linkPairing (gaugeField T ω) j : ℝ)) =
        Complex.exp ((inner ℝ ω.1 k : ℝ) * Complex.I) * ∏ v, g v (ω.2 v) := by
    intro ω
    rw [linkPairing_gaugeField]
    have h1 : (∑ c : T.Chord, ω.1 c * (j c.1 : ℝ)) = inner ℝ ω.1 k := by
      simp [k, PiLp.inner_apply, mul_comm]
    rw [h1, Finset.mul_sum]
    push_cast
    rw [mul_add, Complex.exp_add, Finset.mul_sum, Complex.exp_sum]
    congr 1
    · ring_nf
    · refine Finset.prod_congr rfl fun v _ => ?_
      by_cases hv : v = T.root
      · simp [g, gaugePotential, hv]
      · simp only [g, gaugePotential, hv, ↓reduceIte]
        congr 1
        push_cast
        ring
  simp_rw [hpt]
  unfold gaugeMeasure
  rw [integral_prod_mul (fun x : EuclideanSpace ℝ T.Chord =>
      Complex.exp ((inner ℝ x k : ℝ) * Complex.I)) (fun u : V → ℝ => ∏ v, g v (u v))]
  rw [← charFun_apply, charFun_multivariateGaussian (chordCovariance_posSemidef T hA),
    integral_fintype_prod_eq_prod g]
  have hg : ∀ v, ∫ u, g v u ∂unitLaw =
      if (v ≠ T.root → RootedTreeGauge.divergence T j v = 0) then 1 else 0 := by
    intro v
    by_cases hv : v = T.root
    · simp [g, hv]
    · simp only [g, hv, ↓reduceIte]
      rw [integral_unitLaw_exp]
      simp [hv]
  simp_rw [hg]
  have hprod : (∏ v : V, (if (v ≠ T.root → RootedTreeGauge.divergence T j v = 0) then (1 : ℂ)
      else 0)) = if RootedTreeGauge.CoClosed T j then 1 else 0 := by
    by_cases hj : RootedTreeGauge.CoClosed T j
    · have h1 : ∀ v, v ≠ T.root → RootedTreeGauge.divergence T j v = 0 := fun v hv => hj v hv
      simp only [hj, ↓reduceIte]
      exact Finset.prod_eq_one fun v _ => ite_eq_left (h1 v)
    · obtain ⟨v, hv, hd⟩ : ∃ v, v ≠ T.root ∧ RootedTreeGauge.divergence T j v ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hj fun v hv => hcon v hv
      simp only [hj, ↓reduceIte]
      exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv, hd])
  rw [hprod]
  by_cases hj : RootedTreeGauge.CoClosed T j
  · simp only [hj, ↓reduceIte, mul_one]
    congr 1
    simp only [k, chordCovariance, chordQuadratic, inner_zero_right, Complex.ofReal_zero,
      zero_mul, zero_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    push_cast
    ring
  · simp only [hj, ↓reduceIte, mul_zero]

/-- The value of the gauge-averaged functional on the character of an integer current. -/
noncomputable def characterValue (T : RootedTreeGauge V E) (A : Matrix T.Chord T.Chord ℝ)
    (j : E → ℤ) : ℂ :=
  open Classical in
  if RootedTreeGauge.CoClosed T j then
    Complex.exp (-(Real.pi * chordQuadratic T A j : ℝ)) else 0

theorem characterValue_of_coClosed (T : RootedTreeGauge V E) (A : Matrix T.Chord T.Chord ℝ)
    {j : E → ℤ} (hj : RootedTreeGauge.CoClosed T j) :
    characterValue T A j = Complex.exp (-(Real.pi * chordQuadratic T A j : ℝ)) := by
  simp [characterValue, hj]

theorem characterValue_of_not_coClosed (T : RootedTreeGauge V E)
    (A : Matrix T.Chord T.Chord ℝ) {j : E → ℤ} (hj : ¬ RootedTreeGauge.CoClosed T j) :
    characterValue T A j = 0 := by
  simp [characterValue, hj]

theorem integral_exp_linkPairing_eq_characterValue (T : RootedTreeGauge V E)
    {A : Matrix T.Chord T.Chord ℝ} (hA : A.PosDef) (j : E → ℤ) :
    ∫ ω, Complex.exp (Complex.I * (linkPairing (gaugeField T ω) j : ℝ)) ∂gaugeMeasure T A =
      characterValue T A j := by
  classical
  rw [integral_exp_linkPairing T hA j]
  rfl

theorem integrable_exp_linkPairing (T : RootedTreeGauge V E) (A : Matrix T.Chord T.Chord ℝ)
    (j : E → ℤ) :
    Integrable (fun ω => Complex.exp (Complex.I * (linkPairing (gaugeField T ω) j : ℝ)))
      (gaugeMeasure T A) := by
  refine Integrable.of_bound ?_ 1 (ae_of_all _ fun ω => ?_)
  · have hm := measurable_linkPairing_gaugeField T j
    exact (Complex.measurable_exp.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp hm))).aestronglyMeasurable
  · rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

/-! ## Cosine products -/

/-- The coefficient of a sign pattern in a product of cosine factors with phases. -/
noncomputable def signWeight {ι : Type*} [Fintype ι] (K θ : ι → ℝ) (σ : ι → Sign) : ℂ :=
  ∏ i, signCoeff (K i) (σ i) * Complex.exp (Complex.I * ((signValue (σ i) * θ i : ℝ) : ℂ))

/-- The sign-pattern expansion of a finite product of cosine factors with phases. -/
theorem cosineProduct_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] (K θ p : ι → ℝ) :
    ((∏ i, (1 + K i * Real.cos (p i + θ i)) : ℝ) : ℂ) =
      ∑ σ : ι → Sign, signWeight K θ σ *
        Complex.exp (Complex.I * ((∑ i, signValue (σ i) * p i : ℝ) : ℂ)) := by
  have h := familyCosineExpansion K (fun i => p i + θ i)
  simp only [Complex.ofReal_prod, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul]
  refine h.trans (Finset.sum_congr rfl fun σ _ => ?_)
  unfold signWeight charTerm
  rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem integral_cosineProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : RootedTreeGauge V E) {A : Matrix T.Chord T.Chord ℝ} (hA : A.PosDef)
    (K θ : ι → ℝ) (J : ι → E → ℤ) :
    ((∫ ω, ∏ i, (1 + K i * Real.cos (linkPairing (gaugeField T ω) (J i) + θ i))
        ∂gaugeMeasure T A : ℝ) : ℂ) =
      ∑ σ : ι → Sign, signWeight K θ σ * characterValue T A (signedSum J σ) := by
  rw [← integral_complex_ofReal]
  have hpt : ∀ ω : EuclideanSpace ℝ T.Chord × (V → ℝ),
      ((∏ i, (1 + K i * Real.cos (linkPairing (gaugeField T ω) (J i) + θ i)) : ℝ) : ℂ) =
        ∑ σ : ι → Sign, signWeight K θ σ *
          Complex.exp (Complex.I * (linkPairing (gaugeField T ω) (signedSum J σ) : ℝ)) := by
    intro ω
    rw [cosineProduct_expansion K θ fun i => linkPairing (gaugeField T ω) (J i)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [linkPairing_signedSum]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun σ _ => (integrable_exp_linkPairing T A _).const_mul _]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_const_mul, integral_exp_linkPairing_eq_characterValue T hA]

end FroehlichSpencer.FS82.XY.GaugeAverage

end
