/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.GaugeAverage

/-!
# the gauge-averaged Gaussian field of an integer divergence matrix

`XY/GaugeAverage.lean` realizes the functional `e^{i⟨j, φ⟩} ↦ 1[j co-closed] · e^{−Q(j)/2}` for the
co-closed currents of a rooted tree gauge, in chord coordinates.

Forms of degree at least two have
no tree gauge, so the same functional is realized here without a chart.

Let `D : V → E → ℤ` be an integer matrix (the divergence `(D j)(v) = ∑_e D v e · j e` of an integer
current `j` on `E`) and `S` a positive semidefinite matrix on `E`.

The field is

`φ = ψ + 2π Dᵀ u`,

with `ψ` a centred Gaussian with covariance `S` and `u` independent uniform variables on `[0, 1]`
indexed by `V`.

Because `D` has integer entries, the uniform variables remove every integer
current with a nonzero divergence:

`∫ e^{i⟨j, φ⟩} = 1[D j = 0] · exp(−½ ⟨j, S j⟩)`   (`integral_exp_linkPairingD`).

* `gaugeMeasureD`, `gaugeFieldD`, `ClosedD`, `quadraticD`, `characterValueD`.
* `linkPairing_gaugeFieldD_of_closed`: on a closed current the pairing does not see `u`.
* `integral_cosineProductD`: the integral of `∏ (1 + K cos(⟨J, φ⟩ + θ))` as a sum over sign
  patterns.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.XY.GaugeAverage
open FroehlichSpencer.FS82.Gaussian.RenormalizedFamily.RenormalizedCharacters

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]

/-- The divergence of an integer current for the integer matrix `D`. -/
def divergenceD (D : V → E → ℤ) (j : E → ℤ) (v : V) : ℤ := ∑ e, D v e * j e

/-- A current is closed for `D` when its divergence vanishes. -/
def ClosedD (D : V → E → ℤ) (j : E → ℤ) : Prop := ∀ v, divergenceD D j v = 0

instance (D : V → E → ℤ) (j : E → ℤ) : Decidable (ClosedD D j) := by
  unfold ClosedD
  infer_instance

/-- The quadratic form `⟨j, S j⟩` of an integer current. -/
noncomputable def quadraticD (S : Matrix E E ℝ) (j : E → ℤ) : ℝ :=
  dotProduct (fun e => (j e : ℝ)) (S.mulVec fun e => (j e : ℝ))

/-- The gauge-averaged Gaussian: a centred Gaussian field with covariance `S` and independent
uniform variables indexed by `V`. -/
noncomputable def gaugeMeasureD (V : Type*) [Fintype V] (S : Matrix E E ℝ) :
    Measure (EuclideanSpace ℝ E × (V → ℝ)) :=
  (multivariateGaussian 0 S).prod (Measure.pi fun _ : V => unitLaw)

instance gaugeMeasureD_isProbability (S : Matrix E E ℝ) :
    IsProbabilityMeasure (gaugeMeasureD V S) := by
  unfold gaugeMeasureD
  infer_instance

/-- The field: the Gaussian field plus `2π` times the transpose of `D` applied to the uniform
variables. -/
noncomputable def gaugeFieldD (D : V → E → ℤ) (ω : EuclideanSpace ℝ E × (V → ℝ)) : E → ℝ :=
  fun e => ω.1 e + 2 * Real.pi * ∑ v, ω.2 v * (D v e : ℝ)

omit [Fintype E] [DecidableEq E] in
theorem measurable_gaugeFieldD_apply (D : V → E → ℤ) (e : E) :
    Measurable fun ω : EuclideanSpace ℝ E × (V → ℝ) => gaugeFieldD D ω e := by
  unfold gaugeFieldD
  refine Measurable.add ?_ (Measurable.const_mul ?_ _)
  · fun_prop
  · exact Finset.measurable_sum _ fun v _ =>
      ((measurable_pi_apply v).comp measurable_snd).mul_const _

omit [DecidableEq E] in
theorem measurable_linkPairing_gaugeFieldD (D : V → E → ℤ) (j : E → ℤ) :
    Measurable fun ω : EuclideanSpace ℝ E × (V → ℝ) => linkPairing (gaugeFieldD D ω) j := by
  unfold linkPairing
  exact Finset.measurable_sum _ fun e _ => (measurable_gaugeFieldD_apply D e).mul_const _

omit [DecidableEq E] in
/-- The pairing in the Gaussian and the uniform variables. -/
theorem linkPairing_gaugeFieldD (D : V → E → ℤ) (ω : EuclideanSpace ℝ E × (V → ℝ))
    (j : E → ℤ) :
    linkPairing (gaugeFieldD D ω) j =
      (∑ e, ω.1 e * (j e : ℝ)) +
        2 * Real.pi * ∑ v, ω.2 v * ((divergenceD D j v : ℤ) : ℝ) := by
  unfold linkPairing gaugeFieldD divergenceD
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, Int.cast_sum, Int.cast_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun e _ => by ring


/-- **The character formula.** -/
theorem integral_exp_linkPairingD (D : V → E → ℤ) {S : Matrix E E ℝ} (hS : S.PosSemidef)
    (j : E → ℤ) :
    ∫ ω, Complex.exp (Complex.I * (linkPairing (gaugeFieldD D ω) j : ℝ)) ∂gaugeMeasureD V S =
      if ClosedD D j then Complex.exp (-(quadraticD S j / 2 : ℝ)) else 0 := by
  classical
  let k : EuclideanSpace ℝ E := WithLp.toLp 2 (fun e => (j e : ℝ))
  let g : V → ℝ → ℂ := fun v u =>
    Complex.exp (Complex.I * ((2 * Real.pi * (u * ((divergenceD D j v : ℤ) : ℝ)) : ℝ) : ℂ))
  have hpt : ∀ ω : EuclideanSpace ℝ E × (V → ℝ),
      Complex.exp (Complex.I * (linkPairing (gaugeFieldD D ω) j : ℝ)) =
        Complex.exp ((inner ℝ ω.1 k : ℝ) * Complex.I) * ∏ v, g v (ω.2 v) := by
    intro ω
    rw [linkPairing_gaugeFieldD]
    have h1 : (∑ e, ω.1 e * (j e : ℝ)) = inner ℝ ω.1 k := by
      simp [k, PiLp.inner_apply, mul_comm]
    rw [h1, Finset.mul_sum]
    push_cast
    rw [mul_add, Complex.exp_add, Finset.mul_sum, Complex.exp_sum]
    congr 1
    · ring_nf
    · refine Finset.prod_congr rfl fun v _ => ?_
      simp only [g]
      congr 1
      push_cast
      ring
  simp_rw [hpt]
  unfold gaugeMeasureD
  rw [integral_prod_mul (fun x : EuclideanSpace ℝ E =>
      Complex.exp ((inner ℝ x k : ℝ) * Complex.I)) (fun u : V → ℝ => ∏ v, g v (u v))]
  rw [← charFun_apply, charFun_multivariateGaussian hS, integral_fintype_prod_eq_prod g]
  have hg : ∀ v, ∫ u, g v u ∂unitLaw = if divergenceD D j v = 0 then 1 else 0 := by
    intro v
    simp only [g]
    rw [integral_unitLaw_exp]
  simp_rw [hg]
  have hprod : (∏ v : V, (if divergenceD D j v = 0 then (1 : ℂ) else 0)) =
      if ClosedD D j then 1 else 0 := by
    by_cases hj : ClosedD D j
    · simp only [hj, ↓reduceIte]
      exact Finset.prod_eq_one fun v _ => ite_eq_left (hj v)
    · obtain ⟨v, hd⟩ : ∃ v, divergenceD D j v ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hj hcon
      simp only [hj, ↓reduceIte]
      exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hd])
  rw [hprod]
  by_cases hj : ClosedD D j
  · simp only [hj, ↓reduceIte, mul_one]
    congr 1
    simp only [k, quadraticD, inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
    push_cast
    ring
  · simp only [hj, ↓reduceIte, mul_zero]

/-- The value of the gauge-averaged functional on the character of an integer current. -/
noncomputable def characterValueD (D : V → E → ℤ) (S : Matrix E E ℝ) (j : E → ℤ) : ℂ :=
  if ClosedD D j then Complex.exp (-(quadraticD S j / 2 : ℝ)) else 0

omit [DecidableEq E] in
theorem characterValueD_of_closed (D : V → E → ℤ) (S : Matrix E E ℝ) {j : E → ℤ}
    (hj : ClosedD D j) : characterValueD D S j = Complex.exp (-(quadraticD S j / 2 : ℝ)) := by
  simp [characterValueD, hj]

omit [DecidableEq E] in
theorem characterValueD_of_not_closed (D : V → E → ℤ) (S : Matrix E E ℝ) {j : E → ℤ}
    (hj : ¬ ClosedD D j) : characterValueD D S j = 0 := by
  simp [characterValueD, hj]

theorem integrable_exp_linkPairingD (D : V → E → ℤ) (S : Matrix E E ℝ) (j : E → ℤ) :
    Integrable (fun ω => Complex.exp (Complex.I * (linkPairing (gaugeFieldD D ω) j : ℝ)))
      (gaugeMeasureD V S) := by
  refine Integrable.of_bound ?_ 1 (ae_of_all _ fun ω => ?_)
  · have hm := measurable_linkPairing_gaugeFieldD D j
    exact (Complex.measurable_exp.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp hm))).aestronglyMeasurable
  · rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

/-- **The integral of a product of cosine factors** as a sum over sign patterns. -/
theorem integral_cosineProductD {ι : Type*} [Fintype ι] [DecidableEq ι] (D : V → E → ℤ)
    {S : Matrix E E ℝ} (hS : S.PosSemidef) (K θ : ι → ℝ) (J : ι → E → ℤ) :
    ((∫ ω, ∏ i, (1 + K i * Real.cos (linkPairing (gaugeFieldD D ω) (J i) + θ i))
        ∂gaugeMeasureD V S : ℝ) : ℂ) =
      ∑ σ : ι → Sign, signWeight K θ σ * characterValueD D S (signedSum J σ) := by
  rw [← integral_complex_ofReal]
  have hpt : ∀ ω : EuclideanSpace ℝ E × (V → ℝ),
      ((∏ i, (1 + K i * Real.cos (linkPairing (gaugeFieldD D ω) (J i) + θ i)) : ℝ) : ℂ) =
        ∑ σ : ι → Sign, signWeight K θ σ *
          Complex.exp (Complex.I * (linkPairing (gaugeFieldD D ω) (signedSum J σ) : ℝ)) := by
    intro ω
    rw [cosineProduct_expansion K θ fun i => linkPairing (gaugeFieldD D ω) (J i)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [linkPairing_signedSum]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun σ _ => (integrable_exp_linkPairingD D S _).const_mul _]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_const_mul, integral_exp_linkPairingD D hS]
  rfl

end FroehlichSpencer.FS82.XY.DualD

end
