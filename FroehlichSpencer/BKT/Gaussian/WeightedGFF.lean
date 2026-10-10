/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.GFFWellDefined
public import FroehlichSpencer.BKT.Surface.SubGaussian
public import FroehlichSpencer.BKT.Bridge.GFFMeasure
public import FroehlichSpencer.BKT.Gaussian.ExponentialMoment
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# The weighted GFF functional of KP (1.8)

KP §1.5, p. 4 (Kharash–Peled, first version).

For real,
even, normalized trigonometric polynomials `λ_j`, KP define the (not necessarily positive)
measure
`dμ_{β,Λ,λ,v} = Z⁻¹ ∏_j λ_j(φ_j) dμ^GFF_{β,Λ,v}`, with `Z = ∫ ∏_j λ_j(φ_j) dμ^GFF_{β,Λ,v}`,
and write `𝔼_{β,Λ,λ,v}` for integration against it.

Everything here is built on the GFF law `gffLaw` (KP (1.3)):

* `weightedGFFNormalizer` is `Z`;
* `weightedGFFExpectation` is the functional `F ↦ Z⁻¹ ∫ F ∏_j λ_j(φ_j) dμ^GFF`;
* `weightedGFFSignedMeasure` is the signed measure itself, as a `SignedMeasure`.

The characterization theorems state KP's formulas.

`weightedGFFExpectation_exp` identifies the
functional at `F = e^⟨φ,f⟩` with the ratio in the statement of KP Theorem 1.5.

For
`(Γ, η, θ)`-sub-Gaussian weights (the `IsSubGaussian`, Definition 1.4), the product
`∏_j λ_j(φ_j)` is bounded and continuous, so the functional is defined by absolutely convergent
integrals for every integrable `F`, in particular for `e^⟨φ,f⟩` with `∑ f = 0` (KP (1.4)).

With all
weights equal to `1`, `Z = 1` and the functional is the GFF expectation (KP p. 5).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT

open MeasureTheory

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]

/-- KP (1.8): the normalizer `Z_{β,Λ,λ,v} = ∫ ∏_j λ_j(φ_j) dμ^GFF_{β,Λ,v}`. -/
def weightedGFFNormalizer (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (β : ℝ)
    (hβ : 0 < β) (v : V) (lam : V → ℝ → ℝ) : ℝ :=
  ∫ φ, ∏ j, lam j (φ j) ∂gffLaw G hG β hβ v

/-- KP (1.8): the weighted functional `𝔼_{β,Λ,λ,v}[F] = Z⁻¹ ∫ F ∏_j λ_j(φ_j) dμ^GFF`. -/
def weightedGFFExpectation (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (β : ℝ)
    (hβ : 0 < β) (v : V) (lam : V → ℝ → ℝ) (F : (V → ℝ) → ℝ) : ℝ :=
  (∫ φ, F φ * ∏ j, lam j (φ j) ∂gffLaw G hG β hβ v) / weightedGFFNormalizer G hG β hβ v lam

/-- KP (1.8): the signed measure `Z⁻¹ ∏_j λ_j(φ_j) dμ^GFF_{β,Λ,v}`. -/
def weightedGFFSignedMeasure (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (β : ℝ)
    (hβ : 0 < β) (v : V) (lam : V → ℝ → ℝ) : SignedMeasure (V → ℝ) :=
  (weightedGFFNormalizer G hG β hβ v lam)⁻¹ •
    (gffLaw G hG β hβ v).withDensityᵥ fun φ => ∏ j, lam j (φ j)

section Characterization

variable (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V)
  (lam : V → ℝ → ℝ)

/-- KP (1.8), the normalizer: its defining formula. -/
theorem weightedGFFNormalizer_eq :
    weightedGFFNormalizer G hG β hβ v lam = ∫ φ, ∏ j, lam j (φ j) ∂gffLaw G hG β hβ v :=
  rfl

/-- KP (1.8), the functional: its defining formula. -/
theorem weightedGFFExpectation_eq (F : (V → ℝ) → ℝ) :
    weightedGFFExpectation G hG β hβ v lam F =
      (∫ φ, F φ * ∏ j, lam j (φ j) ∂gffLaw G hG β hβ v) /
        ∫ φ, ∏ j, lam j (φ j) ∂gffLaw G hG β hβ v :=
  rfl

/--
The functional at `F = e^⟨φ,f⟩` is exactly the ratio in the statement of KP
Theorem 1.5 (`weightedGFF_expMoment_lower_bound`).
-/
theorem weightedGFFExpectation_exp (f : V → ℝ) :
    weightedGFFExpectation G hG β hβ v lam (fun φ => Real.exp (∑ j, φ j * f j)) =
      (∫ φ, Real.exp (∑ j, φ j * f j) * ∏ j, lam j (φ j) ∂gffLaw G hG β hβ v) /
        ∫ φ, ∏ j, lam j (φ j) ∂gffLaw G hG β hβ v :=
  rfl

/-- The signed measure of a measurable set is `Z⁻¹ ∫_S ∏_j λ_j(φ_j) dμ^GFF`. -/
theorem weightedGFFSignedMeasure_apply
    (hint : Integrable (fun φ => ∏ j, lam j (φ j)) (gffLaw G hG β hβ v)) {S : Set (V → ℝ)}
    (hS : MeasurableSet S) :
    weightedGFFSignedMeasure G hG β hβ v lam S =
      (weightedGFFNormalizer G hG β hβ v lam)⁻¹ *
        ∫ φ in S, ∏ j, lam j (φ j) ∂gffLaw G hG β hβ v := by
  rw [weightedGFFSignedMeasure, smul_apply, withDensityᵥ_apply hint hS,
    smul_eq_mul]

/-- When `Z ≠ 0`, the signed measure has total mass one. -/
theorem weightedGFFSignedMeasure_univ
    (hint : Integrable (fun φ => ∏ j, lam j (φ j)) (gffLaw G hG β hβ v))
    (hZ : weightedGFFNormalizer G hG β hβ v lam ≠ 0) :
    weightedGFFSignedMeasure G hG β hβ v lam Set.univ = 1 := by
  rw [weightedGFFSignedMeasure_apply G hG β hβ v lam hint MeasurableSet.univ,
    Measure.restrict_univ]
  exact inv_mul_cancel₀ hZ

/-- KP p. 5: with every weight equal to `1`, the normalizer is `1`. -/
theorem weightedGFFNormalizer_one :
    weightedGFFNormalizer G hG β hβ v (fun _ _ => 1) = 1 := by
  have := isProbabilityMeasure_gffLaw G hG β hβ v
  simp [weightedGFFNormalizer]

/-- KP p. 5: `μ_{β,Λ,1,v} = μ^GFF_{β,Λ,v}`; the functional with unit weights is the GFF
expectation. -/
theorem weightedGFFExpectation_one (F : (V → ℝ) → ℝ) :
    weightedGFFExpectation G hG β hβ v (fun _ _ => 1) F = ∫ φ, F φ ∂gffLaw G hG β hβ v := by
  rw [weightedGFFExpectation, weightedGFFNormalizer_one]
  simp

end Characterization

/-! ### Sub-Gaussian weights -/

/-- A sub-Gaussian weight is a trigonometric polynomial, hence continuous. -/
theorem IsSubGaussian.continuous {Γ η θ β : ℝ} {lam : ℝ → ℝ}
    (h : IsSubGaussian Γ η θ β lam) : Continuous lam := by
  obtain ⟨N, -, lamHat, -, hform, -⟩ := h
  rw [show lam = fun φ => 1 + 2 * ∑ q ∈ Finset.Icc 1 N, lamHat q * Real.cos (q * φ) from
    funext hform]
  fun_prop

/-- A sub-Gaussian weight is bounded by `1 + 2 ∑_q |λ̂(q)|`. -/
theorem IsSubGaussian.exists_abs_le {Γ η θ β : ℝ} {lam : ℝ → ℝ}
    (h : IsSubGaussian Γ η θ β lam) : ∃ C : ℝ, ∀ φ, |lam φ| ≤ C := by
  obtain ⟨N, -, lamHat, -, hform, -⟩ := h
  refine ⟨1 + 2 * ∑ q ∈ Finset.Icc 1 N, |lamHat q|, fun φ => ?_⟩
  rw [hform]
  calc |1 + 2 * ∑ q ∈ Finset.Icc 1 N, lamHat q * Real.cos (q * φ)|
      ≤ |(1 : ℝ)| + |2 * ∑ q ∈ Finset.Icc 1 N, lamHat q * Real.cos (q * φ)| := abs_add_le _ _
    _ ≤ 1 + 2 * ∑ q ∈ Finset.Icc 1 N, |lamHat q| := by
      rw [abs_one, abs_mul, abs_two]
      gcongr
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

section SubGaussian

variable {Γ η θ β' : ℝ} {lam : V → ℝ → ℝ}

/-- The product of sub-Gaussian weights is continuous on field space. -/
theorem continuous_prod_of_isSubGaussian (hlam : ∀ j, IsSubGaussian Γ η θ β' (lam j)) :
    Continuous fun φ : V → ℝ => ∏ j, lam j (φ j) :=
  continuous_finsetProd _ fun j _ => (hlam j).continuous.comp (continuous_apply j)

/-- The product of sub-Gaussian weights is uniformly bounded on field space. -/
theorem exists_abs_prod_le_of_isSubGaussian (hlam : ∀ j, IsSubGaussian Γ η θ β' (lam j)) :
    ∃ C : ℝ, ∀ φ : V → ℝ, |∏ j, lam j (φ j)| ≤ C := by
  choose C hC using fun j => (hlam j).exists_abs_le
  refine ⟨∏ j, C j, fun φ => ?_⟩
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ => hC j (φ j)

variable (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V)

/-- For sub-Gaussian weights, `∏_j λ_j(φ_j)` is integrable for the GFF, so `Z` is a genuine
integral. -/
theorem integrable_prod_of_isSubGaussian (hlam : ∀ j, IsSubGaussian Γ η θ β' (lam j)) :
    Integrable (fun φ => ∏ j, lam j (φ j)) (gffLaw G hG β hβ v) := by
  have := isProbabilityMeasure_gffLaw G hG β hβ v
  obtain ⟨C, hC⟩ := exists_abs_prod_le_of_isSubGaussian hlam
  exact Integrable.of_bound (continuous_prod_of_isSubGaussian hlam).aestronglyMeasurable C
    (ae_of_all _ fun φ => (Real.norm_eq_abs _).le.trans (hC φ))

/-- For sub-Gaussian weights and an integrable observable `F`, the numerator of the weighted
functional is an absolutely convergent integral. -/
theorem integrable_mul_prod_of_isSubGaussian (hlam : ∀ j, IsSubGaussian Γ η θ β' (lam j))
    {F : (V → ℝ) → ℝ} (hF : Integrable F (gffLaw G hG β hβ v)) :
    Integrable (fun φ => F φ * ∏ j, lam j (φ j)) (gffLaw G hG β hβ v) := by
  obtain ⟨C, hC⟩ := exists_abs_prod_le_of_isSubGaussian hlam
  exact hF.mul_bdd (continuous_prod_of_isSubGaussian hlam).aestronglyMeasurable
    (ae_of_all _ fun φ => (Real.norm_eq_abs _).le.trans (hC φ))

/--
KP (1.4) under the GFF law: `e^⟨φ,f⟩` is integrable for every zero-sum `f`.
-/
theorem integrable_exp_pairing_gffLaw (f : V → ℝ) (hf : ∑ j, f j = 0) :
    Integrable (fun φ : V → ℝ => Real.exp (∑ j, φ j * f j)) (gffLaw G hG β hβ v) := by
  classical
  rw [gffLaw_eq_gffMeasure G hG β hβ v]
  exact (gff_exponential_moment G hG β hβ f hf v).1

/-- For sub-Gaussian weights and zero-sum `f`, the numerator `∫ e^⟨φ,f⟩ ∏_j λ_j(φ_j) dμ^GFF`
of KP (1.10) is an absolutely convergent integral. -/
theorem integrable_exp_mul_prod_of_isSubGaussian (hlam : ∀ j, IsSubGaussian Γ η θ β' (lam j))
    (f : V → ℝ) (hf : ∑ j, f j = 0) :
    Integrable (fun φ => Real.exp (∑ j, φ j * f j) * ∏ j, lam j (φ j)) (gffLaw G hG β hβ v) :=
  integrable_mul_prod_of_isSubGaussian G hG β hβ v hlam
    (integrable_exp_pairing_gffLaw G hG β hβ v f hf)

end SubGaussian

end FroehlichSpencer.BKT

end
