/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Villain.CurrentFormula
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# The real cosine observable in the rooted Villain measure

The bounded real observable is integrable under the finite-volume Villain density. Its expectation
is the real current ratio from KP §1.4, p. 4 and §6.1, p. 33.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FroehlichSpencer.BKT.Villain

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- The scalar Fourier summand for the periodized Gaussian. -/
def villainCosineFourierTerm (β : ℝ) (q : ℤ) (x : ℝ) : ℝ :=
  Real.exp (-((q : ℝ) ^ 2) / (2 * β)) * Real.cos ((q : ℝ) * x)

/-- The periodized Gaussian is continuous, by uniform convergence of its real Fourier series. -/
theorem continuous_villainWeight (β : ℝ) (hβ : 0 < β) :
    Continuous (villainWeight β) := by
  let a : ℤ → ℝ := fun q => Real.exp (-((q : ℝ) ^ 2) / (2 * β))
  have ha : Summable a := by
    simpa [a] using VillainWeight.villainWeight_fourier_coeff_summable hβ
  have hcont : ∀ q : ℤ, Continuous (villainCosineFourierTerm β q) := by
    intro q
    unfold villainCosineFourierTerm
    fun_prop
  have hbound (q : ℤ) (x : ℝ) :
      ‖villainCosineFourierTerm β q x‖ ≤ a q := by
    unfold villainCosineFourierTerm a
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-((q : ℝ) ^ 2) / (2 * β)) * |Real.cos ((q : ℝ) * x)| ≤
          Real.exp (-((q : ℝ) ^ 2) / (2 * β)) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
      _ = Real.exp (-((q : ℝ) ^ 2) / (2 * β)) := by ring
  have htsum : Continuous (fun x : ℝ => ∑' q : ℤ, villainCosineFourierTerm β q x) :=
    continuous_tsum hcont ha hbound
  have hfourier :
      villainWeight β =
        fun x => (2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) *
          ∑' q : ℤ, villainCosineFourierTerm β q x := by
    funext x
    simpa [villainCosineFourierTerm] using
      VillainWeight.villainWeight_fourier_real hβ x
  exact hfourier ▸ continuous_const.mul htsum

/-- A uniform finite bound for the one-edge Villain weight from the absolutely summable Fourier
coefficients. -/
theorem villainWeight_fourier_bound (β : ℝ) (hβ : 0 < β) (x : ℝ) :
    villainWeight β x ≤
      (2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) *
        ∑' q : ℤ, Real.exp (-((q : ℝ) ^ 2) / (2 * β)) := by
  let a : ℤ → ℝ := fun q => Real.exp (-((q : ℝ) ^ 2) / (2 * β))
  let f : ℤ → ℝ := fun q => villainCosineFourierTerm β q x
  have ha : Summable a := by
    simpa [a] using VillainWeight.villainWeight_fourier_coeff_summable hβ
  have hf : Summable f := by
    apply Summable.of_norm_bounded ha
    intro q
    change ‖Real.exp (-((q : ℝ) ^ 2) / (2 * β)) *
      Real.cos ((q : ℝ) * x)‖ ≤ Real.exp (-((q : ℝ) ^ 2) / (2 * β))
    calc
      ‖Real.exp (-((q : ℝ) ^ 2) / (2 * β)) *
          Real.cos ((q : ℝ) * x)‖ =
          Real.exp (-((q : ℝ) ^ 2) / (2 * β)) *
            |Real.cos ((q : ℝ) * x)| := by
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-((q : ℝ) ^ 2) / (2 * β)) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
      _ = Real.exp (-((q : ℝ) ^ 2) / (2 * β)) := by ring
  have hterm (q : ℤ) : f q ≤ a q := by
    change a q * Real.cos ((q : ℝ) * x) ≤ a q
    calc
      a q * Real.cos ((q : ℝ) * x) ≤ a q * 1 :=
        mul_le_mul_of_nonneg_left (Real.cos_le_one _) (Real.exp_pos _).le
      _ = a q := by ring
  have hsum : (∑' q : ℤ, f q) ≤ ∑' q : ℤ, a q := hf.tsum_le_tsum hterm ha
  rw [VillainWeight.villainWeight_fourier_real hβ x]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- The real product of edge weights in a rooted graph. -/
def villainRealDensity (G : Multigraph V E) (z : V) (β : ℝ)
    (θ : FreeAngles V z) : ℝ :=
  ∏ e, villainWeight β
    (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e))

/-- The complex density with a positive spin character inserted. -/
def villainCharacterIntegrand (G : Multigraph V E) (z : V) (β : ℝ)
    (site : FreeVertices V z) (θ : FreeAngles V z) : ℂ :=
  (∏ e, (villainWeight β
    (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℂ)) *
      Complex.exp (Complex.I * (θ site : ℂ))

/-- The real density multiplied by the cosine observable. -/
def villainCosineIntegrand (G : Multigraph V E) (z : V) (β : ℝ)
    (site : FreeVertices V z) (θ : FreeAngles V z) : ℝ :=
  villainRealDensity G z β θ * Real.cos (θ site)

omit [Fintype V] in
/-- The root-pinned angle at a fixed vertex is continuous in the free angle coordinates. -/
theorem continuous_pinnedAngle (z j : V) :
    Continuous (fun θ : FreeAngles V z => pinnedAngle z θ j) := by
  by_cases hj : j = z
  · simpa [pinnedAngle, hj] using
      (continuous_const : Continuous (fun _ : FreeAngles V z => (0 : ℝ)))
  · simpa [pinnedAngle, hj] using
      (continuous_apply (⟨j, hj⟩ : FreeVertices V z))

omit [Fintype V] in
/-- The edge product is continuous on the root-pinned angle space. -/
theorem continuous_villainRealDensity (G : Multigraph V E) (z : V) (β : ℝ)
    (hβ : 0 < β) : Continuous (villainRealDensity G z β) := by
  unfold villainRealDensity
  apply continuous_finsetProd
  intro e he
  apply (continuous_villainWeight β hβ).comp
  exact (continuous_pinnedAngle z (G.src e)).sub
    (continuous_pinnedAngle z (G.tgt e))

omit [Fintype V] in
/-- The real edge product is nonnegative and bounded by the product of the one-edge Fourier
coefficient sums. -/
theorem villainRealDensity_nonneg_le (G : Multigraph V E) (z : V) (β : ℝ)
    (hβ : 0 < β) (θ : FreeAngles V z) :
    0 ≤ villainRealDensity G z β θ ∧
      villainRealDensity G z β θ ≤
        ((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) *
          ∑' q : ℤ, Real.exp (-((q : ℝ) ^ 2) / (2 * β))) ^ Fintype.card E := by
  let C : ℝ := (2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) *
    ∑' q : ℤ, Real.exp (-((q : ℝ) ^ 2) / (2 * β))
  constructor
  · unfold villainRealDensity
    exact Finset.prod_nonneg fun e he => (VillainWeight.villainWeight_pos hβ _).le
  · unfold villainRealDensity
    calc
      ∏ e, villainWeight β
          (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) ≤
          ∏ _e : E, C := by
        apply Finset.prod_le_prod₀
        · intro e he
          exact (VillainWeight.villainWeight_pos hβ _).le
        · intro e he
          exact villainWeight_fourier_bound β hβ _
      _ = C ^ Fintype.card E := by simp [C]

/-- The complex character integrand is integrable under the restricted product angle measure. -/
theorem integrable_villainCharacterIntegrand (G : Multigraph V E) (z : V) (β : ℝ)
    (hβ : 0 < β) (site : FreeVertices V z) :
    Integrable (villainCharacterIntegrand G z β site) (rootedAngleMeasure z) := by
  classical
  have hμ : IsFiniteMeasure (rootedAngleMeasure z) := by
    dsimp [rootedAngleMeasure]
    infer_instance
  have hcont : Continuous (villainCharacterIntegrand G z β site) := by
    unfold villainCharacterIntegrand
    apply Continuous.mul
    · apply continuous_finsetProd
      intro e he
      apply Complex.continuous_ofReal.comp
      apply (continuous_villainWeight β hβ).comp
      exact (continuous_pinnedAngle z (G.src e)).sub
        (continuous_pinnedAngle z (G.tgt e))
    · fun_prop
  have hbound : ∀ θ : FreeAngles V z,
      ‖villainCharacterIntegrand G z β site θ‖ ≤
        ((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) *
          ∑' q : ℤ, Real.exp (-((q : ℝ) ^ 2) / (2 * β))) ^ Fintype.card E := by
    intro θ
    rw [villainCharacterIntegrand, Complex.norm_mul, Complex.norm_exp]
    have hre : (Complex.I * (θ site : ℂ)).re = 0 := by simp [Complex.mul_re]
    rw [hre, Real.exp_zero, mul_one, Complex.norm_prod]
    calc
      ∏ e, ‖(villainWeight β
          (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℂ)‖ ≤
          ∏ _e : E,
            (2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) *
              ∑' q : ℤ, Real.exp (-((q : ℝ) ^ 2) / (2 * β)) := by
        apply Finset.prod_le_prod₀
        · intro e he
          rw [Complex.norm_real, Real.norm_of_nonneg
            (VillainWeight.villainWeight_pos hβ _).le]
          exact (VillainWeight.villainWeight_pos hβ _).le
        · intro e he
          rw [Complex.norm_real, Real.norm_of_nonneg
            (VillainWeight.villainWeight_pos hβ _).le]
          exact villainWeight_fourier_bound β hβ _
      _ = _ := by simp
  exact Integrable.of_bound hcont.aestronglyMeasurable _
    (Filter.Eventually.of_forall hbound)

/-- The cosine density is integrable: the observable is bounded by one and the Villain density
has a uniform Fourier-series bound on the finite angle box. -/
theorem integrable_villainCosineIntegrand (G : Multigraph V E) (z : V) (β : ℝ)
    (hβ : 0 < β) (site : FreeVertices V z) :
    Integrable (villainCosineIntegrand G z β site) (rootedAngleMeasure z) := by
  classical
  have hμ : IsFiniteMeasure (rootedAngleMeasure z) := by
    dsimp [rootedAngleMeasure]
    infer_instance
  have hcont : Continuous (villainCosineIntegrand G z β site) := by
    unfold villainCosineIntegrand
    exact (continuous_villainRealDensity G z β hβ).mul
      (Real.continuous_cos.comp (continuous_apply site))
  have hbound (θ : FreeAngles V z) :
      ‖villainCosineIntegrand G z β site θ‖ ≤
        ((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) *
          ∑' q : ℤ, Real.exp (-((q : ℝ) ^ 2) / (2 * β))) ^ Fintype.card E := by
    rw [villainCosineIntegrand, Real.norm_eq_abs, abs_mul]
    have hd := villainRealDensity_nonneg_le G z β hβ θ
    rw [abs_of_nonneg hd.1]
    calc
      villainRealDensity G z β θ * |Real.cos (θ site)| ≤
          villainRealDensity G z β θ * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hd.1
      _ = villainRealDensity G z β θ := by ring
      _ ≤ _ := hd.2
  exact Integrable.of_bound hcont.aestronglyMeasurable _
    (Filter.Eventually.of_forall hbound)

/-- The rooted Villain cosine expectation, defined as the real observable integral divided by the
partition function (KP §1.4, p. 4). -/
noncomputable def villainCosExpectation (G : Multigraph V E) (z : V) (β : ℝ)
    (site : FreeVertices V z) : ℝ :=
  (∫ θ, villainCosineIntegrand G z β site θ ∂rootedAngleMeasure z) /
    villainPartitionFunction G z β

/-- The normalized complex character expectation is real and equals the real current-sum ratio.
-/
theorem villainCharacterExpectation_eq_real_current_ratio (G : Multigraph V E) (z : V)
    (β : ℝ) (hβ : 0 < β) (site : FreeVertices V z) :
    villainCharacterExpectation G z β site =
      ((∑' q : E → ℤ, sourceCurrentGaussianWeight G z site.1 β q) /
        (∑' q : E → ℤ, neutralCurrentGaussianWeight G z β q) : ℂ) := by
  rw [villainCharacterExpectation_eq_current_ratio G z β hβ site]
  have hsource :
      (∑' q : E → ℤ, (sourceCurrentGaussianWeight G z site.1 β q : ℂ)) =
        ((∑' q : E → ℤ, sourceCurrentGaussianWeight G z site.1 β q : ℝ) : ℂ) := by
    rw [← Complex.ofReal_tsum]
  have hneutral :
      (∑' q : E → ℤ, (neutralCurrentGaussianWeight G z β q : ℂ)) =
        ((∑' q : E → ℤ, neutralCurrentGaussianWeight G z β q : ℝ) : ℂ) := by
    rw [← Complex.ofReal_tsum]
  rw [hsource, hneutral, ← Complex.ofReal_div]

/-- The real cosine numerator is the real part of the complex positive-character numerator. -/
theorem integral_villainCosineIntegrand_eq_re_character (G : Multigraph V E) (z : V)
    (β : ℝ) (hβ : 0 < β) (site : FreeVertices V z) :
    (∫ θ, villainCosineIntegrand G z β site θ ∂rootedAngleMeasure z) =
      Complex.re (∫ θ, villainCharacterIntegrand G z β site θ ∂rootedAngleMeasure z) := by
  calc
    (∫ θ, villainCosineIntegrand G z β site θ ∂rootedAngleMeasure z) =
        ∫ θ, (villainCharacterIntegrand G z β site θ).re ∂rootedAngleMeasure z := by
      apply integral_congr_ae
      filter_upwards with θ
      unfold villainCosineIntegrand villainCharacterIntegrand villainRealDensity
      rw [← Complex.ofReal_prod, Complex.mul_re]
      have hphase : Complex.I * (θ site : ℂ) = (θ site : ℂ) * Complex.I := by ring
      rw [hphase, Complex.exp_ofReal_mul_I]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
    _ = Complex.re (∫ θ, villainCharacterIntegrand G z β site θ
          ∂rootedAngleMeasure z) :=
      integral_re (integrable_villainCharacterIntegrand G z β hβ site)

/-- The cosine expectation equals the real positive-character expectation and is the real ratio of
unit-source to neutral current sums. This is KP's finite-volume observable formula. -/
theorem villainCosExpectation_eq_character_and_current_ratio (G : Multigraph V E) (z : V)
    (β : ℝ) (hβ : 0 < β) (site : FreeVertices V z) :
    villainCosExpectation G z β site =
      (∑' q : E → ℤ, sourceCurrentGaussianWeight G z site.1 β q) /
        (∑' q : E → ℤ, neutralCurrentGaussianWeight G z β q) ∧
      villainCharacterExpectation G z β site =
        (villainCosExpectation G z β site : ℂ) := by
  classical
  let A : ℝ :=
    ((2 * Real.pi * β) ^ (-(1 / 2 : ℝ))) ^ Fintype.card E *
      (2 * Real.pi) ^ Fintype.card (FreeVertices V z)
  have hsource :
      (∑' q : E → ℤ, (sourceCurrentGaussianWeight G z site.1 β q : ℂ)) =
        ((∑' q : E → ℤ, sourceCurrentGaussianWeight G z site.1 β q : ℝ) : ℂ) := by
    rw [← Complex.ofReal_tsum]
  have hnum := villain_character_current_expansion_complex G z β hβ site
  have hnumReal :
      (∫ θ, villainCosineIntegrand G z β site θ ∂rootedAngleMeasure z) =
        A * ∑' q : E → ℤ, sourceCurrentGaussianWeight G z site.1 β q := by
    calc
      _ = Complex.re (∫ θ, villainCharacterIntegrand G z β site θ
            ∂rootedAngleMeasure z) :=
        integral_villainCosineIntegrand_eq_re_character G z β hβ site
      _ = A * ∑' q : E → ℤ, sourceCurrentGaussianWeight G z site.1 β q := by
        change Complex.re (∫ θ, (∏ e, (villainWeight β
          (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℂ)) *
            Complex.exp (Complex.I * (θ site : ℂ)) ∂rootedAngleMeasure z) = _
        rw [hnum, hsource]
        rw [← Complex.ofReal_pow, ← Complex.ofReal_pow,
          ← Complex.ofReal_mul, ← Complex.ofReal_mul]
        rw [Complex.ofReal_re]
  have hden : villainPartitionFunction G z β =
      A * ∑' q : E → ℤ, neutralCurrentGaussianWeight G z β q := by
    rw [villainPartitionFunction, villain_partition_current_expansion G z β hβ]
  have hsumpos : 0 < ∑' q : E → ℤ, neutralCurrentGaussianWeight G z β q :=
    neutralCurrentGaussianWeight_tsum_pos G z β hβ
  have hratio : villainCosExpectation G z β site =
      (∑' q : E → ℤ, sourceCurrentGaussianWeight G z site.1 β q) /
        (∑' q : E → ℤ, neutralCurrentGaussianWeight G z β q) := by
    unfold villainCosExpectation
    rw [hnumReal, hden]
    have hA : A ≠ 0 := by
      dsimp [A]
      positivity
    field_simp [hA, ne_of_gt hsumpos]
  refine ⟨hratio, ?_⟩
  rw [villainCharacterExpectation_eq_real_current_ratio G z β hβ site, hratio]
  exact (Complex.ofReal_div _ _).symm

end FroehlichSpencer.BKT.Villain

end
