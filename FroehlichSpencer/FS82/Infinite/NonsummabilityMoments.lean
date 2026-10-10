module
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory MeasureTheory Topology

@[expose] public section

namespace FroehlichSpencer.FS82.Infinite.Nonsummability

noncomputable def symSecondDifference (M : ℝ → ℝ) (t : ℝ) : ℝ :=
  (M t + M (-t) - 2) / t ^ 2

theorem symSecondDifference_tendsto_secondDerivative
    (f : ℝ → ℝ) (c : ℝ) (hf : ContDiff ℝ 2 f)
    (hf0 : f 0 = 1) (hf1 : deriv f 0 = 0)
    (hf2 : iteratedDeriv 2 f 0 = c) :
    Tendsto (symSecondDifference f) (𝓝[≠] (0:ℝ)) (𝓝 c) := by
  have hpoly (t : ℝ) : taylorWithinEval f 2 Set.univ 0 t = 1 + c * t^2 / 2 := by
    rw [taylor_within_apply]
    simp [Finset.sum_range_succ, iteratedDerivWithin_univ, iteratedDeriv_succ,
      hf0, hf1, hf2]
    ring
  have hTaylor := Real.taylor_tendsto (f := f) (x₀ := (0:ℝ))
    (n := 2) convex_univ (Set.mem_univ _) hf.contDiffOn
  have hRem : Tendsto (fun t => (f t - (1 + c * t^2 / 2)) / t^2)
      (𝓝 (0:ℝ)) (𝓝 0) := by
    have heq : (fun x => (f x - taylorWithinEval f 2 Set.univ 0 x) / (x - 0) ^ 2) =ᶠ[𝓝[Set.univ] 0]
        (fun t => (f t - (1 + c * t^2 / 2)) / t^2) := by
      filter_upwards [] with t
      rw [hpoly t]
      ring
    simpa using hTaylor.congr' heq
  have hRem' : Tendsto (fun t => (f (-t) - (1 + c * (-t)^2 / 2)) / (-t)^2)
      (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    exact hRem.comp (by simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
  have hRem₁ : Tendsto (fun t => (f t - (1 + c * t^2 / 2)) / t^2)
      (𝓝[≠] (0:ℝ)) (𝓝 0) := hRem.mono_left (nhdsWithin_le_nhds)
  have hsum : Tendsto (fun t =>
      (f t - (1 + c * t^2 / 2)) / t^2 +
      (f (-t) - (1 + c * (-t)^2 / 2)) / (-t)^2 + c)
      (𝓝[≠] (0:ℝ)) (𝓝 c) := by
    simpa using (hRem₁.add hRem').add tendsto_const_nhds
  have heq : (fun t => symSecondDifference f t) =ᶠ[𝓝[≠] (0:ℝ)]
      (fun t => (f t - (1 + c * t^2 / 2)) / t^2 +
        (f (-t) - (1 + c * (-t)^2 / 2)) / (-t)^2 + c) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht
    dsimp [symSecondDifference]
    field_simp [ht0]
    ring_nf
  exact hsum.congr' heq.symm

theorem mgf_symSecondDifference_squeeze
    (M : ℝ → ℝ) (a b : ℝ)
    (hM : ∀ t, Real.exp (a * t ^ 2 / 2) ≤ M t ∧ M t ≤ Real.exp (b * t ^ 2 / 2))
    {t : ℝ} (ht : t ≠ 0) :
    2 * (Real.exp (a * t ^ 2 / 2) - 1) / t ^ 2 ≤ symSecondDifference M t ∧
      symSecondDifference M t ≤
        2 * (Real.exp (b * t ^ 2 / 2) - 1) / t ^ 2 := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  have hlow : 2 * Real.exp (a * t ^ 2 / 2) ≤ M t + M (-t) := by
    have h₁ := (hM t).1
    have h₂ := (hM (-t)).1
    have h₂' : Real.exp (a * t ^ 2 / 2) ≤ M (-t) := by simpa [neg_sq] using h₂
    nlinarith [add_le_add h₁ h₂']
  have hupp : M t + M (-t) ≤ 2 * Real.exp (b * t ^ 2 / 2) := by
    have h₁ := (hM t).2
    have h₂ := (hM (-t)).2
    have h₂' : M (-t) ≤ Real.exp (b * t ^ 2 / 2) := by simpa [neg_sq] using h₂
    nlinarith [add_le_add h₁ h₂']
  constructor
  · unfold symSecondDifference
    have hnum : 2 * (Real.exp (a * t ^ 2 / 2) - 1) ≤ M t + M (-t) - 2 := by linarith
    exact (div_le_div_of_nonneg_right hnum (sq_nonneg t))
  · unfold symSecondDifference
    have hnum : M t + M (-t) - 2 ≤ 2 * (Real.exp (b * t ^ 2 / 2) - 1) := by linarith
    exact (div_le_div_of_nonneg_right hnum (sq_nonneg t))


private theorem expQuadratic_hasDerivAt (c t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (c * u ^ 2))
      (Real.exp (c * t ^ 2) * (c * (2 * t))) t := by
  have hq : HasDerivAt (fun u : ℝ => c * u ^ 2) (c * (2 * t)) t := by
    simpa [Function.id_def, mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id t).pow 2).const_mul c
  simpa [Function.comp_def, Function.id_def, mul_comm, mul_left_comm, mul_assoc] using
    (Real.hasDerivAt_exp (c * t ^ 2)).comp t hq

private theorem expQuadratic_symSecondDifference_tendsto (a : ℝ) :
    Tendsto (fun t => 2 * (Real.exp (a * t ^ 2 / 2) - 1) / t ^ 2)
      (𝓝[≠] (0:ℝ)) (𝓝 a) := by
  let c := a / 2
  let f : ℝ → ℝ := fun t => Real.exp (c * t ^ 2)
  have hf : ContDiff ℝ 2 f := by
    dsimp [f]
    fun_prop
  have hf0 : f 0 = 1 := by simp [f]
  have hf1 : deriv f 0 = 0 := by
    have h := expQuadratic_hasDerivAt c 0
    simpa [f] using h.deriv
  have hf2 : iteratedDeriv 2 f 0 = 2 * c := by
    have hmul : HasDerivAt (fun t : ℝ => Real.exp (c * t ^ 2) * (c * (2 * t)))
        (2 * c) 0 := by
      have h₁ : HasDerivAt (fun t : ℝ => Real.exp (c * t ^ 2)) 0 0 := by
        simpa using expQuadratic_hasDerivAt c 0
      have h₂ : HasDerivAt (fun t : ℝ => c * (2 * t)) (2 * c) 0 := by
        simpa [Function.id_def, mul_comm, mul_left_comm, mul_assoc] using
          (hasDerivAt_id (0:ℝ)).const_mul (2 * c)
      convert h₁.mul h₂ using 1
      simp
    have hderiv : deriv f = fun t => Real.exp (c * t ^ 2) * (c * (2 * t)) := by
      funext t
      exact (expQuadratic_hasDerivAt c t).deriv
    rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv]
    exact hmul.deriv
  have hlim := symSecondDifference_tendsto_secondDerivative f (2 * c) hf hf0 hf1 hf2
  have heq : (fun t => 2 * (Real.exp (a * t ^ 2 / 2) - 1) / t ^ 2) =ᶠ[𝓝[≠] (0:ℝ)]
      (symSecondDifference f) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hct : c = a / 2 := rfl
    simp only [symSecondDifference, f, hct, neg_sq]
    ring_nf
  convert hlim.congr' heq.symm using 1
  dsimp [c]
  ring_nf

theorem variance_mem_Icc_of_mgf_quadratic_bounds
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b : ℝ)
    (hExp : ∀ t : ℝ, Integrable (fun x : ℝ => Real.exp (t * x)) μ)
    (hM : ∀ t : ℝ,
      Real.exp (a * t ^ 2 / 2) ≤ ProbabilityTheory.mgf id μ t ∧
      ProbabilityTheory.mgf id μ t ≤ Real.exp (b * t ^ 2 / 2)) :
    a ≤ ProbabilityTheory.variance id μ ∧ ProbabilityTheory.variance id μ ≤ b := by
  have hset : ProbabilityTheory.integrableExpSet id μ = Set.univ := by
    ext t
    simp [ProbabilityTheory.integrableExpSet, hExp]
  have hAna := ProbabilityTheory.analyticOnNhd_mgf (X := id) (μ := μ)
  rw [hset, interior_univ] at hAna
  have hf : ContDiff ℝ 2 (ProbabilityTheory.mgf id μ) := hAna.contDiff
  have h0 : (0:ℝ) ∈ interior (ProbabilityTheory.integrableExpSet id μ) := by
    rw [hset, interior_univ]
    simp
  have hmean : ∫ x : ℝ, x ∂μ = 0 := by
    let f : ℝ → ℝ := ProbabilityTheory.mgf id μ
    have hloc : IsLocalMax (fun t => f t - Real.exp (b * t ^ 2 / 2)) 0 := by
      change ∀ᶠ t in 𝓝 (0:ℝ),
        f t - Real.exp (b * t ^ 2 / 2) ≤ f 0 - Real.exp (b * 0 ^ 2 / 2)
      filter_upwards [Filter.Eventually.of_forall fun t => (hM t).2] with t ht
      have hf0 : f 0 = 1 := by simp [f]
      rw [hf0]
      simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div, Real.exp_zero]
      linarith
    have hmgf : HasDerivAt f (∫ x : ℝ, x ∂μ) 0 := by
      simpa [f] using ProbabilityTheory.hasDerivAt_mgf (X := id) (μ := μ) h0
    have hquad : HasDerivAt (fun t : ℝ => Real.exp (b * t ^ 2 / 2)) 0 0 := by
      convert expQuadratic_hasDerivAt (b / 2) 0 using 1
      · ext t
        congr 1
        ring_nf
      · simp
    have hz := hloc.hasDerivAt_eq_zero (hmgf.sub hquad)
    simpa using hz
  have hm2 : iteratedDeriv 2 (ProbabilityTheory.mgf id μ) 0 = ∫ x : ℝ, x ^ 2 ∂μ := by
    simpa [Pi.pow_apply] using
      ProbabilityTheory.iteratedDeriv_mgf_zero (X := id) (μ := μ) h0 2
  have hsym := symSecondDifference_tendsto_secondDerivative
    (ProbabilityTheory.mgf id μ) (∫ x : ℝ, x ^ 2 ∂μ) hf (by simp)
    (by simpa [ProbabilityTheory.deriv_mgf h0] using hmean) hm2
  have hlow := expQuadratic_symSecondDifference_tendsto a
  have hupp := expQuadratic_symSecondDifference_tendsto b
  have hlowEventually :
      (fun t => 2 * (Real.exp (a * t ^ 2 / 2) - 1) / t ^ 2) ≤ᶠ[𝓝[≠] (0:ℝ)]
        symSecondDifference (ProbabilityTheory.mgf id μ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (mgf_symSecondDifference_squeeze (ProbabilityTheory.mgf id μ) a b hM ht).1
  have huppEventually :
      symSecondDifference (ProbabilityTheory.mgf id μ) ≤ᶠ[𝓝[≠] (0:ℝ)]
        (fun t => 2 * (Real.exp (b * t ^ 2 / 2) - 1) / t ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (mgf_symSecondDifference_squeeze (ProbabilityTheory.mgf id μ) a b hM ht).2
  have hlowBound : a ≤ ∫ x : ℝ, x ^ 2 ∂μ :=
    le_of_tendsto_of_tendsto hlow hsym hlowEventually
  have huppBound : ∫ x : ℝ, x ^ 2 ∂μ ≤ b :=
    le_of_tendsto_of_tendsto hsym hupp huppEventually
  have hvar : ProbabilityTheory.variance id μ = ∫ x : ℝ, x ^ 2 ∂μ := by
    rw [ProbabilityTheory.variance_eq_integral (μ := μ) (X := id) measurable_id.aemeasurable]
    simp [hmean]
  rw [hvar]
  exact ⟨hlowBound, huppBound⟩

end FroehlichSpencer.FS82.Infinite.Nonsummability
