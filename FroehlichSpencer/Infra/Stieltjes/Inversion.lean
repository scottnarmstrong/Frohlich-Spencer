/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Stieltjes.Transform
public import FroehlichSpencer.Infra.Stieltjes.Poisson
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Poisson inversion and uniqueness for the Stieltjes transform

For a finite measure `μ` on `ℝ`: the Fubini identity relating the Poisson smoothing of an
integrable continuous `f` to `(1/π) ∫ f(E) Im S_μ(E + iη) dE`, weak Stieltjes–Perron inversion for
continuous compactly supported `f`, and uniqueness: finite measures with equal Stieltjes
transforms on the upper half-plane (or on a set accumulating at a point of it) are equal.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set

namespace FroehlichSpencer.Infra

/-- Integrability on `volume.prod μ` of `(E, t) ↦ f E · P_η(t − E)` for integrable continuous
`f`. -/
theorem integrable_poissonKernel_prod (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) {η : ℝ} (hη : 0 < η) :
    Integrable (fun p : ℝ × ℝ => f p.1 * poissonKernel η (p.2 - p.1)) (volume.prod μ) := by
  have hb : Integrable (fun p : ℝ × ℝ => ‖f p.1‖ * (1 / (Real.pi * η))) (volume.prod μ) :=
    hfi.norm.mul_prod (integrable_const (1 / (Real.pi * η)))
  refine hb.mono' ?_ (Eventually.of_forall fun p => ?_)
  · have : Continuous fun x : ℝ => poissonKernel η x := by
      unfold poissonKernel; fun_prop (disch := intro x; positivity)
    exact (hf.comp continuous_fst |>.mul (this.comp (continuous_snd.sub continuous_fst)))
      |>.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poissonKernel_nonneg hη.le _),
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (poissonKernel_le hη _) (abs_nonneg _)

theorem integral_poissonSmooth_eq (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) {η : ℝ} (hη : 0 < η) :
    ∫ t, (∫ x, f (t - x) * poissonKernel η x) ∂μ =
      ∫ E, f E * (stieltjes μ (E + η * I)).im / Real.pi := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h1 : ∀ t, ∫ x, f (t - x) * poissonKernel η x = ∫ E, f E * poissonKernel η (t - E) := by
    intro t
    have := integral_sub_left_eq_self
      (fun E : ℝ => f E * poissonKernel η (t - E)) volume t
    simp only [sub_sub_cancel] at this
    exact this
  have h2 : ∀ E, f E * (stieltjes μ (E + η * I)).im / Real.pi
      = ∫ t, f E * poissonKernel η (t - E) ∂μ := by
    intro E
    rw [im_stieltjes μ E hη, integral_const_mul]
    have : ∀ t : ℝ, η / ((t - E) ^ 2 + η ^ 2) = Real.pi * poissonKernel η (t - E) := by
      intro t
      rw [← im_inv_ofReal_sub, im_inv_ofReal_sub_eq_poissonKernel]
    simp only [this]
    rw [integral_const_mul]
    field_simp
  simp only [h1, h2]
  exact (integral_integral_swap (f := fun E t : ℝ => f E * poissonKernel η (t - E))
    (integrable_poissonKernel_prod μ hf hfi hη)).symm

/-- The Poisson smoothing of an integrable continuous `f` is integrable against a finite measure. -/
theorem integrable_poissonSmooth (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) {η : ℝ} (hη : 0 < η) :
    Integrable (fun t => ∫ x, f (t - x) * poissonKernel η x) μ := by
  have h1 : ∀ t, ∫ x, f (t - x) * poissonKernel η x = ∫ E, f E * poissonKernel η (t - E) := by
    intro t
    have := integral_sub_left_eq_self
      (fun E : ℝ => f E * poissonKernel η (t - E)) volume t
    simp only [sub_sub_cancel] at this
    exact this
  simp only [h1]
  exact (integrable_poissonKernel_prod μ hf hfi hη).integral_prod_right

theorem tendsto_integral_im_stieltjes (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun η : ℝ => ∫ E, f E * (stieltjes μ (E + η * I)).im / Real.pi) (𝓝[>] 0)
      (𝓝 (∫ t, f t ∂μ)) := by
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfc
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
  have hU := tendsto_poissonSmooth_uniformly (hfc.uniformContinuous_of_continuous hf)
    (C := C) (fun t => by simpa only [Real.norm_eq_abs] using hC t)
  have hfμ : Integrable f μ := hf.integrable_of_hasCompactSupport hfc
  refine Tendsto.congr' ?_ ?_ (f₁ := fun η : ℝ => ∫ t, (∫ x, f (t - x) * poissonKernel η x) ∂μ)
  · filter_upwards [self_mem_nhdsWithin] with η hη
    exact integral_poissonSmooth_eq μ hf hfi hη
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hm : 0 ≤ μ.real univ := measureReal_nonneg
  have hδ : 0 < ε / (μ.real univ + 1) := by positivity
  filter_upwards [Metric.tendstoUniformly_iff.1 hU _ hδ, self_mem_nhdsWithin] with η h hη
  have hη : 0 < η := hη
  rw [dist_eq_norm, ← integral_sub (integrable_poissonSmooth μ hf hfi hη) hfμ]
  have hb := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun t => (∫ x, f (t - x) * poissonKernel η x) - f t) (C := ε / (μ.real univ + 1))
    (Eventually.of_forall fun t => by
      have := h t
      rw [dist_eq_norm, norm_sub_rev] at this
      exact this.le)
  refine lt_of_le_of_lt hb ?_
  calc ε / (μ.real univ + 1) * μ.real univ
      < ε / (μ.real univ + 1) * (μ.real univ + 1) :=
        mul_lt_mul_of_pos_left (by linarith) hδ
    _ = ε := by field_simp

/-- A continuous trapezoidal cutoff, equal to `1` on `[-n, n]`, vanishing outside
`(-(n+1), n+1)`, with values in `[0, 1]`. -/
noncomputable def trapezoidCutoff (n : ℕ) (x : ℝ) : ℝ := max 0 (min 1 ((n : ℝ) + 1 - |x|))

theorem continuous_trapezoidCutoff (n : ℕ) : Continuous (trapezoidCutoff n) := by
  unfold trapezoidCutoff; fun_prop

theorem trapezoidCutoff_nonneg (n : ℕ) (x : ℝ) : 0 ≤ trapezoidCutoff n x := le_max_left _ _

theorem trapezoidCutoff_le_one (n : ℕ) (x : ℝ) : trapezoidCutoff n x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem trapezoidCutoff_eq_zero {n : ℕ} {x : ℝ} (hx : (n : ℝ) + 1 ≤ |x|) :
    trapezoidCutoff n x = 0 := by
  unfold trapezoidCutoff
  exact max_eq_left (min_le_of_right_le (by linarith))

theorem trapezoidCutoff_eq_one {n : ℕ} {x : ℝ} (hx : |x| ≤ n) : trapezoidCutoff n x = 1 := by
  unfold trapezoidCutoff
  rw [min_eq_left (by linarith)]
  exact max_eq_right zero_le_one

theorem hasCompactSupport_mul_trapezoidCutoff (n : ℕ) {g : ℝ → ℝ} :
    HasCompactSupport fun x => g x * trapezoidCutoff n x := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -((n : ℝ) + 1)) (b := (n : ℝ) + 1))
    fun x hx => ?_
  have : (n : ℝ) + 1 ≤ |x| := by
    by_contra h
    rw [not_le, abs_lt] at h
    exact hx ⟨h.1.le, h.2.le⟩
  rw [trapezoidCutoff_eq_zero this, mul_zero]

private theorem ext_of_integral_eq_compactSupport {μ ν : Measure ℝ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → ∫ t, f t ∂μ = ∫ t, f t ∂ν) :
    μ = ν := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
  have key : ∀ m : Measure ℝ, [IsFiniteMeasure m] →
      Tendsto (fun n : ℕ => ∫ t, g t * trapezoidCutoff n t ∂m) atTop (𝓝 (∫ t, g t ∂m)) := by
    intro m _
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖g‖) (fun n => ?_)
      (integrable_const _) (fun n => Eventually.of_forall fun t => ?_)
      (Eventually.of_forall fun t => ?_)
    · exact (g.continuous.mul (continuous_trapezoidCutoff n)).aestronglyMeasurable
    · rw [norm_mul]
      calc ‖g t‖ * ‖trapezoidCutoff n t‖ ≤ ‖g‖ * 1 := by
            refine mul_le_mul (g.norm_coe_le_norm t) ?_ (norm_nonneg _) (norm_nonneg _)
            rw [Real.norm_eq_abs, abs_of_nonneg (trapezoidCutoff_nonneg n t)]
            exact trapezoidCutoff_le_one n t
        _ = ‖g‖ := mul_one _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈|t|⌉₊] with n hn
      rw [trapezoidCutoff_eq_one ((Nat.le_ceil _).trans (by exact_mod_cast hn)), mul_one]
  refine tendsto_nhds_unique (key μ) ((key ν).congr fun n => ?_)
  exact (h _ (g.continuous.mul (continuous_trapezoidCutoff n))
    (hasCompactSupport_mul_trapezoidCutoff n)).symm

theorem ext_of_stieltjes_eq {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ z : ℂ, 0 < z.im → stieltjes μ z = stieltjes ν z) : μ = ν := by
  refine ext_of_integral_eq_compactSupport fun f hf hfc => ?_
  refine tendsto_nhds_unique (tendsto_integral_im_stieltjes μ hf hfc) ?_
  refine (tendsto_integral_im_stieltjes ν hf hfc).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hη : 0 < η := hη
  refine integral_congr_ae (Eventually.of_forall fun E => ?_)
  simp only [h (E + η * I) (by simpa using hη)]

theorem ext_of_stieltjes_eq_frequently {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {D : Set ℂ} {z₀ : ℂ} (hz₀ : 0 < z₀.im) (hD : ∃ᶠ z in 𝓝[≠] z₀, z ∈ D)
    (h : ∀ z ∈ D, stieltjes μ z = stieltjes ν z) : μ = ν := by
  have hconv : Convex ℝ {z : ℂ | 0 < z.im} := by
    intro a ha b hb s t hs ht hst
    simp only [mem_ofPred_eq, add_im, smul_im, smul_eq_mul] at *
    rcases hs.eq_or_lt with rfl | hs'
    · have : t = 1 := by linarith
      subst this; simpa using hb
    · nlinarith [mul_pos hs' ha, mul_nonneg ht hb.le]
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (analyticOnNhd_stieltjes μ)
    (analyticOnNhd_stieltjes ν) hconv.isPreconnected hz₀ (hD.mono fun z hz => h z hz)
  exact ext_of_stieltjes_eq fun z hz => heq hz
