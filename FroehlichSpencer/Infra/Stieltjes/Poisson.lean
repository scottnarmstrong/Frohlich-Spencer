/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Stieltjes.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The Poisson kernel as an approximate identity

Nonnegativity, integrability, total mass `1` and the sup bound for the Poisson kernel
`P_η(x) = η / (π (x² + η²))`, and the approximate-identity property: for bounded uniformly
continuous `f`, the Poisson smoothing `t ↦ ∫ f (t - x) P_η(x) dx` converges uniformly to `f` as
`η → 0⁺`; for bounded continuous `f` it converges pointwise.

The proofs rescale to `P_1` (`x = η s`) and use dominated convergence.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace FroehlichSpencer.Infra

theorem poissonKernel_nonneg {η : ℝ} (hη : 0 ≤ η) (x : ℝ) : 0 ≤ poissonKernel η x := by
  unfold poissonKernel
  positivity

private theorem poissonKernel_eq_scaled {η : ℝ} (hη : 0 < η) (x : ℝ) :
    poissonKernel η x = (Real.pi⁻¹ * η⁻¹) * (1 + (η⁻¹ * x) ^ 2)⁻¹ := by
  unfold poissonKernel
  have : (0 : ℝ) < Real.pi := Real.pi_pos
  field_simp
  ring

private theorem poissonKernel_mul {η : ℝ} (hη : 0 < η) (s : ℝ) :
    poissonKernel η (η * s) = η⁻¹ * poissonKernel 1 s := by
  unfold poissonKernel
  have : (0 : ℝ) < Real.pi := Real.pi_pos
  field_simp

theorem integrable_poissonKernel {η : ℝ} (hη : 0 < η) : Integrable (poissonKernel η) := by
  have h : Integrable fun x : ℝ => (1 + (η⁻¹ * x) ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hη.ne')
  have := h.const_mul (Real.pi⁻¹ * η⁻¹)
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [poissonKernel_eq_scaled hη]

theorem integral_poissonKernel {η : ℝ} (hη : 0 < η) : ∫ x, poissonKernel η x = 1 := by
  have h1 : ∫ x, poissonKernel η x
      = ∫ x : ℝ, (Real.pi⁻¹ * η⁻¹) * (1 + (η⁻¹ * x) ^ 2)⁻¹ := by
    simp only [poissonKernel_eq_scaled hη]
  rw [h1, integral_const_mul]
  have := Measure.integral_comp_mul_left (fun y : ℝ => (1 + y ^ 2)⁻¹) η⁻¹
  rw [this, integral_univ_inv_one_add_sq, inv_inv, abs_of_pos hη]
  have : (0 : ℝ) < Real.pi := Real.pi_pos
  simp only [smul_eq_mul]
  field_simp

theorem poissonKernel_le {η : ℝ} (hη : 0 < η) (x : ℝ) :
    poissonKernel η x ≤ 1 / (Real.pi * η) := by
  unfold poissonKernel
  have : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos this hη, sq_nonneg x, mul_nonneg (mul_pos this hη).le (sq_nonneg x)]

/-- Rescaling the smoothing integral to the kernel `P_1`. -/
private theorem integral_poissonKernel_mul {η : ℝ} (hη : 0 < η) (h : ℝ → ℝ) :
    ∫ x, h x * poissonKernel η x = ∫ s, h (η * s) * poissonKernel 1 s := by
  have := Measure.integral_comp_mul_left (fun x : ℝ => h x * poissonKernel η x) η
  simp only [poissonKernel_mul hη, abs_of_pos (inv_pos.2 hη), smul_eq_mul] at this
  have h2 : ∫ s, h (η * s) * poissonKernel 1 s
      = η * ∫ s, h (η * s) * (η⁻¹ * poissonKernel 1 s) := by
    rw [← integral_const_mul]
    congr 1
    funext s
    field_simp
  rw [h2, this]
  field_simp

private theorem integrable_smooth {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ t, |f t| ≤ C)
    (t η : ℝ) : Integrable fun s => f (t - η * s) * poissonKernel 1 s := by
  refine (integrable_poissonKernel one_pos).bdd_mul ?_
    (Eventually.of_forall fun s => ?_) (c := C)
  · exact (hf.comp (by fun_prop)).aestronglyMeasurable
  · simpa only [Real.norm_eq_abs] using hC _

/-- The difference between the smoothing and `f t`, in rescaled form. -/
private theorem smooth_sub_eq {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ t, |f t| ≤ C)
    (t η : ℝ) (hη : 0 < η) :
    (∫ x, f (t - x) * poissonKernel η x) - f t
      = ∫ s, (f (t - η * s) - f t) * poissonKernel 1 s := by
  rw [integral_poissonKernel_mul hη (fun x => f (t - x))]
  have h1 := integrable_smooth hf hC t η
  have h2 : Integrable fun s => f t * poissonKernel 1 s :=
    (integrable_poissonKernel one_pos).const_mul _
  simp only [sub_mul]
  rw [integral_sub h1 h2, integral_const_mul, integral_poissonKernel one_pos]
  ring

/-- The rescaled tail mass `∫_{|η s| > δ} P_1`. -/
private noncomputable def tailMass (δ η : ℝ) : ℝ :=
  ∫ s, Set.indicator {s : ℝ | δ < |η * s|} (poissonKernel 1) s

private theorem tendsto_tailMass {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (tailMass δ) (𝓝[>] 0) (𝓝 0) := by
  have := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[>] (0 : ℝ))
    (F := fun η s => Set.indicator {s : ℝ | δ < |η * s|} (poissonKernel 1) s)
    (f := fun _ => 0) (poissonKernel 1) ?_ ?_ (integrable_poissonKernel one_pos) ?_
  · have e : tailMass δ =
        fun η => ∫ s, Set.indicator {s : ℝ | δ < |η * s|} (poissonKernel 1) s := rfl
    rw [e]
    simpa only [integral_zero] using this
  · refine Eventually.of_forall fun η => ?_
    refine (integrable_poissonKernel one_pos).aestronglyMeasurable.indicator ?_
    exact measurableSet_lt measurable_const (by fun_prop)
  · refine Eventually.of_forall fun η => Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs]
    by_cases hs : s ∈ {s : ℝ | δ < |η * s|}
    · rw [Set.indicator_of_mem hs, abs_of_nonneg (poissonKernel_nonneg one_pos.le s)]
    · rw [Set.indicator_of_notMem hs, abs_zero]
      exact poissonKernel_nonneg one_pos.le s
  · refine Eventually.of_forall fun s => ?_
    have hc : Tendsto (fun η : ℝ => |η * s|) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun η : ℝ => |η * s|) (𝓝 0) (𝓝 |0 * s|) :=
        (by fun_prop : Continuous fun η : ℝ => |η * s|).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hc.eventually (gt_mem_nhds hδ)] with η hη
    rw [Set.indicator_of_notMem (by simpa using hη.le)]

/-- Quantitative bound on the smoothing error. -/
private theorem abs_smooth_sub_le {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ t, |f t| ≤ C)
    (t η δ ε : ℝ) (hη : 0 < η) (hδ : 0 ≤ δ) (hε : ∀ x, |x| ≤ δ → |f (t - x) - f t| ≤ ε) :
    |(∫ x, f (t - x) * poissonKernel η x) - f t| ≤ ε + 2 * C * tailMass δ η := by
  have hK := poissonKernel_nonneg (one_pos.le)
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε 0 (by simpa using hδ))
  rw [smooth_sub_eq hf hC t η hη]
  have hi1 := integrable_smooth hf hC t η
  have hi2 : Integrable fun s => f t * poissonKernel 1 s :=
    (integrable_poissonKernel one_pos).const_mul _
  have hi : Integrable fun s => (f (t - η * s) - f t) * poissonKernel 1 s := by
    simp only [sub_mul]; exact hi1.sub hi2
  have hind : Integrable fun s =>
      Set.indicator {s : ℝ | δ < |η * s|} (poissonKernel 1) s :=
    (integrable_poissonKernel one_pos).indicator
      (measurableSet_lt measurable_const (by fun_prop))
  have hb : Integrable fun s => ε * poissonKernel 1 s
      + 2 * C * Set.indicator {s : ℝ | δ < |η * s|} (poissonKernel 1) s :=
    ((integrable_poissonKernel one_pos).const_mul _).add (hind.const_mul _)
  calc |∫ s, (f (t - η * s) - f t) * poissonKernel 1 s|
      ≤ ∫ s, ‖(f (t - η * s) - f t) * poissonKernel 1 s‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ s, (ε * poissonKernel 1 s
          + 2 * C * Set.indicator {s : ℝ | δ < |η * s|} (poissonKernel 1) s) := by
        refine integral_mono hi.norm hb fun s => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK s)]
        by_cases hs : s ∈ {s : ℝ | δ < |η * s|}
        · rw [Set.indicator_of_mem hs]
          have h1 : |f (t - η * s) - f t| ≤ 2 * C := by
            calc |f (t - η * s) - f t| ≤ |f (t - η * s)| + |f t| := abs_sub _ _
              _ ≤ 2 * C := by linarith [hC (t - η * s), hC t]
          have h0 : 0 ≤ ε * poissonKernel 1 s := mul_nonneg hε0 (hK s)
          nlinarith [mul_le_mul_of_nonneg_right h1 (hK s)]
        · rw [Set.indicator_of_notMem hs]
          have : |η * s| ≤ δ := not_lt.1 hs
          have h1 := hε (η * s) this
          nlinarith [mul_le_mul_of_nonneg_right h1 (hK s)]
    _ = ε + 2 * C * tailMass δ η := by
        rw [integral_add ((integrable_poissonKernel one_pos).const_mul _) (hind.const_mul _),
          integral_const_mul, integral_const_mul, integral_poissonKernel one_pos, tailMass]
        ring

/-- Uniform approximation of a bounded uniformly continuous function by its Poisson smoothing. -/
theorem tendsto_poissonSmooth_uniformly {f : ℝ → ℝ} (hf : UniformContinuous f) {C : ℝ}
    (hC : ∀ t, |f t| ≤ C) :
    TendstoUniformly (fun (η : ℝ) (t : ℝ) => ∫ x, f (t - x) * poissonKernel η x) f (𝓝[>] 0) := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.1 hf (ε / 4) (by positivity)
  have hT := tendsto_tailMass (half_pos hδ)
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), tailMass (δ / 2) η < ε / (4 * (C + 1)) :=
    hT.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hev, self_mem_nhdsWithin] with η hη hη0
  intro t
  have hη0 : 0 < η := hη0
  have hb := abs_smooth_sub_le hf.continuous hC t η (δ / 2) (ε / 4) hη0 (half_pos hδ).le
    (fun x hx => by
      have := hδf (a := t - x) (b := t) (by
        rw [Real.dist_eq, sub_sub_cancel_left, abs_neg]; linarith)
      rw [Real.dist_eq] at this
      exact this.le)
  rw [Real.dist_eq, abs_sub_comm]
  have hpos : 0 < C + 1 := by linarith
  have h2 : 2 * C * tailMass (δ / 2) η ≤ 2 * (C + 1) * tailMass (δ / 2) η := by
    have : 0 ≤ tailMass (δ / 2) η := by
      unfold tailMass
      refine integral_nonneg fun s => ?_
      by_cases hs : s ∈ {s : ℝ | δ / 2 < |η * s|}
      · rw [Set.indicator_of_mem hs]; exact poissonKernel_nonneg one_pos.le s
      · rw [Set.indicator_of_notMem hs]; exact le_refl _
    nlinarith
  have h3 : 2 * (C + 1) * tailMass (δ / 2) η < ε / 2 := by
    have := mul_lt_mul_of_pos_left hη (by positivity : 0 < 2 * (C + 1))
    calc 2 * (C + 1) * tailMass (δ / 2) η < 2 * (C + 1) * (ε / (4 * (C + 1))) := this
      _ = ε / 2 := by field_simp; ring
  linarith

/-- Pointwise approximation for a bounded continuous function. -/
theorem tendsto_poissonSmooth {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ t, |f t| ≤ C)
    (t : ℝ) :
    Tendsto (fun η => ∫ x, f (t - x) * poissonKernel η x) (𝓝[>] 0) (𝓝 (f t)) := by
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (l := 𝓝[>] (0 : ℝ)) (F := fun η s => f (t - η * s) * poissonKernel 1 s)
    (f := fun s => f t * poissonKernel 1 s) (fun s => C * poissonKernel 1 s) ?_ ?_
    ((integrable_poissonKernel one_pos).const_mul C) ?_
  · rw [integral_const_mul, integral_poissonKernel one_pos, mul_one] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact (integral_poissonKernel_mul hη (fun x => f (t - x))).symm
  · exact Eventually.of_forall fun η => (integrable_smooth hf hC t η).aestronglyMeasurable
  · refine Eventually.of_forall fun η => Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poissonKernel_nonneg one_pos.le s)]
    exact mul_le_mul_of_nonneg_right (hC _) (poissonKernel_nonneg one_pos.le s)
  · refine Eventually.of_forall fun s => ?_
    refine Tendsto.mul_const _ ?_
    have h0 : Tendsto (fun η : ℝ => t - η * s) (𝓝 0) (𝓝 (t - 0 * s)) :=
      (by fun_prop : Continuous fun η : ℝ => t - η * s).tendsto 0
    simp only [zero_mul, sub_zero] at h0
    exact (hf.tendsto t).comp (h0.mono_left nhdsWithin_le_nhds)

end FroehlichSpencer.Infra
