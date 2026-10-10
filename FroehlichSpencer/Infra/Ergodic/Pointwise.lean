/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Ergodic.LocalErgodic
public import FroehlichSpencer.Infra.Ergodic.Maximal
public import FroehlichSpencer.Infra.Ergodic.Density

/-!
# The pointwise ergodic theorem in `L¹` for cube averages on `ℤ^ν`

For `ν ≥ 1` and an integrable `f` on `(ℤ^ν → ℝ, productMeasure μ)`, the cube averages `A_L f`
converge almost surely to `∫ f`.

The proof approximates `f` in `L¹` by bounded local functions
(`Ergodic/Density.lean`), for which the theorem holds (`Ergodic/LocalErgodic.lean`), and controls
the error by the maximal inequality (`Ergodic/Maximal.lean`).

This is the ergodic input for the
integrated density of states of Fröhlich–Spencer (1983), (1.10), Fröhlich–Spencer (1983).
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace FroehlichSpencer.Infra

variable {ν : ℕ}

private theorem abs_cubeAverage_sub_le_cubeAverage_abs (f g : ((Fin ν → ℤ) → ℝ) → ℝ) (L : ℕ)
    (v : (Fin ν → ℤ) → ℝ) :
    |cubeAverage f L v - cubeAverage g L v| ≤ cubeAverage (fun w => |f w - g w|) L v := by
  have hc : 0 ≤ (((cube ν L).card : ℕ) : ℝ)⁻¹ := by positivity
  unfold cubeAverage
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hc

private theorem measure_bad_le (hν : 0 < ν) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ((Fin ν → ℤ) → ℝ) → ℝ} (hfm : Measurable f) (hf : Integrable f (productMeasure μ))
    {η : ℝ} (hη : 0 < η) {δ : ℝ} (hδ : 0 < δ) (hδη : δ ≤ η / 2) :
    productMeasure μ {v | ∃ᶠ L in atTop,
        2 * η < |cubeAverage f L v - ∫ w, f w ∂productMeasure μ|} ≤
      ENNReal.ofReal (3 ^ ν * δ / η) := by
  obtain ⟨g, M, S, hgm, hgM, hgS, hgd⟩ := exists_local_integral_abs_sub_lt μ hf hδ
  have hgi : Integrable g (productMeasure μ) :=
    Integrable.of_bound hgm.aestronglyMeasurable M (Eventually.of_forall fun v => by
      simpa only [Real.norm_eq_abs] using hgM v)
  have hdi : Integrable (fun w => |f w - g w|) (productMeasure μ) := (hf.sub hgi).abs
  have hmax := measure_exists_lt_cubeAverage_le μ (f := fun w => |f w - g w|)
    (by fun_prop) (fun v => abs_nonneg _) hdi hη
  have hloc := ae_tendsto_cubeAverage_of_local hν μ hgm hgM hgS
  have hint : |∫ w, g w ∂productMeasure μ - ∫ w, f w ∂productMeasure μ| ≤ δ := by
    rw [← integral_sub hgi hf]
    refine (abs_integral_le_integral_abs).trans ?_
    have : ∫ w, |g w - f w| ∂productMeasure μ = ∫ w, |f w - g w| ∂productMeasure μ := by
      congr 1; ext w; exact abs_sub_comm _ _
    linarith only [this, hgd]
  have hsub : {v | ∃ᶠ L in atTop,
        2 * η < |cubeAverage f L v - ∫ w, f w ∂productMeasure μ|} ⊆
      {v | ¬ Tendsto (fun L => cubeAverage g L v) atTop (𝓝 (∫ w, g w ∂productMeasure μ))} ∪
      {v | ∃ L, η < cubeAverage (fun w => |f w - g w|) L v} := by
    intro v hv
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_exists, not_lt] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hev := Metric.tendsto_nhds.1 h1 (η / 2) (by positivity)
    have := (hv.and_eventually hev).exists
    obtain ⟨L, hL1, hL2⟩ := this
    rw [Real.dist_eq] at hL2
    have h3 := abs_cubeAverage_sub_le_cubeAverage_abs f g L v
    have h4 := h2 L
    have h5 : |cubeAverage f L v - ∫ w, f w ∂productMeasure μ| ≤
        |cubeAverage f L v - cubeAverage g L v| +
        |cubeAverage g L v - ∫ w, g w ∂productMeasure μ| +
        |∫ w, g w ∂productMeasure μ - ∫ w, f w ∂productMeasure μ| := by
      have e : cubeAverage f L v - ∫ w, f w ∂productMeasure μ =
          (cubeAverage f L v - cubeAverage g L v) +
          (cubeAverage g L v - ∫ w, g w ∂productMeasure μ) +
          (∫ w, g w ∂productMeasure μ - ∫ w, f w ∂productMeasure μ) := by ring
      rw [e]
      exact abs_add_three _ _ _
    linarith only [hL1, h3, h4, hL2, hint, hδη, h5]
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [(ae_iff.1 hloc), zero_add]
  refine hmax.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [div_le_div_iff_of_pos_right hη]
  have : 0 ≤ (3 : ℝ) ^ ν := by positivity
  exact mul_le_mul_of_nonneg_left hgd.le this |>.trans (by gcongr)

private theorem ae_tendsto_of_measurable (hν : 0 < ν) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ((Fin ν → ℤ) → ℝ) → ℝ} (hfm : Measurable f) (hf : Integrable f (productMeasure μ)) :
    ∀ᵐ v ∂productMeasure μ,
      Tendsto (fun L => cubeAverage f L v) atTop (𝓝 (∫ w, f w ∂productMeasure μ)) := by
  have hn : ∀ n : ℕ, ∀ᵐ v ∂productMeasure μ,
      ¬ ∃ᶠ L in atTop, 2 * (1 / ((n : ℝ) + 1)) <
        |cubeAverage f L v - ∫ w, f w ∂productMeasure μ| := by
    intro n
    rw [ae_iff]
    simp only [not_not]
    have hη : 0 < 1 / ((n : ℝ) + 1) := by positivity
    refine le_antisymm ?_ zero_le
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    rw [zero_add]
    set η := 1 / ((n : ℝ) + 1)
    set δ := min (η / 2) ((ε : ℝ) * η / 3 ^ ν) with hδ
    have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
    refine (measure_bad_le hν μ hfm hf hη hδpos (min_le_left _ _)).trans ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hη]
    have h1 : δ ≤ (ε : ℝ) * η / 3 ^ ν := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    linarith only [h1]
  filter_upwards [ae_all_iff.2 hn] with v hv
  rw [Metric.tendsto_nhds]
  intro e he
  obtain ⟨n, hn'⟩ := exists_nat_one_div_lt (show 0 < e / 2 by positivity)
  have := hv n
  rw [not_frequently] at this
  filter_upwards [this] with L hL
  rw [Real.dist_eq]
  push Not at hL
  linarith only [hL, hn']

/-- **Pointwise ergodic theorem** for cube averages: for `ν ≥ 1` and integrable `f`,
`A_L f → ∫ f` almost surely as `L → ∞`. -/
theorem ae_tendsto_cubeAverage (hν : 0 < ν) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ((Fin ν → ℤ) → ℝ) → ℝ} (hf : Integrable f (productMeasure μ)) :
    ∀ᵐ v ∂productMeasure μ,
      Tendsto (fun L => cubeAverage f L v) atTop (𝓝 (∫ w, f w ∂productMeasure μ)) := by
  set f' := hf.1.mk f with hf'
  have hfm : Measurable f' := hf.1.stronglyMeasurable_mk.measurable
  have hae : f =ᵐ[productMeasure μ] f' := hf.1.ae_eq_mk
  have hi' : Integrable f' (productMeasure μ) := hf.congr hae
  have hint : ∫ w, f w ∂productMeasure μ = ∫ w, f' w ∂productMeasure μ := integral_congr_ae hae
  have hsh : ∀ a : Fin ν → ℤ,
      ∀ᵐ v ∂productMeasure μ, f (latticeShift a v) = f' (latticeShift a v) :=
    fun a => (measurePreserving_latticeShift μ a).quasiMeasurePreserving.ae_eq_comp hae
  filter_upwards [ae_all_iff.2 hsh, ae_tendsto_of_measurable hν μ hfm hi'] with v h1 h2
  rw [hint]
  refine h2.congr fun L => ?_
  unfold cubeAverage
  rw [Finset.sum_congr rfl fun a _ => h1 a]

end FroehlichSpencer.Infra
