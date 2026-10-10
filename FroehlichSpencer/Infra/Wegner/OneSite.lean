/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.ProductMeasure

/-!
# One-dimensional and one-site spectral averaging

The two analytic steps of Wegner's argument (Fröhlich–Spencer (1983), Appendix C,
(C.2)–(C.4), Fröhlich–Spencer (1983)), for an abstract integer-valued function: if an
antitone `ℕ`-valued function drops by at most one in total, its drop over a shift by `s`
integrates to at most `ρ s` against a measure with density bounded by `ρ`, and the same holds
for one coordinate of a product measure.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FroehlichSpencer.Infra

/-- One-dimensional spectral averaging. -/
theorem lintegral_natSub_comp_add_le {μ : Measure ℝ} {g : ℝ → ℝ≥0∞} {ρ : ℝ≥0∞}
    (hμ : μ = volume.withDensity g) (hg : ∀ᵐ t ∂(volume : Measure ℝ), g t ≤ ρ)
    {f : ℝ → ℕ} (hf : Antitone f) (hjump : ∀ s t, f s ≤ f t + 1) (s : ℝ) :
    ∫⁻ t, ((f t - f (t + s) : ℕ) : ℝ≥0∞) ∂μ ≤ ρ * ENNReal.ofReal s := by
  set D : Set ℝ := {t | f (t + s) < f t} with hD
  have hdiam : ∀ t ∈ D, ∀ t' ∈ D, t' ≤ t + s := by
    intro t ht t' ht'
    by_contra hlt
    push Not at hlt
    have h1 : f t' ≤ f (t + s) := hf hlt.le
    have h2 := hjump t (t' + s)
    have ht : f (t + s) < f t := ht
    have ht' : f (t' + s) < f t' := ht'
    omega
  have hsub : ∃ c : ℝ, D ⊆ Set.Icc c (c + s) := by
    by_cases hne : D.Nonempty
    · refine ⟨sInf D, fun t ht => ⟨?_, ?_⟩⟩
      · obtain ⟨t0, ht0⟩ := hne
        exact csInf_le ⟨t0 - s, fun u hu => by linarith [hdiam u hu t0 ht0]⟩ ht
      · have : t - s ≤ sInf D :=
          le_csInf ⟨t, ht⟩ (fun u hu => by linarith [hdiam u hu t ht])
        linarith
    · exact ⟨0, by rw [Set.not_nonempty_iff_eq_empty.mp hne]; exact Set.empty_subset _⟩
  obtain ⟨c, hc⟩ := hsub
  calc ∫⁻ t, ((f t - f (t + s) : ℕ) : ℝ≥0∞) ∂μ
      ≤ ∫⁻ t, (Set.Icc c (c + s)).indicator 1 t ∂μ := by
        refine lintegral_mono fun t => ?_
        by_cases ht : t ∈ D
        · rw [Set.indicator_of_mem (hc ht)]
          have h := hjump t (t + s)
          have : f t - f (t + s) ≤ 1 := by omega
          show _ ≤ (1 : ℝ≥0∞)
          exact_mod_cast this
        · have ht' : ¬ f (t + s) < f t := ht
          have : f t - f (t + s) = 0 := by omega
          simp [this]
    _ = μ (Set.Icc c (c + s)) := lintegral_indicator_one measurableSet_Icc
    _ ≤ ρ * ENNReal.ofReal (c + s - c) := measure_Icc_le_boundedDensity μ hμ hg c (c + s)
    _ = ρ * ENNReal.ofReal s := by rw [add_sub_cancel_left]

/-- One-site spectral averaging under the product measure. -/
theorem lintegral_natSub_update_add_le {ι : Type*} [DecidableEq ι] (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {g : ℝ → ℝ≥0∞} {ρ : ℝ≥0∞}
    (hμ : μ = volume.withDensity g) (hg : ∀ᵐ t ∂(volume : Measure ℝ), g t ≤ ρ)
    {F : (ι → ℝ) → ℕ} (hF : Measurable F) (x : ι)
    (hmono : ∀ v, Antitone fun t => F (Function.update v x t))
    (hjump : ∀ v t t', F (Function.update v x t) ≤ F (Function.update v x t') + 1)
    (s : ℝ) :
    ∫⁻ v, ((F v - F (Function.update v x (v x + s)) : ℕ) : ℝ≥0∞) ∂productMeasure μ ≤
      ρ * ENNReal.ofReal s := by
  have hshift : Measurable fun v : ι → ℝ => Function.update v x (v x + s) :=
    measurable_pi_iff.2 fun i => by
      by_cases hi : i = x
      · subst hi
        simp only [Function.update_self]
        exact (measurable_pi_apply i : Measurable fun v : ι → ℝ => v i).add_const s
      · simp only [Function.update_of_ne hi]
        exact measurable_pi_apply i
  have hmeas :
      Measurable fun v : ι → ℝ => ((F v - F (Function.update v x (v x + s)) : ℕ) : ℝ≥0∞) :=
    ((measurable_from_prod_countable_right (f := fun p : ℕ × ℕ => ((p.1 - p.2 : ℕ) : ℝ≥0∞))
      (fun _ => measurable_of_countable _)).comp (hF.prodMk (hF.comp hshift)) :)
  rw [lintegral_productMeasure_update μ x hmeas]
  calc ∫⁻ v, ∫⁻ t, ((F (Function.update v x t) -
          F (Function.update (Function.update v x t) x (Function.update v x t x + s)) : ℕ) :
            ℝ≥0∞) ∂μ ∂productMeasure (ι := ι) μ
      ≤ ∫⁻ _v, ρ * ENNReal.ofReal s ∂productMeasure (ι := ι) μ := by
        refine lintegral_mono fun v => ?_
        have := lintegral_natSub_comp_add_le hμ hg (hmono v) (hjump v) s
        simpa only [Function.update_idem, Function.update_self] using this
    _ = ρ * ENNReal.ofReal s := by simp

end FroehlichSpencer.Infra
