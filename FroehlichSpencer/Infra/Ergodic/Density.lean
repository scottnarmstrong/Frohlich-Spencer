/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Ergodic.Basic
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent

/-!
# Local bounded functions are dense in `L¹` of the product measure

Every integrable function on `(ℤ^ν → ℝ, productMeasure μ)` is approximated in `L¹` by bounded
measurable functions depending on finitely many coordinates.

This is the density input for the
`L¹` ergodic theorem behind the integrated density of states of Fröhlich–Spencer (1983), (1.10),
Fröhlich–Spencer (1983); nothing here is model specific.
-/

@[expose] public section

open MeasureTheory
open scoped symmDiff

namespace FroehlichSpencer.Infra

variable {ν : ℕ}

/-- `f` is `ε`-approximable in `L¹` by a bounded measurable local function. -/
private def LocallyApprox (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ((Fin ν → ℤ) → ℝ) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (g : ((Fin ν → ℤ) → ℝ) → ℝ) (M : ℝ) (S : Finset (Fin ν → ℤ)),
      Measurable g ∧ (∀ v, |g v| ≤ M) ∧
      (∀ v w : (Fin ν → ℤ) → ℝ, (∀ x ∈ S, v x = w x) → g v = g w) ∧
      ∫ v, |f v - g v| ∂productMeasure μ < ε

private lemma integrable_of_bounded (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {g : ((Fin ν → ℤ) → ℝ) → ℝ} {M : ℝ} (hg : Measurable g) (hM : ∀ v, |g v| ≤ M) :
    Integrable g (productMeasure μ) :=
  Integrable.of_bound hg.aestronglyMeasurable M (Filter.Eventually.of_forall fun v => by
    simpa only [Real.norm_eq_abs] using hM v)

private lemma integral_abs_sub_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f g h : ((Fin ν → ℤ) → ℝ) → ℝ} (hf : Integrable f (productMeasure μ))
    (hg : Integrable g (productMeasure μ)) (hh : Integrable h (productMeasure μ)) :
    ∫ v, |f v - h v| ∂productMeasure μ ≤
      ∫ v, |f v - g v| ∂productMeasure μ + ∫ v, |g v - h v| ∂productMeasure μ := by
  calc ∫ v, |f v - h v| ∂productMeasure μ
      ≤ ∫ v, (|f v - g v| + |g v - h v|) ∂productMeasure μ :=
        integral_mono (hf.sub hh).abs ((hf.sub hg).abs.add (hg.sub hh).abs)
          fun v => abs_sub_le (f v) (g v) (h v)
    _ = _ := integral_add (hf.sub hg).abs (hg.sub hh).abs

private lemma locallyApprox_indicator (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ)
    {A : Set ((Fin ν → ℤ) → ℝ)} (hA : MeasurableSet A) :
    LocallyApprox μ (A.indicator fun _ => c) := by
  intro ε hε
  have hδ : (0 : ENNReal) < ENNReal.ofReal (ε / (|c| + 1)) :=
    ENNReal.ofReal_pos.2 (div_pos hε (by positivity))
  obtain ⟨C, hC, hCA⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (μ := productMeasure μ) (isSetRing_measurableCylinders (α := fun _ : Fin ν → ℤ => ℝ))
    ⟨{Set.univ}, by simp,
      by simpa using univ_mem_measurableCylinders (fun _ : Fin ν → ℤ => ℝ), by simp⟩
    (generateFrom_measurableCylinders (α := fun _ : Fin ν → ℤ => ℝ)).symm hA hδ
  obtain ⟨s, T, hT, rfl⟩ := (mem_measurableCylinders (α := fun _ : Fin ν → ℤ => ℝ) C).1 hC
  refine ⟨(cylinder s T).indicator fun _ => c, |c|, s, ?_, ?_, ?_, ?_⟩
  · exact measurable_const.indicator (MeasurableSet.cylinder (α := fun _ : Fin ν → ℤ => ℝ) s hT)
  · intro v
    by_cases h : v ∈ cylinder s T <;> simp [h]
  · exact fun v w hvw => dependsOn_cylinder_indicator_const T c hvw
  · have hCm : MeasurableSet (cylinder s T) :=
      MeasurableSet.cylinder (α := fun _ : Fin ν → ℤ => ℝ) s hT
    have key : ∫ v, |A.indicator (fun _ => c) v - (cylinder s T).indicator (fun _ => c) v|
          ∂productMeasure μ = |c| * (productMeasure μ (cylinder s T ∆ A)).toReal := by
      have : (fun v => |A.indicator (fun _ => c) v - (cylinder s T).indicator (fun _ => c) v|) =
          (cylinder s T ∆ A).indicator fun _ => |c| := by
        ext v
        by_cases h1 : v ∈ A <;> by_cases h2 : v ∈ cylinder s T <;>
          simp [h1, h2, Set.indicator, Set.mem_symmDiff]
      rw [this, integral_indicator_const _ (hCm.symmDiff hA)]
      simp [Measure.real, mul_comm]
    rw [key]
    have h1 : (productMeasure μ (cylinder s T ∆ A)).toReal < ε / (|c| + 1) := by
      have := ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top hCA
      rwa [ENNReal.toReal_ofReal (div_pos hε (by positivity)).le] at this
    calc |c| * (productMeasure μ (cylinder s T ∆ A)).toReal
        ≤ (|c| + 1) * (productMeasure μ (cylinder s T ∆ A)).toReal := by
          gcongr; linarith
      _ < (|c| + 1) * (ε / (|c| + 1)) := by
          gcongr
      _ = ε := by field_simp

private lemma locallyApprox_add (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f g : ((Fin ν → ℤ) → ℝ) → ℝ} (hf : Integrable f (productMeasure μ))
    (hg : Integrable g (productMeasure μ)) (h1 : LocallyApprox μ f) (h2 : LocallyApprox μ g) :
    LocallyApprox μ (f + g) := by
  intro ε hε
  obtain ⟨f', M, S, hm, hb, hl, hi⟩ := h1 (ε / 2) (by positivity)
  obtain ⟨g', M', S', hm', hb', hl', hi'⟩ := h2 (ε / 2) (by positivity)
  classical
  refine ⟨f' + g', M + M', S ∪ S', hm.add hm', fun v => ?_, fun v w hvw => ?_, ?_⟩
  · exact (abs_add_le _ _).trans (add_le_add (hb v) (hb' v))
  · simp only [Pi.add_apply]
    rw [hl v w fun x hx => hvw x (Finset.mem_union_left _ hx),
      hl' v w fun x hx => hvw x (Finset.mem_union_right _ hx)]
  · have if' := integrable_of_bounded μ hm hb
    have ig' := integrable_of_bounded μ hm' hb'
    have e1 : ∫ v, |(f + g) v - (f + g') v| ∂productMeasure μ =
        ∫ v, |g v - g' v| ∂productMeasure μ := by
      congr 1; ext v; simp
    have e2 : ∫ v, |(f + g') v - (f' + g') v| ∂productMeasure μ =
        ∫ v, |f v - f' v| ∂productMeasure μ := by
      congr 1; ext v; simp
    have hle := integral_abs_sub_le μ (hf.add hg) (hf.add ig') (if'.add ig')
    rw [e1, e2] at hle
    linarith

/-- Every integrable function on `(ℤ^ν → ℝ, productMeasure μ)` is approximated in `L¹` by a
bounded measurable function depending on finitely many coordinates. -/
theorem exists_local_integral_abs_sub_lt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ((Fin ν → ℤ) → ℝ) → ℝ} (hf : Integrable f (productMeasure μ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : ((Fin ν → ℤ) → ℝ) → ℝ) (M : ℝ) (S : Finset (Fin ν → ℤ)),
      Measurable g ∧ (∀ v, |g v| ≤ M) ∧
      (∀ v w : (Fin ν → ℤ) → ℝ, (∀ x ∈ S, v x = w x) → g v = g w) ∧
      ∫ v, |f v - g v| ∂productMeasure μ < ε := by
  have main : LocallyApprox μ f := by
    refine Integrable.induction (μ := productMeasure μ) (LocallyApprox μ)
      (fun c _ hs _ => locallyApprox_indicator μ c hs)
      (fun _ _ hdisj hf hg => locallyApprox_add μ hf hg) ?_ ?_ hf
    · refine isClosed_of_closure_subset fun F hF => ?_
      rw [Metric.mem_closure_iff] at hF
      intro e he
      obtain ⟨G, hG, hd⟩ := hF (e / 2) (by positivity)
      obtain ⟨g', M, S, hm, hb, hl, hi⟩ := hG (e / 2) (by positivity)
      refine ⟨g', M, S, hm, hb, hl, ?_⟩
      have hFi : Integrable (F : ((Fin ν → ℤ) → ℝ) → ℝ) (productMeasure μ) :=
        L1.integrable_coeFn F
      have hGi : Integrable (G : ((Fin ν → ℤ) → ℝ) → ℝ) (productMeasure μ) :=
        L1.integrable_coeFn G
      have hdist : ∫ v, |F v - G v| ∂productMeasure μ < e / 2 := by
        rw [dist_eq_norm, L1.norm_eq_integral_norm] at hd
        refine lt_of_eq_of_lt (integral_congr_ae ?_) hd
        filter_upwards [Lp.coeFn_sub F G] with v hv
        rw [hv, Real.norm_eq_abs]
        rfl
      have := integral_abs_sub_le μ hFi hGi
        (integrable_of_bounded μ hm hb)
      linarith
    · intro f g hfg hfi hP e he
      obtain ⟨g', M, S, hm, hb, hl, hi⟩ := hP e he
      refine ⟨g', M, S, hm, hb, hl, ?_⟩
      rwa [integral_congr_ae (g := fun v => |f v - g' v|)]
      filter_upwards [hfg] with v hv using by simp [hv]
  exact main ε hε

end FroehlichSpencer.Infra
