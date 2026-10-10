/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.ProductMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic

/-!
# Gaussian single-site estimates

Elementary bounds for the centered Gaussian `gaussianReal 0 γ` (`γ` the variance): a density
bound, a small-interval bound away from the origin, a two-sided tail bound, and their transfer to
one coordinate of the product measure.

Motivation: the low-energy Gaussian regime of
Fröhlich–Spencer (1983), transcribed in Fröhlich–Spencer (1983).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FroehlichSpencer.Infra

theorem gaussianPDFReal_zero_le {γ : ℝ≥0} (t : ℝ) :
    gaussianPDFReal 0 γ t ≤ 1 / √(2 * Real.pi * γ) := by
  rw [gaussianPDFReal_def, one_div]
  have h : Real.exp (-(t - 0) ^ 2 / (2 * γ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [sq_nonneg (t - 0)]
    · positivity
  calc (√(2 * Real.pi * γ))⁻¹ * Real.exp (-(t - 0) ^ 2 / (2 * γ))
      ≤ (√(2 * Real.pi * γ))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.2 (Real.sqrt_nonneg _))
    _ = (√(2 * Real.pi * γ))⁻¹ := mul_one _

theorem gaussianPDF_zero_le {γ : ℝ≥0} (t : ℝ) :
    gaussianPDF 0 γ t ≤ ENNReal.ofReal (1 / √(2 * Real.pi * γ)) := by
  rw [gaussianPDF_def]
  exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_zero_le t)

/-- A window of half-width `r` around `a`, at distance `|a| - r ≥ 0` from the origin (for
`r < 0` the window is empty and the bound is `0`). -/
theorem gaussianReal_Icc_le {γ : ℝ≥0} (hγ : γ ≠ 0) {a r : ℝ} (hra : r ≤ |a|) :
    gaussianReal 0 γ (Set.Icc (a - r) (a + r)) ≤
      ENNReal.ofReal (2 * r / √(2 * Real.pi * γ) * Real.exp (-(|a| - r) ^ 2 / (2 * γ))) := by
  rw [gaussianReal_of_var_ne_zero 0 hγ, withDensity_apply _ measurableSet_Icc]
  set c : ℝ := (√(2 * Real.pi * γ))⁻¹ * Real.exp (-(|a| - r) ^ 2 / (2 * γ)) with hc
  have hpt : ∀ t ∈ Set.Icc (a - r) (a + r), gaussianPDF 0 γ t ≤ ENNReal.ofReal c := by
    intro t ht
    rw [gaussianPDF_def, gaussianPDFReal_def]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (Real.sqrt_nonneg _))
    apply Real.exp_le_exp.2
    have h1 : |a| - r ≤ |t| := by
      have := abs_sub_abs_le_abs_sub a t
      have h2 : |a - t| ≤ r := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      linarith
    have h3 : (|a| - r) ^ 2 ≤ (t - 0) ^ 2 := by
      have : (|a| - r) ^ 2 ≤ |t| ^ 2 := by
        apply pow_le_pow_left₀ (by linarith) h1
      simpa [sq_abs] using this
    have h4 : 0 < 2 * (γ : ℝ) := by
      have : (0 : ℝ) < γ := by exact_mod_cast pos_iff_ne_zero.2 hγ
      linarith
    apply div_le_div_of_nonneg_right _ h4.le
    linarith
  calc ∫⁻ t in Set.Icc (a - r) (a + r), gaussianPDF 0 γ t
      ≤ ∫⁻ _ in Set.Icc (a - r) (a + r), ENNReal.ofReal c :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = ENNReal.ofReal c * volume (Set.Icc (a - r) (a + r)) := setLIntegral_const _ _
    _ = ENNReal.ofReal c * ENNReal.ofReal (2 * r) := by
        rw [Real.volume_Icc]; congr 2; ring
    _ = ENNReal.ofReal (2 * r / √(2 * Real.pi * γ) * Real.exp (-(|a| - r) ^ 2 / (2 * γ))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hc]; ring

/-- One-sided Gaussian tail via the Chernoff bound. -/
theorem gaussianReal_le_apply_le {γ : ℝ≥0} (hγ : γ ≠ 0) {R : ℝ} (hR : 0 ≤ R) :
    gaussianReal 0 γ {t | R ≤ t} ≤ ENNReal.ofReal (Real.exp (-R ^ 2 / (2 * γ))) := by
  have hγ' : (0 : ℝ) < γ := by exact_mod_cast pos_iff_ne_zero.2 hγ
  have hint : Integrable (fun ω : ℝ => Real.exp ((R / γ) * id ω)) (gaussianReal 0 γ) := by
    simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := γ) (R / γ)
  have h := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 γ) (X := id) R
    (div_nonneg hR hγ'.le) hint
  rw [mgf_id_gaussianReal] at h
  have e : Real.exp (-(R / γ) * R) * Real.exp (0 * (R / γ) + γ * (R / γ) ^ 2 / 2)
      = Real.exp (-R ^ 2 / (2 * γ)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [e] at h
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal h

/-- Two-sided Gaussian tail. -/
theorem gaussianReal_le_abs_le {γ : ℝ≥0} {R : ℝ} (hR : 0 ≤ R) :
    gaussianReal 0 γ {t | R ≤ |t|} ≤ ENNReal.ofReal (2 * Real.exp (-R ^ 2 / (2 * γ))) := by
  by_cases hγ : γ = 0
  · subst hγ
    calc gaussianReal 0 0 {t | R ≤ |t|} ≤ 1 := by
          rw [gaussianReal_zero_var]; exact prob_le_one
      _ ≤ ENNReal.ofReal (2 * Real.exp (-R ^ 2 / (2 * ((0 : ℝ≥0) : ℝ)))) := by
          rw [← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          have := Real.exp_pos (-R ^ 2 / (2 * ((0 : ℝ≥0) : ℝ)))
          simp
  · have hneg : gaussianReal 0 γ {t | R ≤ -t} = gaussianReal 0 γ {t | R ≤ t} := by
      have h := gaussianReal_map_neg (μ := 0) (v := γ)
      rw [neg_zero] at h
      have hm : MeasurableSet {t : ℝ | R ≤ t} := measurableSet_le measurable_const measurable_id
      have := Measure.map_apply (μ := gaussianReal 0 γ) (f := fun x : ℝ => -x)
        (by fun_prop) hm
      rw [h] at this
      exact this.symm
    have hsub : {t : ℝ | R ≤ |t|} ⊆ {t | R ≤ t} ∪ {t | R ≤ -t} := by
      intro t ht
      have ht' : R ≤ |t| := ht
      rcases le_abs'.1 ht' with h | h
      · right; show R ≤ -t; linarith
      · left; exact h
    calc gaussianReal 0 γ {t | R ≤ |t|}
        ≤ gaussianReal 0 γ ({t | R ≤ t} ∪ {t | R ≤ -t}) := measure_mono hsub
      _ ≤ gaussianReal 0 γ {t | R ≤ t} + gaussianReal 0 γ {t | R ≤ -t} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-R ^ 2 / (2 * γ))) +
            ENNReal.ofReal (Real.exp (-R ^ 2 / (2 * γ))) := by
          rw [hneg]; exact add_le_add (gaussianReal_le_apply_le hγ hR)
            (gaussianReal_le_apply_le hγ hR)
      _ = ENNReal.ofReal (2 * Real.exp (-R ^ 2 / (2 * γ))) := by
          rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
          congr 1; ring

/-- One coordinate of the product measure has law `μ`. -/
theorem productMeasure_setOf_apply_mem {ι : Type*} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x : ι) {s : Set ℝ} (hs : MeasurableSet s) :
    productMeasure μ {v : ι → ℝ | v x ∈ s} = μ s := by
  have h := Measure.infinitePi_map_eval (fun _ : ι => μ) x
  have h2 := Measure.map_apply (μ := Measure.infinitePi (fun _ : ι => μ))
    (measurable_pi_apply x) hs
  rw [h] at h2
  exact h2.symm

theorem productMeasure_gaussianReal_apply_mem_Icc_le {ι : Type*} {γ : ℝ≥0} (hγ : γ ≠ 0)
    (x : ι) {a r : ℝ} (hra : r ≤ |a|) :
    productMeasure (gaussianReal 0 γ) {v : ι → ℝ | v x ∈ Set.Icc (a - r) (a + r)} ≤
      ENNReal.ofReal (2 * r / √(2 * Real.pi * γ) * Real.exp (-(|a| - r) ^ 2 / (2 * γ))) := by
  rw [productMeasure_setOf_apply_mem _ x measurableSet_Icc]
  exact gaussianReal_Icc_le hγ hra

theorem productMeasure_gaussianReal_le_abs_apply_le {ι : Type*} {γ : ℝ≥0} (x : ι) {R : ℝ}
    (hR : 0 ≤ R) :
    productMeasure (gaussianReal 0 γ) {v : ι → ℝ | R ≤ |v x|} ≤
      ENNReal.ofReal (2 * Real.exp (-R ^ 2 / (2 * γ))) := by
  have hm : MeasurableSet {t : ℝ | R ≤ |t|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have := productMeasure_setOf_apply_mem (ι := ι) (gaussianReal 0 γ) x hm
  rw [show {v : ι → ℝ | R ≤ |v x|} = {v : ι → ℝ | v x ∈ {t : ℝ | R ≤ |t|}} from rfl, this]
  exact gaussianReal_le_abs_le hR

end FroehlichSpencer.Infra
