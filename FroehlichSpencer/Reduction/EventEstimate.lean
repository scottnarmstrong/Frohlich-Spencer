/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Reduction.GreenAPriori
public import FroehlichSpencer.Surface.KuboIntegrandMeasurable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# One-site Kubo estimate from a Green probability event

This is the integral step in the reduction of Theorem 1.2 to Theorem 1.1,
following (1.24)--(1.27), Fröhlich–Spencer (1983).

On the
good event, the square of the bound in (1.24) has exponent `2m(N-|x|)`;
this is the correction to the factor-two misprint flagged in (1.25).
-/

public section

open MeasureTheory

namespace FroehlichSpencer.Reduction

/-- The event `V_N` from (1.24), for a fixed endpoint. -/
@[expose] def greenDecayEvent (ν : ℕ) (hν : 0 < ν) (E m N : ℝ) (x : Site ν) :
    Set (Configuration ν) :=
  {v | ∀ ε : ℝ, ∀ hε : ε ≠ 0,
    ‖greenFunction ν hν ((E : ℂ) + (ε : ℂ) * Complex.I)
        (by simpa using hε) v 0 x‖ ≤
      Real.exp (m * (N - latticeLength ν x))}

private theorem measure_compl_le_of_probability_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (hμ : IsProbabilityMeasure μ)
    {S : Set Ω} (hS : MeasurableSet S) {q : ℝ} (hq : 0 ≤ q)
    (hprob : ENNReal.ofReal (1 - q) ≤ μ S) : μ Sᶜ ≤ ENNReal.ofReal q := by
  have hμS : μ S ≤ 1 := by
    calc μ S ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := hμ.measure_univ
  have hfinite : μ S ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hμS ENNReal.one_lt_top)
  by_cases hq1 : 1 ≤ q
  · calc
      μ Sᶜ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := hμ.measure_univ
      _ ≤ ENNReal.ofReal q := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq1
  · have hqle : q ≤ 1 := le_of_not_ge hq1
    rw [measure_compl hS hfinite, hμ.measure_univ]
    apply (tsub_le_iff_right).2
    have hsum : ENNReal.ofReal q + ENNReal.ofReal (1 - q) = 1 := by
      rw [← ENNReal.ofReal_add hq (sub_nonneg.mpr hqle)]
      norm_num [add_sub_cancel_right]
    calc
      1 = ENNReal.ofReal q + ENNReal.ofReal (1 - q) := hsum.symm
      _ ≤ ENNReal.ofReal q + μ S := add_le_add le_rfl hprob

/-- If a nonnegative function is bounded separately on a measurable event and
its complement, its integral is bounded by the corresponding two constants. -/
private theorem lintegral_le_event_split
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {S : Set Ω}
    (hS : MeasurableSet S) (f : Ω → ENNReal) (a b : ENNReal)
    (hfS : ∀ ω ∈ S, f ω ≤ a) (hfSc : ∀ ω ∈ Sᶜ, f ω ≤ b) :
    ∫⁻ ω, f ω ∂μ ≤ a * μ S + b * μ Sᶜ := by
  classical
  let g : Ω → ENNReal := S.indicator (fun _ => a) + Sᶜ.indicator (fun _ => b)
  have hfg : ∀ ω, f ω ≤ g ω := by
    intro ω
    by_cases hω : ω ∈ S
    · simpa [g, hω] using hfS ω hω
    · have hωc : ω ∈ Sᶜ := by simpa using hω
      simpa [g, hω, hωc] using hfSc ω hωc
  calc
    ∫⁻ ω, f ω ∂μ ≤ ∫⁻ ω, g ω ∂μ := lintegral_mono hfg
    _ = (∫⁻ ω, S.indicator (fun _ => a) ω ∂μ) +
          ∫⁻ ω, Sᶜ.indicator (fun _ => b) ω ∂μ := by
        change (∫⁻ ω, S.indicator (fun _ => a) ω +
            Sᶜ.indicator (fun _ => b) ω ∂μ) = _
        rw [lintegral_add_left (measurable_const.indicator hS)]
    _ = a * μ S + b * μ Sᶜ := by
        rw [lintegral_indicator_const hS a,
          lintegral_indicator_const hS.compl b]

/-- The Green-function second moment, multiplied by `ε²`, is controlled by the
good-event decay and the exceptional probability. -/
theorem weighted_green_lintegral_le
    (ν : ℕ) (hν : 0 < ν) (law : Measure ℝ) [IsProbabilityMeasure law]
    (E m N K p : ℝ) (hN : 0 < N) (hK : 0 ≤ K)
    (x : Site ν) (ε : {ε : ℝ // ε ≠ 0})
    (hS : MeasurableSet (greenDecayEvent ν hν E m N x))
    (hprob : ENNReal.ofReal (1 - K / Real.rpow N p) ≤
      configurationMeasure ν law (greenDecayEvent ν hν E m N x)) :
    ENNReal.ofReal (ε.1 ^ 2) *
        ∫⁻ v : Configuration ν,
          ENNReal.ofReal
            (‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
              (by simpa using ε.2) v 0 x‖ ^ 2)
          ∂configurationMeasure ν law ≤
      ENNReal.ofReal (ε.1 ^ 2 *
        Real.exp (m * (N - latticeLength ν x)) ^ 2) +
        ENNReal.ofReal (K / Real.rpow N p) := by
  let μ := configurationMeasure ν law
  let S := greenDecayEvent ν hν E m N x
  have hq : 0 ≤ K / Real.rpow N p := by
    exact div_nonneg hK (Real.rpow_nonneg hN.le _)
  have hμprob : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (Measure.infinitePi (fun _ : Site ν => law))
    infer_instance
  have hbad : μ Sᶜ ≤ ENNReal.ofReal (K / Real.rpow N p) := by
    simpa [μ, S] using measure_compl_le_of_probability_lower_bound μ hμprob hS hq hprob
  have hG : ∀ v, ‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
      (by simpa using ε.2) v 0 x‖ ≤ 1 / |ε.1| := by
    intro v
    have hz : (((E : ℂ) + (ε.1 : ℂ) * Complex.I)).im ≠ 0 := by
      simpa using ε.2
    simpa using norm_greenFunction_le ν hν _ hz v 0 x
  let f : Configuration ν → ENNReal := fun v => ENNReal.ofReal
    (‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
      (by simpa using ε.2) v 0 x‖ ^ 2)
  let a : ENNReal := ENNReal.ofReal
    (ε.1 ^ 2 * Real.exp (m * (N - latticeLength ν x)) ^ 2)
  have hsplit : ∀ v, ENNReal.ofReal (ε.1 ^ 2) * f v ≤
      S.indicator (fun _ => a) v + Sᶜ.indicator (fun _ => 1) v := by
    classical
    intro v
    by_cases hv : v ∈ S
    · have hdecay := hv ε.1 ε.2
      have hsq : ‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
          (by simpa using ε.2) v 0 x‖ ^ 2 ≤
          Real.exp (m * (N - latticeLength ν x)) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (Real.exp_nonneg _)).2 hdecay
      rw [Set.indicator_of_mem hv,
        Set.indicator_of_notMem (by simpa using hv), add_zero,
        ← ENNReal.ofReal_mul (sq_nonneg ε.1)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsq (sq_nonneg ε.1))
    · have hv' : v ∈ Sᶜ := (Set.mem_compl_iff S v).mpr hv
      have hbound := hG v
      have htrivial : ε.1 ^ 2 *
          ‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
            (by simpa using ε.2) v 0 x‖ ^ 2 ≤ 1 := by
        have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 1 / |ε.1|)).2 hbound
        rw [div_pow, one_pow, sq_abs] at hsq
        calc
          ε.1 ^ 2 *
              ‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
                (by simpa using ε.2) v 0 x‖ ^ 2 ≤
            ε.1 ^ 2 * (1 / ε.1 ^ 2) := by
              exact mul_le_mul_of_nonneg_left hsq (sq_nonneg ε.1)
          _ = 1 := by field_simp [ε.2]
      rw [Set.indicator_of_notMem hv, Set.indicator_of_mem hv', zero_add,
        ← ENNReal.ofReal_mul (sq_nonneg ε.1)]
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal htrivial
  have hlocal := lintegral_le_event_split μ hS
    (fun v => ENNReal.ofReal (ε.1 ^ 2) * f v) a 1
    (fun v hv => by
      have hvnot : v ∉ Sᶜ := fun h => (Set.mem_compl_iff S v).mp h hv
      have h := hsplit v
      rw [Set.indicator_of_mem hv, Set.indicator_of_notMem hvnot, add_zero] at h
      exact h)
    (fun v hv => by
      have hv' : v ∈ Sᶜ := hv
      have h := hsplit v
      rw [Set.indicator_of_notMem hv, Set.indicator_of_mem hv', zero_add] at h
      exact h)
  have hfmeas : Measurable f := by
    exact measurable_kubo_integrand ν hν E ε x
  have hfactor := lintegral_const_mul (μ := μ) (ENNReal.ofReal (ε.1 ^ 2)) hfmeas
  dsimp only [μ, S, f, a] at hbad hlocal hfactor ⊢
  rw [hfactor] at hlocal
  calc
    ENNReal.ofReal (ε.1 ^ 2) *
        ∫⁻ v : Configuration ν,
          ENNReal.ofReal
            (‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
              (by simpa using ε.2) v 0 x‖ ^ 2)
          ∂configurationMeasure ν law ≤
      a * μ S + 1 * μ Sᶜ := hlocal
    _ ≤ a + ENNReal.ofReal (K / Real.rpow N p) := by
      have hSle : μ S ≤ 1 := by
        calc μ S ≤ μ Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := hμprob.measure_univ
      calc
        a * μ S + 1 * μ Sᶜ ≤ a * 1 + 1 * ENNReal.ofReal (K / Real.rpow N p) :=
          by gcongr
        _ = a + ENNReal.ofReal (K / Real.rpow N p) := by simp

end FroehlichSpencer.Reduction

end
