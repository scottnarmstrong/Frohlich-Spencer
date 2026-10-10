/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Moment.SourceEnsembleConstructor

/-!
# Jensen's inequality for a product of cosine factors

For an even probability law `ν`, odd angles and amplitudes `0 ≤ z < 1`, the shifted product
`∏ (1 + z cos(angle − θ))` integrates to at least `exp(−Σ γ(z) θ²)` times the unshifted product.

This is FS82 (2.101) in integral form: the Gibbs tilt by the unshifted density is taken inside the
proof, so the statement mentions only the reference law.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace FroehlichSpencer.FS82.Root.MomentComparisonAssembly

open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.SourceEnsembleConstructor

theorem measurable_ensembleLogShift {I X : Type*} [Fintype I] [MeasurableSpace X]
    (z θ : I → ℝ) (angle : I → X → ℝ) (hangle : ∀ i, Measurable (angle i)) :
    Measurable (SourceJensen.ensembleLogShift z θ angle 1) := by
  unfold SourceJensen.ensembleLogShift SourceJensen.shiftedLogFactor
    SourceJensen.shiftedDenominator
  fun_prop

/-- **Jensen for cosine products (2.101).** -/
theorem cosineProduct_jensen {I X : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace X] [InvolutiveNeg X] [MeasurableNeg X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (hν : Measure.map (fun x : X => -x) ν = ν)
    (z θ : I → ℝ) (angle : I → X → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i < 1)
    (hangle : ∀ i, Measurable (angle i))
    (hodd : ∀ i x, angle i (-x) = -angle i x) :
    Real.exp (-SourceJensen.ensembleJensenBudget z θ) *
        ∫ x, ensembleCosineDensity z angle x ∂ν ≤
      ∫ x, ensembleShiftedCosineDensity z θ angle x ∂ν := by
  classical
  let f : X → ℝ := ensembleCosineLogDensity z angle
  have hfmeas : Measurable f := measurable_ensembleCosineLogDensity z angle hangle
  have hexpf : ∀ x, Real.exp (f x) = ensembleCosineDensity z angle x :=
    fun x => exp_logDensity_eq_cosineDensity z angle hz0 hz1 x
  have hIntExp : Integrable (fun x => Real.exp (f x)) ν := by
    refine Integrable.of_bound (hfmeas.exp).aestronglyMeasurable (∏ i, (1 + z i))
      (ae_of_all ν fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, hexpf]
    exact (sourceDensity_nonneg_le z angle hz0 hz1 x).2
  have hZpos : 0 < ∫ x, Real.exp (f x) ∂ν := integral_exp_pos hIntExp
  have : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hIntExp
  have hEven : Measure.map (fun x : X => -x) (ν.tilted f) = ν.tilted f := by
    have h := tilted_map_invariant (MeasurableEquiv.neg X) ν f
      (by simpa using hν) (fun x => by simp)
      (fun x => by
        change ensembleCosineLogDensity z angle (-x) = ensembleCosineLogDensity z angle x
        unfold ensembleCosineLogDensity
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hodd, Real.cos_neg])
    simpa using h
  have hshiftMeas : Measurable (SourceJensen.ensembleLogShift z θ angle 1) :=
    measurable_ensembleLogShift z θ angle hangle
  have hint : Integrable (SourceJensen.ensembleLogShift z θ angle 1) (ν.tilted f) := by
    refine Integrable.of_bound hshiftMeas.aestronglyMeasurable (∑ i, 2 * logEnvelope (z i))
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    exact ensembleLogShift_abs_bound z θ angle hz0 hz1 x
  have hexp : Integrable
      (fun x => Real.exp (SourceJensen.ensembleLogShift z θ angle 1 x)) (ν.tilted f) := by
    refine Integrable.of_bound (hshiftMeas.exp).aestronglyMeasurable
      (∏ i, ((1 + z i) / (1 - z i))) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact (ensembleLogShift_exp_bound z θ angle hz0 hz1 x).2
  have hJ := SourceJensen.perEnsembleJensen_279 (ν := ν.tilted f) hEven measurable_neg
    z θ angle hz0 hz1 hodd hint hexp
  have hTilt : ∫ x, Real.exp (SourceJensen.ensembleLogShift z θ angle 1 x) ∂(ν.tilted f) =
      (∫ x, ensembleShiftedCosineDensity z θ angle x ∂ν) / ∫ x, Real.exp (f x) ∂ν := by
    rw [integral_tilted]
    have hpt : ∀ x, (Real.exp (f x) / ∫ x, Real.exp (f x) ∂ν) •
        Real.exp (SourceJensen.ensembleLogShift z θ angle 1 x) =
        ensembleShiftedCosineDensity z θ angle x / ∫ x, Real.exp (f x) ∂ν := by
      intro x
      rw [smul_eq_mul, div_mul_eq_mul_div, ← Real.exp_add,
        exp_logDensity_add_shift_eq_shiftedDensity z θ angle hz0 hz1 x]
    simp_rw [hpt]
    rw [integral_div]
  have hZ : ∫ x, ensembleCosineDensity z angle x ∂ν = ∫ x, Real.exp (f x) ∂ν :=
    integral_congr_ae (ae_of_all ν fun x => (hexpf x).symm)
  rw [hTilt, le_div_iff₀ hZpos] at hJ
  rw [hZ]
  exact hJ

end FroehlichSpencer.FS82.Root.MomentComparisonAssembly

end
