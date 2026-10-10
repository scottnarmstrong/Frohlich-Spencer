/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import FroehlichSpencer.FS82.Currents.Current
public import FroehlichSpencer.FS82.Gaussian.LatticePath
public import FroehlichSpencer.FS82.Cubical.UnitBox
public import Mathlib.Data.Finsupp.Basic
public import FroehlichSpencer.FS82.Currents.ActivityRate

public import FroehlichSpencer.FS82.Moment.SourceConstructor
public import FroehlichSpencer.FS82.Gaussian.LatticeComplex
public import FroehlichSpencer.FS82.Moment.CurrentDecay
public import FroehlichSpencer.FS82.Moment.SourceCoercivity
public import FroehlichSpencer.FS82.Currents.SourceLatticeChain
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.CategoryTheory.Types.Basic

/-!
# FS82 source ensemble Jensen law

For a finite source ensemble, the probability law is the normalized product
of its cosine factors against the centered lattice Gaussian lifted to link
coordinates.

The lift pushes forward to quotient Gaussian.

The source
activity and coercivity inequalities prove the strict one-factor bound needed
for the logarithmic Jensen argument.
-/

@[expose] public section

set_option linter.style.haveILetI false

open scoped BigOperators
open MeasureTheory

namespace FroehlichSpencer.FS82.Moment.SourceEnsembleConstructor

open FroehlichSpencer.FS82
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Moment.SourceJensen

variable {B : Box 4}


/-- Finite product of the source cosine factors. -/
noncomputable def ensembleCosineDensity {I X : Type*} [Fintype I] [DecidableEq I]
    (z : I → ℝ) (angle : I → X → ℝ) (φ : X) : ℝ :=
  (Finset.univ : Finset I).prod fun i => 1 + z i * Real.cos (angle i φ)

/-- The source shifted product in (2.98). -/
noncomputable def ensembleShiftedCosineDensity {I X : Type*} [Fintype I] [DecidableEq I]
    (z θ : I → ℝ) (angle : I → X → ℝ) (φ : X) : ℝ :=
  (Finset.univ : Finset I).prod fun i => 1 + z i * Real.cos (angle i φ - θ i)

/-- Logarithm of the zero-shift source density. -/
noncomputable def ensembleCosineLogDensity {I X : Type*} [Fintype I] [DecidableEq I]
    (z : I → ℝ) (angle : I → X → ℝ) (φ : X) : ℝ :=
  (Finset.univ : Finset I).sum fun i => Real.log (1 + z i * Real.cos (angle i φ))

/-- Log shift is exactly the logarithm of the source product ratio. -/
theorem exp_logDensity_eq_cosineDensity {I X : Type*} [Fintype I] [DecidableEq I]
    (z : I → ℝ) (angle : I → X → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i < 1) (φ : X) :
    Real.exp (ensembleCosineLogDensity z angle φ) =
      ensembleCosineDensity z angle φ := by
  rw [ensembleCosineLogDensity, Real.exp_sum]
  unfold ensembleCosineDensity
  apply Finset.prod_congr rfl
  intro i hi
  rw [Real.exp_log (by
    have hcos := Real.neg_one_le_cos (angle i φ)
    have h := mul_le_mul_of_nonneg_left hcos (hz0 i)
    nlinarith [hz1 i])]

theorem exp_logDensity_add_shift_eq_shiftedDensity {I X : Type*} [Fintype I] [DecidableEq I]
    (z θ : I → ℝ) (angle : I → X → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i < 1) (φ : X) :
    Real.exp (ensembleCosineLogDensity z angle φ +
        SourceJensen.ensembleLogShift z θ angle 1 φ) =
      ensembleShiftedCosineDensity z θ angle φ := by
  have hsum : ensembleCosineLogDensity z angle φ +
      SourceJensen.ensembleLogShift z θ angle 1 φ =
      (Finset.univ : Finset I).sum fun i => Real.log (1 + z i * Real.cos (angle i φ - θ i)) := by
    unfold ensembleCosineLogDensity SourceJensen.ensembleLogShift
      SourceJensen.shiftedLogFactor SourceJensen.shiftedDenominator
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp
  rw [hsum, Real.exp_sum]
  unfold ensembleShiftedCosineDensity
  apply Finset.prod_congr rfl
  intro i hi
  rw [Real.exp_log (by
    have hcos := Real.neg_one_le_cos (angle i φ - θ i)
    have h := mul_le_mul_of_nonneg_left hcos (hz0 i)
    nlinarith [hz1 i])]

/-- Reusable change-of-sign lemma for a Gibbs tilt by an even density. -/
theorem tilted_map_invariant {V : Type*} [MeasurableSpace V]
    (e : V ≃ᵐ V) (μ : Measure V) (f : V → ℝ)
    (hmap : μ.map e = μ) (hinv : ∀ x, e (e x) = x)
    (hEven : ∀ x, f (e x) = f x) :
    Measure.map e (μ.tilted f) = μ.tilted f := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply e.measurable hs, tilted_apply' _ _ (e.measurable hs),
    tilted_apply' _ _ hs]
  rw [← lintegral_indicator (e.measurable hs), ← lintegral_indicator hs]
  calc
    ∫⁻ x, (e ⁻¹' s).indicator
        (fun y => ENNReal.ofReal
          (Real.exp (f y) / ∫ x, Real.exp (f x) ∂μ)) x ∂μ
      = ∫⁻ x, (e ⁻¹' s).indicator
        (fun y => ENNReal.ofReal
          (Real.exp (f y) / ∫ x, Real.exp (f x) ∂μ)) x ∂(μ.map e) := by rw [hmap]
    _ = ∫⁻ x, (e ⁻¹' s).indicator
        (fun y => ENNReal.ofReal
          (Real.exp (f y) / ∫ x, Real.exp (f x) ∂μ)) (e x) ∂μ := by
          rw [lintegral_map_equiv]
    _ = ∫⁻ x, s.indicator
        (fun y => ENNReal.ofReal
          (Real.exp (f y) / ∫ x, Real.exp (f x) ∂μ)) x ∂μ := by
          congr 1
          funext x
          by_cases hx : x ∈ s <;> simp [hinv x, hEven x, hx]


-- Replaces the removed raw `sourceJensenAngle`; the cosine law uses this C2 pairing.


/-- Log-density measurability follows from continuity of each finite current
phase and the positivity of every cosine factor. -/
theorem measurable_ensembleCosineLogDensity {I X : Type*}
    [Fintype I] [DecidableEq I] [MeasurableSpace X]
    (z : I → ℝ) (angle : I → X → ℝ)
    (hangle : ∀ i, Measurable (angle i)) :
    Measurable (ensembleCosineLogDensity z angle) := by
  unfold ensembleCosineLogDensity
  fun_prop

private theorem shiftedDenominator_bounds {z a θ t : ℝ}
    (hz0 : 0 ≤ z) (_hz1 : z < 1) :
    1 - z ≤ SourceJensen.shiftedDenominator z a θ t ∧
      SourceJensen.shiftedDenominator z a θ t ≤ 1 + z := by
  have hcosLo := Real.neg_one_le_cos (a - t * θ)
  have hcosHi := Real.cos_le_one (a - t * θ)
  unfold SourceJensen.shiftedDenominator
  constructor <;> nlinarith

noncomputable def logEnvelope (z : ℝ) : ℝ :=
  |Real.log (1 - z)| + |Real.log (1 + z)|

private theorem abs_log_shiftedDenominator_le {z a θ t : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    |Real.log (SourceJensen.shiftedDenominator z a θ t)| ≤ logEnvelope z := by
  have hlow : 0 < 1 - z := by linarith
  have hhigh : 0 < 1 + z := by linarith
  have hden : 0 < SourceJensen.shiftedDenominator z a θ t :=
    SourceJensen.shiftedDenominator_pos hz0 hz1
  have hb := shiftedDenominator_bounds (z := z) (a := a) (θ := θ) (t := t) hz0 hz1
  have hlo : Real.log (1 - z) ≤
      Real.log (SourceJensen.shiftedDenominator z a θ t) :=
    Real.log_le_log hlow hb.1
  have hhi : Real.log (SourceJensen.shiftedDenominator z a θ t) ≤
      Real.log (1 + z) := Real.log_le_log hden hb.2
  rw [abs_le]
  constructor
  · dsimp [logEnvelope]
    have hleft : -|Real.log (1 - z)| ≤ Real.log (1 - z) := neg_abs_le _
    have hnonpos : -|Real.log (1 + z)| ≤ 0 := neg_nonpos.mpr (abs_nonneg _)
    linarith
  · dsimp [logEnvelope]
    have hright : Real.log (1 + z) ≤ |Real.log (1 + z)| := le_abs_self _
    have hnonneg : 0 ≤ |Real.log (1 - z)| := abs_nonneg _
    linarith

private theorem shiftedFactorRatio_le {z a θ : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    SourceJensen.shiftedDenominator z a θ 1 /
      SourceJensen.shiftedDenominator z a θ 0 ≤ (1 + z) / (1 - z) := by
  have hzDen : 0 < 1 - z := by linarith
  have hden0 : 0 < SourceJensen.shiftedDenominator z a θ 0 :=
    SourceJensen.shiftedDenominator_pos hz0 hz1
  have hbounds1 := shiftedDenominator_bounds (z := z) (a := a) (θ := θ) (t := 1) hz0 hz1
  have hbounds0 := shiftedDenominator_bounds (z := z) (a := a) (θ := θ) (t := 0) hz0 hz1
  rw [div_le_div_iff₀ hden0 hzDen]
  have hnum := hbounds1.2
  have hden := hbounds0.1
  have hpos : 0 ≤ 1 + z := by linarith
  nlinarith

theorem sourceDensity_nonneg_le {I X : Type*} [Fintype I] [DecidableEq I]
    (z : I → ℝ) (angle : I → X → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i < 1) (φ : X) :
    0 ≤ ensembleCosineDensity z angle φ ∧
      ensembleCosineDensity z angle φ ≤ ∏ i, (1 + z i) := by
  unfold ensembleCosineDensity
  constructor
  · apply Finset.prod_nonneg
    intro i hi
    have hc := Real.neg_one_le_cos (angle i φ)
    have h := mul_le_mul_of_nonneg_left hc (hz0 i)
    nlinarith [hz1 i, h]
  · apply Finset.prod_le_prod₀
    · intro i hi
      have hc := Real.neg_one_le_cos (angle i φ)
      have h := mul_le_mul_of_nonneg_left hc (hz0 i)
      nlinarith [hz1 i, h]
    · intro i hi
      have hc := Real.cos_le_one (angle i φ)
      have h := mul_le_mul_of_nonneg_left hc (hz0 i)
      nlinarith

private theorem sourceDensity_pos {I X : Type*} [Fintype I] [DecidableEq I]
    (z : I → ℝ) (angle : I → X → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i < 1) (φ : X) :
    0 < ensembleCosineDensity z angle φ := by
  unfold ensembleCosineDensity
  apply Finset.prod_pos
  intro i hi
  have hc := Real.neg_one_le_cos (angle i φ)
  have h := mul_le_mul_of_nonneg_left hc (hz0 i)
  nlinarith [hz1 i]

theorem ensembleLogShift_abs_bound {I X : Type*} [Fintype I] [DecidableEq I]
    (z θ : I → ℝ) (angle : I → X → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i < 1) (φ : X) :
    |SourceJensen.ensembleLogShift z θ angle 1 φ| ≤
      ∑ i, 2 * logEnvelope (z i) := by
  unfold SourceJensen.ensembleLogShift SourceJensen.shiftedLogFactor
  calc
    |∑ i, (Real.log (SourceJensen.shiftedDenominator (z i)
        (angle i φ) (θ i) 1) - Real.log (SourceJensen.shiftedDenominator
        (z i) (angle i φ) (θ i) 0))| ≤
      ∑ i, |Real.log (SourceJensen.shiftedDenominator (z i)
        (angle i φ) (θ i) 1) - Real.log (SourceJensen.shiftedDenominator
        (z i) (angle i φ) (θ i) 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (2 * logEnvelope (z i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have h1 := abs_log_shiftedDenominator_le (hz0 i) (hz1 i)
        (a := angle i φ) (θ := θ i) (t := 1)
      have h0 := abs_log_shiftedDenominator_le (hz0 i) (hz1 i)
        (a := angle i φ) (θ := θ i) (t := 0)
      calc
        _ ≤ |Real.log (SourceJensen.shiftedDenominator (z i)
            (angle i φ) (θ i) 1)| +
              |Real.log (SourceJensen.shiftedDenominator (z i)
            (angle i φ) (θ i) 0)| := abs_sub _ _
        _ ≤ logEnvelope (z i) + logEnvelope (z i) := add_le_add h1 h0
        _ = 2 * logEnvelope (z i) := by ring

theorem ensembleLogShift_exp_bound {I X : Type*} [Fintype I] [DecidableEq I]
    (z θ : I → ℝ) (angle : I → X → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i < 1) (φ : X) :
    0 ≤ Real.exp (SourceJensen.ensembleLogShift z θ angle 1 φ) ∧
      Real.exp (SourceJensen.ensembleLogShift z θ angle 1 φ) ≤
        ∏ i, ((1 + z i) / (1 - z i)) := by
  rw [SourceJensen.exp_ensembleLogShift_eq_factorRatio z θ angle hz0 hz1 φ]
  constructor
  · apply Finset.prod_nonneg
    intro i hi
    exact div_nonneg
      (le_of_lt (SourceJensen.shiftedDenominator_pos (hz0 i) (hz1 i)))
      (le_of_lt (SourceJensen.shiftedDenominator_pos (hz0 i) (hz1 i)))
  · apply Finset.prod_le_prod₀
    · intro i hi
      exact div_nonneg
        (le_of_lt (SourceJensen.shiftedDenominator_pos (hz0 i) (hz1 i)))
        (le_of_lt (SourceJensen.shiftedDenominator_pos (hz0 i) (hz1 i)))
    · intro i hi
      exact shiftedFactorRatio_le (hz0 i) (hz1 i)


end FroehlichSpencer.FS82.Moment.SourceEnsembleConstructor
end
