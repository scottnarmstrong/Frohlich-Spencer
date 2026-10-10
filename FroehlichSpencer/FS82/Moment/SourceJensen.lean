/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Moment.Packing
public import FroehlichSpencer.BKT.SOS.Repair.Ensemble
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Convex.Integral

/-!
# FS82 source Jensen estimate and A0.1 weighted mixture

The logarithmic cosine curvature estimate is proved for every symmetric
probability measure, then aggregated with the corrected source weights
`d_γ Z_γ / Ξ`.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory
open Filter

namespace FroehlichSpencer.FS82.Moment.SourceJensen

noncomputable def sourceJensenGamma (z : ℝ) : ℝ := z / (2 * (1 - z)) + 2 * z ^ 2 / (1 - z) ^ 2

theorem integral_exp_ge_exp_integral_even {X : Type*} [MeasurableSpace X] [Neg X]
    {μ : Measure X} [IsProbabilityMeasure μ]
    (hμ : Measure.map (fun x : X => -x) μ = μ)
    (hneg : Measurable (fun x : X => -x))
    {W : X → ℝ} (hW : Integrable W μ)
    (hexp : Integrable (fun x => Real.exp (W x)) μ) :
    Real.exp (∫ x, (W x + W (-x)) / 2 ∂μ) ≤ ∫ x, Real.exp (W x) ∂μ := by
  have hnegMeas : AEMeasurable (fun x : X => -x) μ := hneg.aemeasurable
  have hWmap : Integrable W (μ.map (fun x : X => -x)) := by rw [hμ]; exact hW
  have hWneg : Integrable (fun x => W (-x)) μ := hWmap.comp_aemeasurable hnegMeas
  have hintNeg : ∫ x, W (-x) ∂μ = ∫ x, W x ∂μ := by
    rw [← integral_map hnegMeas (by rw [hμ]; exact hW.aestronglyMeasurable), hμ]
  have heven : ∫ x, (W x + W (-x)) / 2 ∂μ = ∫ x, W x ∂μ := by
    rw [integral_div, integral_add hW hWneg, hintNeg]
    ring
  rw [heven]
  exact (convexOn_exp).map_integral_le Real.continuous_exp.continuousOn
    isClosed_univ (Eventually.of_forall fun _ => Set.mem_univ _) hW hexp

theorem exp_neg_half_le_integral_exp {X : Type*} [MeasurableSpace X] [Neg X]
    {μ : Measure X} [IsProbabilityMeasure μ]
    (hμ : Measure.map (fun x : X => -x) μ = μ)
    (hneg : Measurable (fun x : X => -x))
    {W W' W'' : ℝ → X → ℝ} {B : ℝ}
    (h0 : ∀ x, W 0 x = 0) (hsymm : ∀ t x, W t (-x) = W (-t) x)
    (hd : ∀ x s, |s| ≤ 1 → HasDerivAt (fun t => W t x) (W' s x) s)
    (hd' : ∀ x s, |s| ≤ 1 → HasDerivAt (fun t => W' t x) (W'' s x) s)
    (hB : ∀ x s, |s| ≤ 1 → |W'' s x| ≤ B)
    (hint : Integrable (W 1) μ)
    (hexp : Integrable (fun x => Real.exp (W 1 x)) μ) :
    Real.exp (-(B / 2)) ≤ ∫ x, Real.exp (W 1 x) ∂μ := by
  refine le_trans ?_ (integral_exp_ge_exp_integral_even hμ hneg hint hexp)
  apply Real.exp_le_exp.mpr
  have hpt : ∀ x, -(B / 2) ≤ (W 1 x + W 1 (-x)) / 2 := by
    intro x
    have h := FroehlichSpencer.BKT.SOS.Repair.add_neg_sub_two_mul_ge
      (g := fun t => W t x) (g' := fun t => W' t x)
      (g'' := fun t => W'' t x) (t := 1)
      (fun s hs => hd x s (by simpa using hs))
      (fun s hs => hd' x s (by simpa using hs))
      (fun s hs => hB x s (by simpa using hs))
    simp only [one_pow, mul_one, h0 x, mul_zero, sub_zero] at h
    rw [hsymm 1 x]
    linarith
  have hconst : ∫ _x : X, -(B / 2) ∂μ = -(B / 2) := by simp
  rw [← hconst]
  have hintNeg : Integrable (fun x => W 1 (-x)) μ := by
    have hint' : Integrable (W 1) (Measure.map (fun x : X => -x) μ) := by
      rw [hμ]
      exact hint
    exact hint'.comp_aemeasurable hneg.aemeasurable
  exact integral_mono (integrable_const _) ((hint.add hintNeg).div_const 2) hpt


theorem half_curvature_le_sourceJensenGamma {z θ : ℝ} (hz1 : z < 1) :
    ((z / (1 - z) + z ^ 2 / (1 - z) ^ 2) * θ ^ 2) / 2 ≤
      sourceJensenGamma z * θ ^ 2 := by
  have hden : 0 < 1 - z := by linarith
  have hden2 : 0 < (1 - z) ^ 2 := sq_pos_of_pos hden
  have hzsq : 0 ≤ z ^ 2 := sq_nonneg z
  unfold sourceJensenGamma
  have hcoeff :
      (z / (1 - z) + z ^ 2 / (1 - z) ^ 2) / 2 ≤
        z / (2 * (1 - z)) + 2 * z ^ 2 / (1 - z) ^ 2 := by
    rw [add_div]
    have hfirst : z / (1 - z) / 2 = z / (2 * (1 - z)) := by
      field_simp
    have hratio : 0 ≤ z ^ 2 / (1 - z) ^ 2 :=
      div_nonneg hzsq (sq_nonneg (1 - z))
    have hsecond : z ^ 2 / (1 - z) ^ 2 / 2 ≤ 2 * z ^ 2 / (1 - z) ^ 2 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      calc
        z ^ 2 / (1 - z) ^ 2 ≤ 4 * (z ^ 2 / (1 - z) ^ 2) := by
          simpa using (mul_le_mul_of_nonneg_right
            (show (1 : ℝ) ≤ 4 by norm_num) hratio)
        _ = (2 * z ^ 2 / (1 - z) ^ 2) * 2 := by
          field_simp
          ring
    rw [hfirst]
    linarith [hsecond]
  have hθ : 0 ≤ θ ^ 2 := sq_nonneg θ
  calc
    ((z / (1 - z) + z ^ 2 / (1 - z) ^ 2) * θ ^ 2) / 2 =
        ((z / (1 - z) + z ^ 2 / (1 - z) ^ 2) / 2) * θ ^ 2 := by ring
    _ ≤ sourceJensenGamma z * θ ^ 2 := mul_le_mul_of_nonneg_right hcoeff hθ


/-- A uniform repair of (2.102) on the printed interval, retaining the exact coefficient. -/
theorem sourceJensenGamma_le_five_mul {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 1 / 2) :
    sourceJensenGamma z ≤ 5 * z := by
  have hden : 0 < 1 - z := by linarith
  have hdenLower : 1 / 2 ≤ 1 - z := by linarith
  have hdenSqLower : 1 / 4 ≤ (1 - z) ^ 2 := by nlinarith
  have hfirst : z / (2 * (1 - z)) ≤ z := by
    rw [div_le_iff₀ (by positivity)]
    have hprod := mul_nonneg hz0 (sub_nonneg.mpr (by linarith : 1 ≤ 2 * (1 - z)))
    nlinarith
  have hsecond : 2 * z ^ 2 / (1 - z) ^ 2 ≤ 4 * z := by
    rw [div_le_iff₀ (sq_pos_of_pos hden)]
    have hmul := mul_le_mul_of_nonneg_left hdenSqLower (show 0 ≤ 4 * z by positivity)
    nlinarith
  unfold sourceJensenGamma
  linarith

/-! ### Scalar logarithmic factor calculus -/

noncomputable def shiftedDenominator (z a θ t : ℝ) : ℝ :=
  1 + z * Real.cos (a - t * θ)

noncomputable def shiftedLogFactor (z a θ t : ℝ) : ℝ :=
  Real.log (shiftedDenominator z a θ t)

noncomputable def shiftedLogFactorFirst (z a θ t : ℝ) : ℝ :=
  z * θ * Real.sin (a - t * θ) / shiftedDenominator z a θ t

noncomputable def shiftedLogFactorSecond (z a θ t : ℝ) : ℝ :=
  ((-z * θ ^ 2 * Real.cos (a - t * θ)) * shiftedDenominator z a θ t -
      (z * θ * Real.sin (a - t * θ)) * (z * θ * Real.sin (a - t * θ))) /
    (shiftedDenominator z a θ t) ^ 2

theorem shiftedDenominator_pos {z a θ t : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    0 < shiftedDenominator z a θ t := by
  have hcos := mul_le_mul_of_nonneg_left
    (Real.neg_one_le_cos (a - t * θ)) hz0
  unfold shiftedDenominator
  nlinarith

theorem hasDerivAt_shiftedLogFactor {z a θ t : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasDerivAt (fun s => shiftedLogFactor z a θ s)
      (shiftedLogFactorFirst z a θ t) t := by
  have harg : HasDerivAt (fun s : ℝ => a - s * θ) (-θ) t := by
    convert (hasDerivAt_const t a).sub ((hasDerivAt_id t).mul_const θ) using 1
    · funext s
      simp
    · ring
  have hcos := (Real.hasDerivAt_cos (a - t * θ)).comp t harg
  have hden : HasDerivAt (fun s => shiftedDenominator z a θ s)
      (z * θ * Real.sin (a - t * θ)) t := by
    have h := (hasDerivAt_const t (1 : ℝ)).add (hcos.const_mul z)
    convert h using 1
    · funext s
      simp [shiftedDenominator]
    · ring
  have hlog := hden.log (ne_of_gt (shiftedDenominator_pos hz0 hz1))
  convert hlog using 1 <;> dsimp [shiftedLogFactor, shiftedLogFactorFirst]

theorem hasDerivAt_shiftedLogFactorFirst {z a θ t : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasDerivAt (fun s => shiftedLogFactorFirst z a θ s)
      (shiftedLogFactorSecond z a θ t) t := by
  have harg : HasDerivAt (fun s : ℝ => a - s * θ) (-θ) t := by
    convert (hasDerivAt_const t a).sub ((hasDerivAt_id t).mul_const θ) using 1
    · funext s
      simp
    · ring
  have hsin := (Real.hasDerivAt_sin (a - t * θ)).comp t harg
  have hnum : HasDerivAt (fun s => z * θ * Real.sin (a - s * θ))
      (-z * θ ^ 2 * Real.cos (a - t * θ)) t := by
    have h := hsin.const_mul (z * θ)
    convert h using 1
    · funext s
      simp
    · ring
  have hcos := (Real.hasDerivAt_cos (a - t * θ)).comp t harg
  have hden : HasDerivAt (fun s => shiftedDenominator z a θ s)
      (z * θ * Real.sin (a - t * θ)) t := by
    have h := (hasDerivAt_const t (1 : ℝ)).add (hcos.const_mul z)
    convert h using 1
    · funext s
      simp [shiftedDenominator]
    · ring
  have hdiv := hnum.div hden (ne_of_gt (shiftedDenominator_pos hz0 hz1))
  change HasDerivAt
    (fun s => z * θ * Real.sin (a - s * θ) / shiftedDenominator z a θ s)
    (((-z * θ ^ 2 * Real.cos (a - t * θ)) * shiftedDenominator z a θ t -
      (z * θ * Real.sin (a - t * θ)) * (z * θ * Real.sin (a - t * θ))) /
      (shiftedDenominator z a θ t) ^ 2) t
  exact hdiv

theorem abs_shiftedLogFactorSecond_le {z a θ t : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    |shiftedLogFactorSecond z a θ t| ≤
      (z / (1 - z) + z ^ 2 / (1 - z) ^ 2) * θ ^ 2 := by
  let δ := 1 - z
  let D := shiftedDenominator z a θ t
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hD : 0 < D := shiftedDenominator_pos hz0 hz1
  have hδD : δ ≤ D := by
    have hcos := mul_le_mul_of_nonneg_left
      (Real.neg_one_le_cos (a - t * θ)) hz0
    dsimp [δ, D, shiftedDenominator]
    nlinarith
  have hDne : D ≠ 0 := ne_of_gt hD
  have hδne : δ ≠ 0 := ne_of_gt hδ
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hD2 : 0 < D ^ 2 := sq_pos_of_pos hD
  have hδ2D2 : δ ^ 2 ≤ D ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self (le_of_lt hδ) hδD
  have hzθ : 0 ≤ z * θ ^ 2 := mul_nonneg hz0 (sq_nonneg θ)
  have hcosAbs : |z * θ ^ 2 * Real.cos (a - t * θ)| ≤ z * θ ^ 2 := by
    rw [abs_mul, abs_of_nonneg hzθ]
    calc
      z * θ ^ 2 * |Real.cos (a - t * θ)| ≤ z * θ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hzθ
      _ = z * θ ^ 2 := mul_one _
  have hsinSq : 0 ≤ Real.sin (a - t * θ) ^ 2 := sq_nonneg _
  have hsinSqLe : Real.sin (a - t * θ) ^ 2 ≤ 1 := by
    have hs := Real.abs_sin_le_one (a - t * θ)
    rw [abs_le] at hs
    nlinarith [sq_nonneg (Real.sin (a - t * θ) - 1),
      sq_nonneg (Real.sin (a - t * θ) + 1)]
  have hz2θ : 0 ≤ z ^ 2 * θ ^ 2 := mul_nonneg (sq_nonneg z) (sq_nonneg θ)
  have hterm1 :
      |(z * θ ^ 2 * Real.cos (a - t * θ)) / D| ≤ z * θ ^ 2 / δ := by
    rw [abs_div, abs_of_pos hD]
    exact (div_le_div_of_nonneg_right hcosAbs (le_of_lt hD)).trans
      (div_le_div_of_nonneg_left hzθ hδ hδD)
  have hterm2 :
      |(z ^ 2 * θ ^ 2 * Real.sin (a - t * θ) ^ 2) / D ^ 2| ≤
        z ^ 2 * θ ^ 2 / δ ^ 2 := by
    rw [abs_div, abs_of_pos hD2]
    have hnum : |z ^ 2 * θ ^ 2 * Real.sin (a - t * θ) ^ 2| ≤ z ^ 2 * θ ^ 2 := by
      rw [abs_of_nonneg (mul_nonneg hz2θ hsinSq)]
      calc
        z ^ 2 * θ ^ 2 * Real.sin (a - t * θ) ^ 2 ≤
            z ^ 2 * θ ^ 2 * 1 := mul_le_mul_of_nonneg_left hsinSqLe hz2θ
        _ = z ^ 2 * θ ^ 2 := by ring
    exact (div_le_div_of_nonneg_right hnum (le_of_lt hD2)).trans
      (div_le_div_of_nonneg_left hz2θ hδ2 hδ2D2)
  have hrewrite : shiftedLogFactorSecond z a θ t =
      -(z * θ ^ 2 * Real.cos (a - t * θ) / D) -
        z ^ 2 * θ ^ 2 * Real.sin (a - t * θ) ^ 2 / D ^ 2 := by
    dsimp [shiftedLogFactorSecond, D, shiftedDenominator]
    field_simp [hDne]
  rw [hrewrite]
  calc
    |-(z * θ ^ 2 * Real.cos (a - t * θ) / D) -
        z ^ 2 * θ ^ 2 * Real.sin (a - t * θ) ^ 2 / D ^ 2| ≤
      |z * θ ^ 2 * Real.cos (a - t * θ) / D| +
        |z ^ 2 * θ ^ 2 * Real.sin (a - t * θ) ^ 2 / D ^ 2| := by
          rw [show -(z * θ ^ 2 * Real.cos (a - t * θ) / D) -
              z ^ 2 * θ ^ 2 * Real.sin (a - t * θ) ^ 2 / D ^ 2 =
              -((z * θ ^ 2 * Real.cos (a - t * θ) / D) +
                z ^ 2 * θ ^ 2 * Real.sin (a - t * θ) ^ 2 / D ^ 2) by ring,
            abs_neg]
          exact abs_add_le _ _
    _ ≤ z * θ ^ 2 / δ + z ^ 2 * θ ^ 2 / δ ^ 2 := add_le_add hterm1 hterm2
    _ = (z / (1 - z) + z ^ 2 / (1 - z) ^ 2) * θ ^ 2 := by
      dsimp [δ]
      field_simp [hδne]

noncomputable def ensembleLogShift {I X : Type*} [Fintype I]
    (z θ : I → ℝ) (angle : I → X → ℝ) (t : ℝ) (φ : X) : ℝ :=
  Finset.univ.sum fun i =>
    (shiftedLogFactor (z i) (angle i φ) (θ i) t -
      shiftedLogFactor (z i) (angle i φ) (θ i) 0)

noncomputable def ensembleLogShiftFirst {I X : Type*} [Fintype I]
    (z θ : I → ℝ) (angle : I → X → ℝ) (t : ℝ) (φ : X) : ℝ :=
  Finset.univ.sum fun i => shiftedLogFactorFirst (z i) (angle i φ) (θ i) t

noncomputable def ensembleLogShiftSecond {I X : Type*} [Fintype I]
    (z θ : I → ℝ) (angle : I → X → ℝ) (t : ℝ) (φ : X) : ℝ :=
  Finset.univ.sum fun i => shiftedLogFactorSecond (z i) (angle i φ) (θ i) t

noncomputable def ensembleJensenBudget {I : Type*} [Fintype I]
    (z θ : I → ℝ) : ℝ :=
  Finset.univ.sum fun i => sourceJensenGamma (z i) * θ i ^ 2

theorem exp_finset_sum_eq_prod {I : Type*} (s : Finset I) (f : I → ℝ) :
    Real.exp (∑ i ∈ s, f i) = ∏ i ∈ s, Real.exp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [Finset.sum_insert, hi, Finset.prod_insert, ih, Real.exp_add]

theorem exp_ensembleLogShift_eq_factorRatio {I X : Type*} [Fintype I]
    (z θ : I → ℝ) (angle : I → X → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i < 1) (φ : X) :
    Real.exp (ensembleLogShift z θ angle 1 φ) =
      Finset.univ.prod fun i =>
        shiftedDenominator (z i) (angle i φ) (θ i) 1 /
          shiftedDenominator (z i) (angle i φ) (θ i) 0 := by
  unfold ensembleLogShift
  rw [exp_finset_sum_eq_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [shiftedLogFactor]
  rw [Real.exp_sub]
  rw [Real.exp_log (shiftedDenominator_pos (hz0 i) (hz1 i))]
  rw [Real.exp_log (shiftedDenominator_pos (hz0 i) (hz1 i))]

theorem perEnsembleJensen_279 {I X : Type*} [Fintype I]
    [MeasurableSpace X] [Neg X]
    {ν : Measure X} [IsProbabilityMeasure ν]
    (hν : Measure.map (fun x : X => -x) ν = ν)
    (hneg : Measurable (fun x : X => -x))
    (z θ : I → ℝ) (angle : I → X → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i < 1)
    (hangleNeg : ∀ i φ, angle i (-φ) = -angle i φ)
    (hint : Integrable (ensembleLogShift z θ angle 1) ν)
    (hexp : Integrable (fun φ => Real.exp (ensembleLogShift z θ angle 1 φ)) ν) :
    Real.exp (-ensembleJensenBudget z θ) ≤
      ∫ φ, Real.exp (ensembleLogShift z θ angle 1 φ) ∂ν := by
  have hcore : Real.exp (-((2 * ensembleJensenBudget z θ) / 2)) ≤
      ∫ φ, Real.exp (ensembleLogShift z θ angle 1 φ) ∂ν := by
    apply exp_neg_half_le_integral_exp
      (μ := ν) (W := ensembleLogShift z θ angle)
      (W' := ensembleLogShiftFirst z θ angle)
      (W'' := ensembleLogShiftSecond z θ angle)
      (B := 2 * ensembleJensenBudget z θ) hν hneg
    · intro φ
      simp [ensembleLogShift]
    · intro t φ
      unfold ensembleLogShift
      apply Finset.sum_congr rfl
      intro i hi
      have hfactor (s : ℝ) :
          shiftedLogFactor (z i) (angle i (-φ)) (θ i) s =
            shiftedLogFactor (z i) (angle i φ) (θ i) (-s) := by
        unfold shiftedLogFactor shiftedDenominator
        rw [hangleNeg]
        have harg : -angle i φ - s * θ i =
            -(angle i φ - (-s) * θ i) := by ring
        rw [harg, Real.cos_neg]
      rw [hfactor t, hfactor 0]
      simp
    · intro φ s hs
      unfold ensembleLogShift ensembleLogShiftFirst
      apply HasDerivAt.fun_sum
      intro i hi
      exact (hasDerivAt_shiftedLogFactor (hz0 i) (hz1 i)).sub_const _
    · intro φ s hs
      unfold ensembleLogShiftFirst ensembleLogShiftSecond
      apply HasDerivAt.fun_sum
      intro i hi
      exact hasDerivAt_shiftedLogFactorFirst (hz0 i) (hz1 i)
    · intro φ s hs
      unfold ensembleLogShiftSecond ensembleJensenBudget
      calc
        |∑ i ∈ Finset.univ,
            shiftedLogFactorSecond (z i) (angle i φ) (θ i) s| ≤
          ∑ i ∈ Finset.univ,
            |shiftedLogFactorSecond (z i) (angle i φ) (θ i) s| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.univ,
            (z i / (1 - z i) + z i ^ 2 / (1 - z i) ^ 2) * θ i ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          exact abs_shiftedLogFactorSecond_le (hz0 i) (hz1 i)
        _ ≤ ∑ i ∈ Finset.univ, 2 * sourceJensenGamma (z i) * θ i ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          have h := half_curvature_le_sourceJensenGamma (hz1 i) (θ := θ i)
          nlinarith
        _ = 2 * (∑ i ∈ Finset.univ, sourceJensenGamma (z i) * θ i ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = 2 * ensembleJensenBudget z θ := by
          simp [ensembleJensenBudget]
    · exact hint
    · exact hexp
  have harg : -((2 * ensembleJensenBudget z θ) / 2) = -ensembleJensenBudget z θ := by
    ring
  rw [harg] at hcore
  exact hcore

/-! ## Correctly scoped finite-mixture aggregation  -/


theorem weightedEnsembleAggregate {I : Type*} [Fintype I]
    (d Z J P : I → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hpoint : ∀ i, Z i * P i ≤ J i)
    (hden : 0 < ∑ i, d i * Z i) :
    (∑ i, d i * J i) / (∑ i, d i * Z i) ≥
      ∑ i, (d i * Z i / (∑ j, d j * Z j)) * P i := by
  have hterm : ∀ i, d i * Z i * P i ≤ d i * J i := by
    intro i
    calc
      d i * Z i * P i = d i * (Z i * P i) := by ring
      _ ≤ d i * J i := mul_le_mul_of_nonneg_left (hpoint i) (hd i)
  have hweighted :
      (∑ i, (d i * Z i / (∑ j, d j * Z j)) * P i) *
          (∑ j, d j * Z j) = ∑ i, d i * Z i * P i := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [ne_of_gt hden]
  rw [ge_iff_le, le_div_iff₀ hden]
  calc
    (∑ i, (d i * Z i / (∑ j, d j * Z j)) * P i) *
        (∑ j, d j * Z j) = ∑ i, d i * Z i * P i := hweighted
    _ ≤ ∑ i, d i * J i := Finset.sum_le_sum fun i hi => hterm i


end FroehlichSpencer.FS82.Moment.SourceJensen
