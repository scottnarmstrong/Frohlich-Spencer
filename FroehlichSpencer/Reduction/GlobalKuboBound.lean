/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Reduction.EventEstimate
public import FroehlichSpencer.Reduction.BadShellBound
import FroehlichSpencer.Infra.Lattice.Decay
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Global Kubo bound from dyadic Green events -/

public section

open MeasureTheory

namespace FroehlichSpencer.Reduction

/-- The finite polynomially weighted exponential moment on the lattice. -/
@[expose] noncomputable def greenDecayMoment (ν : ℕ) (m : ℝ) : ℝ :=
  ∑' x : Site ν, (latticeLength ν x) ^ 2 * Real.exp (-m * latticeLength ν x)

theorem summable_greenDecayMoment (ν : ℕ) {m : ℝ} (hm : 0 < m) :
    Summable (fun x : Site ν =>
      (latticeLength ν x) ^ 2 * Real.exp (-m * latticeLength ν x)) := by
  simpa only [latticeLength_eq_latticeCast_norm] using
    (Infra.Lattice.summable_norm_pow_mul_exp_neg (ν := ν) (a := 2) hm)

private theorem goodDecay_real_bound (ν : ℕ) {m R ε : ℝ} (hm : 0 < m)
    (hR : 1 ≤ R) (x : Site ν) :
    (latticeLength ν x) ^ 2 * ε ^ 2 *
        Real.exp (m * (dyadicGreenScale ν R x - latticeLength ν x)) ^ 2 ≤
      (ε ^ 2 * Real.exp (m * R / 4)) *
        ((latticeLength ν x) ^ 2 * Real.exp (-m * latticeLength ν x)) := by
  have hscale := dyadicGreenScale_le_inner_outer
    (lt_of_lt_of_le zero_lt_one hR) x
  have hml : 0 ≤ m * latticeLength ν x :=
    mul_nonneg hm.le (latticeLength_nonneg ν x)
  have hexpArg : 2 * (m * (dyadicGreenScale ν R x - latticeLength ν x)) ≤
      m * R / 4 - m * latticeLength ν x := by
    have hmul := mul_le_mul_of_nonneg_left hscale hm.le
    nlinarith [hmul, hml]
  have hexp :
      Real.exp (m * (dyadicGreenScale ν R x - latticeLength ν x)) ^ 2 ≤
        Real.exp (m * R / 4) * Real.exp (-m * latticeLength ν x) := by
    calc
      Real.exp (m * (dyadicGreenScale ν R x - latticeLength ν x)) ^ 2 =
          Real.exp (2 * (m * (dyadicGreenScale ν R x - latticeLength ν x))) := by
            rw [pow_two, ← Real.exp_add]
            congr 1; ring
      _ ≤ Real.exp (m * R / 4 - m * latticeLength ν x) :=
            Real.exp_le_exp.mpr hexpArg
      _ = Real.exp (m * R / 4) * Real.exp (-m * latticeLength ν x) := by
            rw [← Real.exp_add]
            congr 1; ring
  calc
    (latticeLength ν x) ^ 2 * ε ^ 2 *
        Real.exp (m * (dyadicGreenScale ν R x - latticeLength ν x)) ^ 2 ≤
      (latticeLength ν x) ^ 2 * ε ^ 2 *
        (Real.exp (m * R / 4) * Real.exp (-m * latticeLength ν x)) := by
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (ε ^ 2 * Real.exp (m * R / 4)) *
          ((latticeLength ν x) ^ 2 * Real.exp (-m * latticeLength ν x)) := by ring

private theorem weighted_site_bound
    (ν : ℕ) (hν : 0 < ν) (law : Measure ℝ) [IsProbabilityMeasure law]
    (E m K R : ℝ) (hK : 0 ≤ K) (hR : 1 ≤ R)
    (x : Site ν) (ε : {ε : ℝ // ε ≠ 0})
    (hprob : MeasurableSet (greenDecayEvent ν hν E m
        (dyadicGreenScale ν R x) x) ∧
      ENNReal.ofReal (1 - K / Real.rpow (dyadicGreenScale ν R x)
          ((ν + 5 : ℕ) : ℝ)) ≤
        configurationMeasure ν law
          (greenDecayEvent ν hν E m (dyadicGreenScale ν R x) x)) :
    ENNReal.ofReal ((latticeLength ν x) ^ 2) *
        (ENNReal.ofReal (ε.1 ^ 2) *
          ∫⁻ v : Configuration ν,
            ENNReal.ofReal
              (‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
                (by simpa using ε.2) v 0 x‖ ^ 2)
            ∂configurationMeasure ν law) ≤
      ENNReal.ofReal
          ((latticeLength ν x) ^ 2 * ε.1 ^ 2 *
            Real.exp (m * (dyadicGreenScale ν R x - latticeLength ν x)) ^ 2) +
        ENNReal.ofReal (badRealTerm ν R (K) x) := by
  have hN : 0 < dyadicGreenScale ν R x := by
    unfold dyadicGreenScale
    positivity
  have hlocal := weighted_green_lintegral_le ν hν law E m
    (dyadicGreenScale ν R x) K ((ν + 5 : ℕ) : ℝ) hN hK x ε hprob.1 hprob.2
  have hlen : 0 ≤ (latticeLength ν x) ^ 2 := sq_nonneg _
  have hmul : ENNReal.ofReal ((latticeLength ν x) ^ 2) *
        (ENNReal.ofReal (ε.1 ^ 2) *
          ∫⁻ v : Configuration ν,
            ENNReal.ofReal
              (‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
                (by simpa using ε.2) v 0 x‖ ^ 2)
            ∂configurationMeasure ν law) ≤
      ENNReal.ofReal ((latticeLength ν x) ^ 2) *
        (ENNReal.ofReal
            (ε.1 ^ 2 * Real.exp
              (m * (dyadicGreenScale ν R x - latticeLength ν x)) ^ 2) +
          ENNReal.ofReal
            (K / Real.rpow (dyadicGreenScale ν R x) ((ν + 5 : ℕ) : ℝ))) :=
    mul_le_mul_of_nonneg_left hlocal (by simp :
      0 ≤ ENNReal.ofReal ((latticeLength ν x) ^ 2))
  rw [mul_add] at hmul
  have hgood : ENNReal.ofReal ((latticeLength ν x) ^ 2) *
        ENNReal.ofReal
          (ε.1 ^ 2 * Real.exp
            (m * (dyadicGreenScale ν R x - latticeLength ν x)) ^ 2) =
      ENNReal.ofReal
        ((latticeLength ν x) ^ 2 * ε.1 ^ 2 *
          Real.exp (m * (dyadicGreenScale ν R x - latticeLength ν x)) ^ 2) := by
    rw [← ENNReal.ofReal_mul hlen]
    congr 1; ring
  have hbad : ENNReal.ofReal ((latticeLength ν x) ^ 2) *
        ENNReal.ofReal
          (K / Real.rpow (dyadicGreenScale ν R x) ((ν + 5 : ℕ) : ℝ)) =
      ENNReal.ofReal (badRealTerm ν R K x) := by
    rw [← ENNReal.ofReal_mul hlen]
    rfl
  rw [hgood, hbad] at hmul
  exact hmul

theorem kubo_le_dyadic_bound
    (ν : ℕ) (hν : 0 < ν) (law : Measure ℝ) [IsProbabilityMeasure law]
    (E m K R : ℝ) (hm : 0 < m) (hK : 0 ≤ K) (hR : 1 ≤ R)
    (ε : {ε : ℝ // ε ≠ 0})
    (hprob : ∀ x : Site ν,
      MeasurableSet (greenDecayEvent ν hν E m (dyadicGreenScale ν R x) x) ∧
      ENNReal.ofReal (1 - K / Real.rpow (dyadicGreenScale ν R x)
          ((ν + 5 : ℕ) : ℝ)) ≤
        configurationMeasure ν law
          (greenDecayEvent ν hν E m (dyadicGreenScale ν R x) x)) :
    kuboQuantity ν hν law E ε ≤
      ENNReal.ofReal (2 / (Real.pi * (ν : ℝ)) *
        (ε.1 ^ 2 * Real.exp (m * R / 4) * greenDecayMoment ν m +
          badShellConstant ν K / R ^ 3 * (8 / 7 : ℝ))) := by
  let Q : ℝ := greenDecayMoment ν m
  let c : ℝ := 2 / (Real.pi * (ν : ℝ))
  have hQsum := summable_greenDecayMoment ν hm
  have hQnonneg : 0 ≤ Q := by
    dsimp [Q, greenDecayMoment]
    exact tsum_nonneg (fun x => mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))
  have hcoeff : 0 ≤ c := by dsimp [c]; positivity
  have hsumGood :
      ∑' x : Site ν,
        ENNReal.ofReal ((latticeLength ν x) ^ 2 * ε.1 ^ 2 *
          Real.exp (m * (dyadicGreenScale ν R x - latticeLength ν x)) ^ 2) ≤
        ENNReal.ofReal (ε.1 ^ 2 * Real.exp (m * R / 4) * Q) := by
    let f : Site ν → ℝ := fun x =>
      (ε.1 ^ 2 * Real.exp (m * R / 4)) *
        ((latticeLength ν x) ^ 2 * Real.exp (-m * latticeLength ν x))
    have hfNonneg : ∀ x, 0 ≤ f x := by
      intro x
      positivity
    have hfSummable : Summable f := hQsum.mul_left _
    have hterm : ∀ x, (latticeLength ν x) ^ 2 * ε.1 ^ 2 *
        Real.exp (m * (dyadicGreenScale ν R x - latticeLength ν x)) ^ 2 ≤ f x := by
      intro x
      exact goodDecay_real_bound ν hm hR x
    calc
      ∑' x : Site ν,
          ENNReal.ofReal ((latticeLength ν x) ^ 2 * ε.1 ^ 2 *
            Real.exp (m * (dyadicGreenScale ν R x - latticeLength ν x)) ^ 2) ≤
          ∑' x : Site ν, ENNReal.ofReal (f x) :=
        ENNReal.tsum_le_tsum (fun x => ENNReal.ofReal_le_ofReal (hterm x))
      _ = ENNReal.ofReal (∑' x : Site ν, f x) :=
        (ENNReal.ofReal_tsum_of_nonneg hfNonneg hfSummable).symm
      _ = ENNReal.ofReal (ε.1 ^ 2 * Real.exp (m * R / 4) * Q) := by
        rw [tsum_mul_left]
        rfl
  have hsumBad := bad_global_sum_bound ν hR hK
  have hsumWeighted :
      ∑' x : Site ν,
        ENNReal.ofReal ((latticeLength ν x) ^ 2) *
          (ENNReal.ofReal (ε.1 ^ 2) *
            ∫⁻ v : Configuration ν,
              ENNReal.ofReal
                (‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
                  (by simpa using ε.2) v 0 x‖ ^ 2)
              ∂configurationMeasure ν law) ≤
      ENNReal.ofReal (ε.1 ^ 2 * Real.exp (m * R / 4) * Q) +
        ENNReal.ofReal (badShellConstant ν K / R ^ 3 * (8 / 7 : ℝ)) := by
    calc
      _ ≤ ∑' x : Site ν,
          (ENNReal.ofReal ((latticeLength ν x) ^ 2 * ε.1 ^ 2 *
              Real.exp (m * (dyadicGreenScale ν R x - latticeLength ν x)) ^ 2) +
            ENNReal.ofReal (badRealTerm ν R K x)) :=
        ENNReal.tsum_le_tsum (fun x => weighted_site_bound ν hν law E m K R
          hK hR x ε (hprob x))
      _ = (∑' x : Site ν,
            ENNReal.ofReal ((latticeLength ν x) ^ 2 * ε.1 ^ 2 *
              Real.exp (m * (dyadicGreenScale ν R x - latticeLength ν x)) ^ 2)) +
          ∑' x : Site ν, ENNReal.ofReal (badRealTerm ν R K x) := ENNReal.tsum_add
      _ ≤ ENNReal.ofReal (ε.1 ^ 2 * Real.exp (m * R / 4) * Q) +
          ENNReal.ofReal (badShellConstant ν K / R ^ 3 * (8 / 7 : ℝ)) :=
        add_le_add hsumGood hsumBad
  have hconst : 0 ≤ 2 / (Real.pi * (ν : ℝ)) := hcoeff
  have hgoodReal : 0 ≤ ε.1 ^ 2 * Real.exp (m * R / 4) * Q := by positivity
  have hbadReal : 0 ≤ badShellConstant ν K / R ^ 3 * (8 / 7 : ℝ) := by
    change 0 ≤ 72 ^ ν * 24 ^ 2 * 512 * K / R ^ 3 * (8 / 7 : ℝ)
    positivity
  have hcombine :
      ENNReal.ofReal (ε.1 ^ 2 * Real.exp (m * R / 4) * Q) +
        ENNReal.ofReal (badShellConstant ν K / R ^ 3 * (8 / 7 : ℝ)) =
      ENNReal.ofReal (ε.1 ^ 2 * Real.exp (m * R / 4) * Q +
        badShellConstant ν K / R ^ 3 * (8 / 7 : ℝ)) := by
    rw [← ENNReal.ofReal_add hgoodReal hbadReal]
  have hkubo : kuboQuantity ν hν law E ε =
      ENNReal.ofReal c *
        ∑' x : Site ν,
          ENNReal.ofReal ((latticeLength ν x) ^ 2) *
            (ENNReal.ofReal (ε.1 ^ 2) *
              ∫⁻ v : Configuration ν,
                ENNReal.ofReal
                  (‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
                    (by simpa using ε.2) v 0 x‖ ^ 2)
                ∂configurationMeasure ν law) := by
    simp only [kuboQuantity, c]
    have hcoeffEq : 2 * ε.1 ^ 2 / (Real.pi * (ν : ℝ)) =
        (2 / (Real.pi * (ν : ℝ))) * ε.1 ^ 2 := by ring
    calc
      ENNReal.ofReal (2 * ε.1 ^ 2 / (Real.pi * (ν : ℝ))) *
          ∑' x : Site ν,
            ENNReal.ofReal ((latticeLength ν x) ^ 2) *
              ∫⁻ v : Configuration ν,
                ENNReal.ofReal
                  (‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
                    (by simpa using ε.2) v 0 x‖ ^ 2)
                ∂configurationMeasure ν law =
        ENNReal.ofReal c *
          (ENNReal.ofReal (ε.1 ^ 2) *
            ∑' x : Site ν,
              ENNReal.ofReal ((latticeLength ν x) ^ 2) *
                ∫⁻ v : Configuration ν,
                  ENNReal.ofReal
                    (‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
                      (by simpa using ε.2) v 0 x‖ ^ 2)
                  ∂configurationMeasure ν law) := by
          rw [hcoeffEq, ENNReal.ofReal_mul
            (by positivity : 0 ≤ 2 / (Real.pi * (ν : ℝ)))]
          ac_rfl
      _ = ENNReal.ofReal c *
          ∑' x : Site ν,
            ENNReal.ofReal ((latticeLength ν x) ^ 2) *
              (ENNReal.ofReal (ε.1 ^ 2) *
                ∫⁻ v : Configuration ν,
                  ENNReal.ofReal
                    (‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
                      (by simpa using ε.2) v 0 x‖ ^ 2)
                  ∂configurationMeasure ν law) := by
          congr 1
          calc
            ENNReal.ofReal (ε.1 ^ 2) *
                ∑' x : Site ν,
                  ENNReal.ofReal ((latticeLength ν x) ^ 2) *
                    ∫⁻ v : Configuration ν,
                      ENNReal.ofReal
                        (‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
                          (by simpa using ε.2) v 0 x‖ ^ 2)
                      ∂configurationMeasure ν law =
              ∑' x : Site ν,
                ENNReal.ofReal (ε.1 ^ 2) *
                  (ENNReal.ofReal ((latticeLength ν x) ^ 2) *
                    ∫⁻ v : Configuration ν,
                      ENNReal.ofReal
                        (‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
                          (by simpa using ε.2) v 0 x‖ ^ 2)
                      ∂configurationMeasure ν law) := ENNReal.tsum_mul_left.symm
            _ = ∑' x : Site ν,
                ENNReal.ofReal ((latticeLength ν x) ^ 2) *
                  (ENNReal.ofReal (ε.1 ^ 2) *
                    ∫⁻ v : Configuration ν,
                      ENNReal.ofReal
                        (‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
                          (by simpa using ε.2) v 0 x‖ ^ 2)
                      ∂configurationMeasure ν law) := by
              apply tsum_congr
              intro x
              ac_rfl
  rw [hkubo]
  calc
    ENNReal.ofReal c *
        ∑' x : Site ν,
          ENNReal.ofReal ((latticeLength ν x) ^ 2) *
            (ENNReal.ofReal (ε.1 ^ 2) *
              ∫⁻ v : Configuration ν,
                ENNReal.ofReal
                  (‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
                    (by simpa using ε.2) v 0 x‖ ^ 2)
                ∂configurationMeasure ν law) ≤
      ENNReal.ofReal c *
        (ENNReal.ofReal (ε.1 ^ 2 * Real.exp (m * R / 4) * Q) +
          ENNReal.ofReal (badShellConstant ν K / R ^ 3 * (8 / 7 : ℝ))) :=
      mul_le_mul_of_nonneg_left hsumWeighted (by simp : 0 ≤ ENNReal.ofReal c)
    _ = ENNReal.ofReal (c *
          (ε.1 ^ 2 * Real.exp (m * R / 4) * Q +
            badShellConstant ν K / R ^ 3 * (8 / 7 : ℝ))) := by
      rw [hcombine, ← ENNReal.ofReal_mul hconst]
    _ = ENNReal.ofReal (2 / (Real.pi * (ν : ℝ)) *
          (ε.1 ^ 2 * Real.exp (m * R / 4) * greenDecayMoment ν m +
            badShellConstant ν K / R ^ 3 * (8 / 7 : ℝ))) := by
      simp [Q, c]

end FroehlichSpencer.Reduction

end
