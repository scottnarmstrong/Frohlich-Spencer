/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.MeasureJacobian
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped InnerProductSpace

public section

namespace FroehlichSpencer.FS82.Gaussian

@[expose] noncomputable def radialWeight {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (β : ℝ) (x : V) : ENNReal :=
  ENNReal.ofReal (Real.exp (-(1 / (2 * β)) * ‖x‖ ^ 2))

@[expose] noncomputable def radialDensityMeasure {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasureSpace V]
    (β : ℝ) : Measure V := volume.withDensity (radialWeight β)

theorem measurable_radialWeight {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] (β : ℝ) :
    Measurable (radialWeight (V := V) β) := by
  change Measurable (fun x : V => ENNReal.ofReal (Real.exp (-(1 / (2 * β)) * ‖x‖ ^ 2)))
  fun_prop

theorem radialWeight_integral {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {β : ℝ} (hβ : 0 < β) :
    radialDensityMeasure (V := V) β Set.univ =
      ENNReal.ofReal ((Real.pi / (1 / (2 * β))) ^ (Module.finrank ℝ V / 2 : ℝ)) := by
  let b : ℝ := 1 / (2 * β)
  have hb : 0 < b := by dsimp [b]; positivity
  have hint : Integrable (fun x : V => Real.exp (-b * ‖x‖ ^ 2)) volume := by
    have hcx := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := V) (show 0 < (b : ℂ).re by exact_mod_cast hb) 0 (0 : V)
    have hn := hcx.norm
    convert hn using 1
    ext x
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, pow_two]
  have hnonneg : 0 ≤ᵐ[volume] fun x : V => Real.exp (-b * ‖x‖ ^ 2) :=
    ae_of_all _ fun _ => (Real.exp_pos _).le
  have hweight : radialWeight β = fun x : V =>
      ENNReal.ofReal (Real.exp (-b * ‖x‖ ^ 2)) := by
    funext x
    simp [radialWeight, b, div_eq_mul_inv, mul_comm]
  have hm : radialDensityMeasure (V := V) β Set.univ =
      ENNReal.ofReal (∫ x : V, Real.exp (-b * ‖x‖ ^ 2) ∂volume) := by
    rw [radialDensityMeasure, withDensity_apply (radialWeight β) MeasurableSet.univ, setLIntegral_univ, hweight,
      ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  rw [hm, GaussianFourier.integral_rexp_neg_mul_sq_norm hb]


theorem normalizedRadial_charFun {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {β : ℝ} (hβ : 0 < β) (t : V) :
    charFun (normalizedMeasure (radialDensityMeasure (V := V) β)) t =
      Complex.exp (-(β : ℂ) * (‖t‖ ^ 2 : ℂ) / 2) := by
  let b : ℝ := 1 / (2 * β)
  let M : ℝ := (Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℝ)
  have hb : 0 < b := by dsimp [b]; positivity
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hmass : radialDensityMeasure (V := V) β Set.univ = ENNReal.ofReal M := by
    simpa [M, b] using radialWeight_integral (V := V) hβ
  rw [charFun_apply]
  simp only [normalizedMeasure, integral_smul_measure]
  rw [hmass, ENNReal.toReal_inv, ENNReal.toReal_ofReal (le_of_lt hMpos)]
  rw [radialDensityMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_radialWeight β) (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
  simp only [radialWeight, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  have hint : (∫ x : V,
      (Real.exp (-(1 / (2 * β)) * ‖x‖ ^ 2) : ℝ) •
        Complex.exp (inner ℝ x t * Complex.I) ∂volume) =
      ∫ x : V, Complex.exp (-(b : ℂ) * (‖x‖ ^ 2 : ℂ) +
        Complex.I * (inner ℝ t x : ℂ)) ∂volume := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Complex.real_smul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp [b, real_inner_comm]
    ring
  rw [hint, GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (V := V) (show 0 < (b : ℂ).re by exact_mod_cast hb) Complex.I t]
  let q : ℝ := Module.finrank ℝ V / 2
  have hbaseR : Real.pi / b = Real.pi * β * 2 := by
    dsimp [b]
    field_simp [ne_of_gt hβ]
  have hbaseC : (↑Real.pi / (b : ℂ)) = (↑(Real.pi * β * 2) : ℂ) := by
    exact_mod_cast hbaseR
  have hexp : Complex.I ^ 2 * (↑‖t‖ ^ 2 : ℂ) / (4 * (b : ℂ)) =
      -(β : ℂ) * (‖t‖ ^ 2 : ℂ) / 2 := by
    have hbC : (b : ℂ) = 1 / (2 * (β : ℂ)) := by
      dsimp [b]
      push_cast
      ring
    rw [Complex.I_sq, hbC]
    have hβC : (β : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hβ)
    field_simp [hβC]
    ring
  have hq : (↑(Module.finrank ℝ V) / 2 : ℂ) = (↑q : ℂ) := by
    simp [q]
  have hMreal : M = (Real.pi * β * 2) ^ q := by
    dsimp [M]
    rw [hbaseR]
  have hfactor : (↑Real.pi / (b : ℂ)) ^
      (↑(Module.finrank ℝ V) / 2 : ℂ) = (↑M : ℂ) := by
    rw [hbaseC, hq]
    exact (Complex.ofReal_cpow (by positivity : 0 ≤ Real.pi * β * 2) q).symm.trans
      (congrArg (fun x : ℝ => (x : ℂ)) hMreal.symm)
  rw [hfactor, hexp, Complex.real_smul]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hMpos)
  simp [Complex.ofReal_inv, hM]


theorem radialDensityMeasure_mass_finite_pos {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {β : ℝ} (hβ : 0 < β) :
    0 < radialDensityMeasure (V := V) β Set.univ ∧
      radialDensityMeasure (V := V) β Set.univ < ⊤ := by
  rw [radialWeight_integral (V := V) hβ]
  constructor
  · positivity
  · exact ENNReal.ofReal_lt_top

theorem normalizedRadialMeasure_mass_eq_one {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {β : ℝ} (hβ : 0 < β) :
    normalizedMeasure (radialDensityMeasure (V := V) β) Set.univ = 1 := by
  have hmass := radialDensityMeasure_mass_finite_pos (V := V) hβ
  simp only [normalizedMeasure, Measure.smul_apply]
  exact ENNReal.inv_mul_cancel (ne_of_gt hmass.1) (ne_of_lt hmass.2)

theorem normalizedRadial_eq_scaledStdGaussian
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {β : ℝ} (hβ : 0 < β) :
    normalizedMeasure (radialDensityMeasure (V := V) β) =
      Measure.map (fun x : V => Real.sqrt β • x) (stdGaussian V) := by
  let μ := normalizedMeasure (radialDensityMeasure (V := V) β)
  have hmass : μ Set.univ = 1 := normalizedRadialMeasure_mass_eq_one (V := V) hβ
  have hμ : IsProbabilityMeasure μ := ⟨hmass⟩
  apply Measure.ext_of_charFun
  funext t
  rw [normalizedRadial_charFun hβ t, charFun_map_smul (μ := stdGaussian V)
    (Real.sqrt β) t, charFun_stdGaussian]
  apply congrArg Complex.exp
  have hnorm : ‖Real.sqrt β • t‖ = Real.sqrt β * ‖t‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg β)]
  rw [hnorm]
  push_cast
  have hsqrt : (↑(Real.sqrt β) : ℂ) ^ 2 = (↑β : ℂ) := by
    exact_mod_cast Real.sq_sqrt (le_of_lt hβ)
  rw [mul_pow, hsqrt]
  ring_nf

end FroehlichSpencer.FS82.Gaussian

end
