/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.StripWeight
public import FroehlichSpencer.BKT.Rotator.BesselInterp.Properties
public import FroehlichSpencer.BKT.Rotator.Contour.Factor
public import FroehlichSpencer.BKT.Rotator.Contour.StripBounds
public import FroehlichSpencer.BKT.Rotator.Contour.Parity
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The Appendix B strip-weight instances

The plane-rotator interpolation `I_β` is a strip weight on `|Im z| ≤ β/2` for all sufficiently
large `β`. Its translation ratio and logarithmic-derivative bounds are the Appendix B estimates in
`Rotator.BesselInterp.Properties`; its decaying strip majorant is `Contour.StripBounds`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex Filter Topology
open scoped Real
open FroehlichSpencer.BKT.Rotator.BesselInterp
open FroehlichSpencer.BKT.Rotator.Contour

private theorem tangent_lower_bound (F F' F'' : ℝ → ℝ) {M : ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x)
    (hF' : ∀ x, HasDerivAt F' (F'' x) x)
    (hF'' : ∀ x, |F'' x| ≤ M) (t s : ℝ) :
    F t + F' t * s - M / 2 * s ^ 2 ≤ F (t + s) := by
  let g : ℝ → ℝ := fun x => F x + M / 2 * x ^ 2
  have hg : ∀ x, HasDerivAt g (F' x + M * x) x := by
    intro x
    have hq : HasDerivAt (fun y : ℝ => M / 2 * y ^ 2) (M * x) x := by
      have h := hasDerivAt_pow 2 x
      convert HasDerivAt.const_mul (M / 2) h using 1; ring_nf
    have h := (hF x).add hq
    convert h using 1
  have hderiv : deriv g = fun x => F' x + M * x := by
    funext x
    exact (hg x).deriv
  have hg2 : ∀ x, HasDerivAt (deriv g) (F'' x + M) x := by
    intro x
    rw [hderiv]
    have h := (hF' x).add (HasDerivAt.const_mul M (hasDerivAt_id x))
    convert h using 1
    · ext y; simp
    · ring
  have hconv : ConvexOn ℝ Set.univ g := convexOn_univ_of_deriv2_nonneg
    (fun x => (hg x).differentiableAt)
    (fun x => (hg2 x).differentiableAt)
    (fun x => by
      have hx := (hg2 x).deriv
      have hiter : (deriv^[2] g) x = F'' x + M := by
        change deriv (deriv g) x = _
        exact hx
      rw [hiter]
      have habs := abs_le.mp (hF'' x)
      linarith)
  by_cases hs : 0 ≤ s
  · by_cases hs0 : s = 0
    · simp [hs0]
    · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
      have hsec := hconv.le_slope_of_hasDerivAt (x := t) (y := t + s)
        (Set.mem_univ _) (Set.mem_univ _) (by linarith) (hg t)
      rw [slope_def_field] at hsec
      have hsec' : F' t + M * t ≤ (g (t + s) - g t) / s := by simpa using hsec
      have hmul := (le_div_iff₀ hspos).mp hsec'
      have htan : g t + (F' t + M * t) * s ≤ g (t + s) := by nlinarith
      dsimp [g] at htan
      nlinarith [htan]
  · have hsneg : s < 0 := lt_of_not_ge hs
    have hsec := hconv.slope_le_of_hasDerivAt (x := t + s) (y := t)
      (Set.mem_univ _) (Set.mem_univ _) (by linarith) (hg t)
    rw [slope_def_field] at hsec
    have hsec' : (g t - g (t + s)) / (-s) ≤ F' t + M * t := by simpa using hsec
    have hmul := (div_le_iff₀ (neg_pos.mpr hsneg)).mp hsec'
    have htan : g (t + s) ≥ g t + (F' t + M * t) * s := by nlinarith
    dsimp [g] at htan
    nlinarith [htan]

/-! ## Schwarz reflection for the Bessel interpolation -/

/-- The entire sinc kernel respects complex conjugation. -/
theorem sincSq_conj (z : ℂ) : star (sincSq z) = sincSq (star z) := by
  by_cases hz : z = 0
  · simp [sincSq, hz]
  · have hcz : (starRingEnd ℂ) z ≠ 0 := by
      intro h
      apply hz
      apply (starRingEnd ℂ).injective
      simpa using h
    change (starRingEnd ℂ) (sincSq z) = sincSq ((starRingEnd ℂ) z)
    simp only [sincSq, ite_eq_right hz, ite_eq_right hcz]
    rw [map_div₀, map_pow, map_mul]
    have hsin : (starRingEnd ℂ) (Complex.sin (π * z)) = Complex.sin (π * ((starRingEnd ℂ) z)) := by
      rw [← Complex.sin_conj]
      rw [map_mul, Complex.conj_ofReal]
    rw [hsin]
    simp only [map_pow, Complex.conj_ofReal]

/-- The Bessel defect series respects Schwarz reflection. -/
theorem defectSeries_conj (β : ℝ) (z : ℂ) :
    (starRingEnd ℂ) (defectSeries β z) = defectSeries β ((starRingEnd ℂ) z) := by
  change (starRingEnd ℂ) (∑' n : ℤ, (logDefect β n : ℂ) * sincSq (z - n)) = _
  rw [Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  rw [map_mul, Complex.conj_ofReal]
  have hkernel := sincSq_conj (z - n)
  have hkernel' : (starRingEnd ℂ) (sincSq (z - n)) =
      sincSq ((starRingEnd ℂ) z - n) := by
    have harg : (starRingEnd ℂ) (z - n) = (starRingEnd ℂ) z - n := by
      simp only [map_sub, map_intCast]
    have harg' : star (z - n) = star z - n := by simpa only [starRingEnd_apply] using harg
    rw [starRingEnd_apply]
    simpa only [starRingEnd_apply] using hkernel.trans (by rw [harg'])
  rw [hkernel']

/-- Schwarz reflection for the principal inverse hyperbolic sine on its interpolation strip. -/
theorem carsinh_conj_of_abs_im_lt_one {z : ℂ} (hz : |z.im| < 1) :
    carsinh ((starRingEnd ℂ) z) = (starRingEnd ℂ) (carsinh z) := by
  let q := 1 + z ^ 2
  have hq : q ∈ Complex.slitPlane := one_add_sq_mem_slitPlane hz
  have hn : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num
  have hsqrt : (starRingEnd ℂ) (q ^ (1 / 2 : ℂ)) =
      ((starRingEnd ℂ) q) ^ (1 / 2 : ℂ) := by
    simpa only [starRingEnd_apply, hn] using
      (Complex.conj_cpow q (1 / 2 : ℂ) (Complex.slitPlane_arg_ne_pi hq)).symm
  have hqconj : (starRingEnd ℂ) q = 1 + ((starRingEnd ℂ) z) ^ 2 := by
    simp [q, map_add, map_pow]
  have hpos : 0 < (z + q ^ (1 / 2 : ℂ)).re := add_sqrt_re_pos hz
  have harg : (z + q ^ (1 / 2 : ℂ)).arg ≠ Real.pi := by
    intro h
    have hneg := (Complex.arg_eq_pi_iff.mp h).1
    linarith
  have hsum : (starRingEnd ℂ) (z + q ^ (1 / 2 : ℂ)) =
      (starRingEnd ℂ) z + (1 + ((starRingEnd ℂ) z) ^ 2) ^ (1 / 2 : ℂ) := by
    rw [map_add, hsqrt, hqconj]
  unfold carsinh
  calc
    Complex.log ((starRingEnd ℂ) z + (1 + ((starRingEnd ℂ) z) ^ 2) ^ (1 / 2 : ℂ)) =
        Complex.log ((starRingEnd ℂ) (z + q ^ (1 / 2 : ℂ))) := by rw [hsum]
    _ = (starRingEnd ℂ) (Complex.log (z + q ^ (1 / 2 : ℂ))) := Complex.log_conj _ harg

/-- Schwarz reflection for the Debye factor on `|Im z| < β`. -/
theorem debye_conj {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : |z.im| < β) :
    debye β ((starRingEnd ℂ) z) = (starRingEnd ℂ) (debye β z) := by
  let w := z / (β : ℂ)
  have hw : |w.im| < 1 := im_div_ofReal_lt hβ hz
  have hbase : 1 + w ^ 2 ∈ Complex.slitPlane := one_add_sq_mem_slitPlane hw
  have hn : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num
  have hnm : star (-(1 / 2 : ℂ)) = -(1 / 2 : ℂ) := by norm_num
  have hroot : (starRingEnd ℂ) ((1 + w ^ 2) ^ (1 / 2 : ℂ)) =
      (1 + (starRingEnd ℂ) w ^ 2) ^ (1 / 2 : ℂ) := by
    have hbaseconj : (starRingEnd ℂ) (1 + w ^ 2) = 1 + (starRingEnd ℂ) w ^ 2 := by
      simp [map_add, map_pow]
    have h := (Complex.conj_cpow (1 + w ^ 2) (1 / 2 : ℂ)
      (Complex.slitPlane_arg_ne_pi hbase)).symm
    have h' : (starRingEnd ℂ) ((1 + w ^ 2) ^ (1 / 2 : ℂ)) =
        ((starRingEnd ℂ) (1 + w ^ 2)) ^ (1 / 2 : ℂ) := by
      simpa only [starRingEnd_apply, hn] using h
    rw [hbaseconj] at h'
    exact h'
  have hwconj : (starRingEnd ℂ) w = (starRingEnd ℂ) z / (β : ℂ) := by simp [w]
  have hbaseZ : 1 + (z / (β : ℂ)) ^ 2 = 1 + z ^ 2 / (β : ℂ) ^ 2 := by ring
  have hplaneZ : 1 + z ^ 2 / (β : ℂ) ^ 2 ∈ Complex.slitPlane := by
    rw [← hbaseZ]
    simpa [w] using hbase
  have hrootZ : (starRingEnd ℂ) ((1 + (z / (β : ℂ)) ^ 2) ^ (1 / 2 : ℂ)) =
      (1 + (starRingEnd ℂ) z ^ 2 / (β : ℂ) ^ 2) ^ (1 / 2 : ℂ) := by
    rw [hbaseZ]
    have hbaseZconj : (starRingEnd ℂ) (1 + z ^ 2 / (β : ℂ) ^ 2) =
        1 + (starRingEnd ℂ) z ^ 2 / (β : ℂ) ^ 2 := by
      simp [map_add, map_pow, map_div₀]
    have h := (Complex.conj_cpow (1 + z ^ 2 / (β : ℂ) ^ 2) (1 / 2 : ℂ)
      (Complex.slitPlane_arg_ne_pi hplaneZ)).symm
    have h' : (starRingEnd ℂ) ((1 + z ^ 2 / (β : ℂ) ^ 2) ^ (1 / 2 : ℂ)) =
        ((starRingEnd ℂ) (1 + z ^ 2 / (β : ℂ) ^ 2)) ^ (1 / 2 : ℂ) := by
      simpa only [starRingEnd_apply, hn] using h
    rw [hbaseZconj] at h'
    exact h'
  have hrootZ' := hrootZ
  rw [hbaseZ] at hrootZ'
  have hcar : carsinh ((starRingEnd ℂ) z / (β : ℂ)) =
      (starRingEnd ℂ) (carsinh (z / (β : ℂ))) := by
    have h := carsinh_conj_of_abs_im_lt_one hw
    simpa [w, hwconj] using h
  have hrootPos : 0 < ((β : ℂ) * (1 + (z / (β : ℂ)) ^ 2) ^ (1 / 2 : ℂ)).re := by
    have hsqrt := half_cpow_re_pos hbase
    have hrewrite : (1 + (z / (β : ℂ)) ^ 2) ^ (1 / 2 : ℂ) = (1 + w ^ 2) ^ (1 / 2 : ℂ) := by
      simp [w]
    rw [hrewrite, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos hβ hsqrt
  have hrootPosDirect : 0 < ((β : ℂ) * (1 + z ^ 2 / (β : ℂ) ^ 2) ^ (1 / 2 : ℂ)).re := by
    rw [← hbaseZ]
    exact hrootPos
  have harg : ((β : ℂ) * (1 + z ^ 2 / (β : ℂ) ^ 2) ^ (1 / 2 : ℂ)).arg ≠ Real.pi := by
    intro h
    have hneg := (Complex.arg_eq_pi_iff.mp h).1
    exact (not_lt_of_ge hrootPosDirect.le) hneg
  have houter : (starRingEnd ℂ) (((β : ℂ) * (1 + z ^ 2 / (β : ℂ) ^ 2) ^ (1 / 2 : ℂ)) ^ (-(1 / 2) : ℂ)) =
      ((starRingEnd ℂ) ((β : ℂ) * (1 + z ^ 2 / (β : ℂ) ^ 2) ^ (1 / 2 : ℂ))) ^ (-(1 / 2) : ℂ) := by
    simpa only [starRingEnd_apply, hnm] using (Complex.conj_cpow
      ((β : ℂ) * (1 + z ^ 2 / (β : ℂ) ^ 2) ^ (1 / 2 : ℂ))
      (-(1 / 2) : ℂ) harg).symm
  have hreal : (starRingEnd ℂ) ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) =
      ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) := by simp
  have hexp : (starRingEnd ℂ) (Complex.exp (-z * carsinh (z / β) + β *
      (1 + z ^ 2 / (β : ℂ) ^ 2) ^ (1 / 2 : ℂ))) =
      Complex.exp (-(starRingEnd ℂ) z * carsinh ((starRingEnd ℂ) z / β) + β *
      (1 + (starRingEnd ℂ) z ^ 2 / (β : ℂ) ^ 2) ^ (1 / 2 : ℂ)) := by
    calc
      _ = Complex.exp ((starRingEnd ℂ) (-z * carsinh (z / β) + β *
          (1 + z ^ 2 / (β : ℂ) ^ 2) ^ (1 / 2 : ℂ))) := (Complex.exp_conj _).symm
      _ = _ := by
        congr 1
        simp only [map_add, map_mul, map_neg, Complex.conj_ofReal]
        rw [hcar, hrootZ']
  unfold debye
  rw [map_mul, map_mul, hreal]
  rw [hexp, houter]
  simp only [map_mul, Complex.conj_ofReal]
  rw [hrootZ']

/-- Schwarz reflection for the full Appendix B interpolation on its closed half-strip. -/
theorem besselInterp_conj {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : |z.im| ≤ β / 2) :
    (starRingEnd ℂ) (besselInterp β z) = besselInterp β ((starRingEnd ℂ) z) := by
  have hz' : |z.im| < β := by linarith [abs_nonneg z.im]
  have hdf : (starRingEnd ℂ) (defectFactor β z) = defectFactor β ((starRingEnd ℂ) z) := by
    unfold defectFactor
    calc
      _ = Complex.exp ((starRingEnd ℂ) (defectSeries β z)) := (Complex.exp_conj _).symm
      _ = _ := by rw [defectSeries_conj]
  unfold besselInterp
  change (starRingEnd ℂ) (debye β z * defectFactor β z) = _
  rw [map_mul, ← debye_conj hβ hz', hdf]

/-! ## Strip-weight instance -/

/-- The Bessel interpolation is a strip weight for all sufficiently large inverse temperatures. -/
theorem exists_isStripWeight_besselInterp :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 ≤ C ∧ ∀ β : ℝ, β₀ ≤ β →
      IsStripWeight (besselInterp β) (β / 2)
        (fun u => cEnvelope C u / β) := by
  obtain ⟨β₀, C, hβ₀, hC, hratio⟩ := norm_besselInterp_translate_div_le
  refine ⟨max β₀ 1, C, lt_max_of_lt_left hβ₀, hC, ?_⟩
  intro β hβ
  have hβlarge : β₀ ≤ β := le_trans (le_max_left _ _) hβ
  have hβ1 : 1 ≤ β := le_trans (le_max_right _ _) hβ
  have hβpos : 0 < β := by linarith
  obtain ⟨K, hK, hstrip⟩ := exists_norm_besselInterp_strip_le hβ1
  refine ⟨by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x => (besselInterp_ofReal_im_eq_zero_and_re_pos hβpos x).1
  · exact fun x => (besselInterp_ofReal_im_eq_zero_and_re_pos hβpos x).2
  · intro z hz
    exact analyticAt_besselInterp hβpos (by linarith [abs_nonneg z.im])
  · intro z hz
    have hz' : |z.im| < β := by linarith [abs_nonneg z.im]
    exact besselInterp_neg hβpos hz'
  · intro z hz
    exact besselInterp_conj hβpos hz
  · intro t u hu
    simpa [cEnvelope] using hratio β hβlarge t u hu
  · refine ⟨K, fun t u hu => ?_⟩
    have h := hstrip t u hu
    have he : Real.exp (-|t|) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
    calc ‖besselInterp β ((t : ℂ) + u * I)‖ ≤ K * Real.exp (-|t|) := h
      _ ≤ K := by nlinarith [hK]
  · let B : ℝ → ℝ := fun t => K * Real.exp (-|t|)
    have hBint : Integrable B := by
      have hpoly : Integrable (fun t : ℝ => 2 * K * (1 + t ^ 2)⁻¹) :=
        (integrable_inv_one_add_sq.const_mul (2 * K))
      refine hpoly.mono' (by fun_prop) (Filter.Eventually.of_forall fun t => ?_)
      have he := exp_neg_abs_le t
      have hK' : 0 ≤ K := hK
      dsimp [B]
      calc ‖K * Real.exp (-|t|)‖ = K * Real.exp (-|t|) := by
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK' (Real.exp_pos _).le)]
        _ ≤ K * (2 * (1 + t ^ 2)⁻¹) := mul_le_mul_of_nonneg_left he hK'
        _ = 2 * K * (1 + t ^ 2)⁻¹ := by ring
    have hBtendsto : Tendsto B (cocompact ℝ) (𝓝 0) := by
      rw [cocompact_eq_atBot_atTop, tendsto_sup]
      constructor
      · dsimp [B]
        simpa [Real.norm_eq_abs] using
          (tendsto_const_nhds.mul
            (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_abs_atBot_atTop))
      · dsimp [B]
        simpa [Real.norm_eq_abs] using
          (tendsto_const_nhds.mul
            (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_abs_atTop_atTop))
    refine ⟨B, hBint, hBtendsto, fun t u hu => ?_⟩
    simpa [B] using hstrip t u hu
  · intro u
    exact congrArg (fun x : ℝ => x / β) (cEnvelope_neg C u)
  · simp [cEnvelope]

/-- The Bessel interpolation satisfies the two logarithmic-derivative translation bounds. -/
theorem exists_hasLogDerivBounds_besselInterp :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 ≤ C ∧ ∀ β : ℝ, β₀ ≤ β →
      HasLogDerivBounds (besselInterp β) (β / 2)
        (fun u => C / β * Real.exp (2 * Real.pi * |u|)) := by
  obtain ⟨β₀, C, hβ₀, hC, h⟩ := logDeriv_besselInterp_translate_sub_le
  refine ⟨β₀, C, hβ₀, hC, ?_⟩
  intro β hβ
  refine ⟨?_, ?_⟩
  · intro t u hu
    exact (h β hβ t u hu).1
  · intro t u hu
    exact (h β hβ t u hu).2

/-- The Bessel interpolation has curvature of order `β⁻¹` for all sufficiently large `β`. -/
theorem exists_hasCurvatureBound_besselInterp :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 ≤ C ∧ ∀ β : ℝ, β₀ ≤ β →
      HasCurvatureBound (besselInterp β) (C / β) := by
  let β₀ := max 1 (2 * debyeConst)
  let C := 20 + 2 * debyeConst * kernelConst2 * (3 * latticeSum)
  have hβ₀ : 0 < β₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC : 0 ≤ C := by
    have hD := debyeConst_pos
    have hK := kernelConst2_nonneg
    have hL := latticeSum_nonneg
    dsimp [C]
    positivity
  refine ⟨β₀, C, hβ₀, hC, ?_⟩
  intro β hβ₀β
  have hβ1 : 1 ≤ β := le_trans (le_max_left _ _) hβ₀β
  have hβD : 2 * debyeConst ≤ β := le_trans (le_max_right _ _) hβ₀β
  have hβpos : 0 < β := lt_of_lt_of_le zero_lt_one hβ1
  let F : ℝ → ℝ := fun x => (interpLog β x).re
  let F' : ℝ → ℝ := fun x => (interpLogDeriv β x).re
  let F'' : ℝ → ℝ := fun x => (interpLogDeriv2 β x).re
  have hF : ∀ x, HasDerivAt F (F' x) x := by
    intro x
    have hx : |(x : ℂ).im| < β := by simpa using hβpos
    exact (hasDerivAt_interpLog hβpos hx).real_of_complex
  have hF' : ∀ x, HasDerivAt F' (F'' x) x := by
    intro x
    have hx : |(x : ℂ).im| < β := by simpa using hβpos
    exact (hasDerivAt_interpLogDeriv hβpos hx).real_of_complex
  have hsecond : ∀ x, |F'' x| ≤ C / β := by
    intro x
    have hcoeff : ∀ n : ℤ, |logDefect β n| ≤ 2 * debyeConst / β :=
      fun n => abs_logDefect_le_of_le hβD n
    have hdef := norm_defectSeriesDeriv2_le hcoeff (x : ℂ)
    simp only [ofReal_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at hdef
    have hdebye := norm_debyeLogDeriv2_le hβ1 (show |(x : ℂ).im| ≤ β / 2 from by
      simp only [Complex.ofReal_im, abs_zero]
      exact div_nonneg hβpos.le (by norm_num))
    have hnorm : ‖interpLogDeriv2 β (x : ℂ)‖ ≤ C / β := by
      rw [interpLogDeriv2]
      calc
        ‖debyeLogDeriv2 β (x : ℂ) + defectSeriesDeriv2 β (x : ℂ)‖ ≤
            ‖debyeLogDeriv2 β (x : ℂ)‖ + ‖defectSeriesDeriv2 β (x : ℂ)‖ := norm_add_le _ _
        _ ≤ 20 / β + (2 * debyeConst / β) * kernelConst2 * (3 * latticeSum) :=
            add_le_add hdebye hdef
        _ = C / β := by dsimp [C]; ring
    exact (abs_re_le_norm _).trans hnorm
  have hvalue (x : ℝ) : (besselInterp β x).re = Real.exp (F x) := by
    have hx : |(x : ℂ).im| < β := by simpa using hβpos
    have hreal := besselInterp_ofReal_im_eq_zero_and_re_pos hβpos x
    have hvalreal : besselInterp β x = ((besselInterp β x).re : ℂ) :=
      Complex.ext rfl hreal.1
    have hnorm : ‖besselInterp β x‖ = Real.exp (F x) := by
      rw [besselInterp_eq_exp_interpLog hβpos hx, Complex.norm_exp]
    rw [hvalreal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hreal.2] at hnorm
    exact hnorm
  have hlog (x : ℝ) : Real.log (besselInterp β x).re = F x := by
    rw [hvalue, Real.log_exp]
  have hlogDeriv (x : ℝ) : (logDeriv (besselInterp β) x).re = F' x := by
    have hx : |(x : ℂ).im| < β := by simpa using hβpos
    rw [logDeriv_besselInterp hβpos hx]
  intro t s
  have ht := tangent_lower_bound F F' F'' hF hF' hsecond t s
  have hM : 0 ≤ C / β := div_nonneg hC hβpos.le
  calc
    Real.log (besselInterp β t).re + (logDeriv (besselInterp β) t).re * s - C / β * s ^ 2
        ≤ F t + F' t * s - (C / β) / 2 * s ^ 2 := by
          rw [hlog t, hlogDeriv t]
          nlinarith [mul_nonneg hM (sq_nonneg s)]
    _ ≤ F (t + s) := ht
    _ = Real.log (besselInterp β ((t + s : ℝ) : ℂ)).re := (hlog (t + s)).symm

end FroehlichSpencer.BKT.Generic

end
