/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.StripWeight
public import FroehlichSpencer.BKT.Generic.Instances.Bessel
public import FroehlichSpencer.BKT.SOS.Interp.Translation
public import FroehlichSpencer.BKT.Rotator.Contour.Factor

/-!
# The Appendix C strip-weight instance

The SOS interpolation is a strip weight on FS81's closed strip
`|Im z| ≤ β⁻¹ᐟ³/2`, for `0 < β ≤ 1`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex Filter Topology
open scoped Real
open FroehlichSpencer.BKT.SOS.Interp
open FroehlichSpencer.BKT.Rotator.BesselInterp
open FroehlichSpencer.BKT.Rotator.Contour

/-! ## Reflection and evenness -/

private theorem sosRoot_neg (β : ℝ) (z : ℂ) : sosRoot β (-z) = sosRoot β z := by
  unfold sosRoot
  rw [neg_sq]

theorem sosSeries_neg (β : ℝ) (z : ℂ) : sosSeries β (-z) = sosSeries β z := by
  change ∑' n : ℤ, (sosDefect β n : ℂ) * sincSq (-z - n) = _
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [Equiv.neg_apply, sosDefect_neg, Int.cast_neg]
  rw [show -z - -(n : ℂ) = -(z - n) by ring, sincSq_neg]

theorem sosSeries_conj (β : ℝ) (z : ℂ) :
    (starRingEnd ℂ) (sosSeries β z) = sosSeries β ((starRingEnd ℂ) z) := by
  change (starRingEnd ℂ) (∑' n : ℤ, (sosDefect β n : ℂ) * sincSq (z - n)) = _
  rw [Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  rw [map_mul, Complex.conj_ofReal, starRingEnd_apply, sincSq_conj]
  congr 1
  simp

private theorem sosRoot_conj {β : ℝ} (hβ : 0 ≤ β) {z : ℂ}
    (hz : β ^ (1 / 3 : ℝ) * |z.im| ≤ 1 / 2) :
    (starRingEnd ℂ) (sosRoot β z) = sosRoot β ((starRingEnd ℂ) z) := by
  have hstrip : β ^ (1 / 3 : ℝ) * |z.im| < 1 := by linarith
  have hbase : 1 + sosB β * z ^ 2 ∈ slitPlane := one_add_sosB_mem_slitPlane hβ hstrip
  have hn : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num
  have hbaseconj : (starRingEnd ℂ) (1 + sosB β * z ^ 2) =
      1 + sosB β * ((starRingEnd ℂ) z) ^ 2 := by
    simp [sosB, map_add, map_mul, map_pow]
  have h := (Complex.conj_cpow (1 + sosB β * z ^ 2) (1 / 2 : ℂ)
    (Complex.slitPlane_arg_ne_pi hbase)).symm
  have h' : (starRingEnd ℂ) ((1 + sosB β * z ^ 2) ^ (1 / 2 : ℂ)) =
      ((starRingEnd ℂ) (1 + sosB β * z ^ 2)) ^ (1 / 2 : ℂ) := by
    simpa only [starRingEnd_apply, hn] using h
  rw [hbaseconj] at h'
  simpa only [sosRoot] using h'

private theorem sosLog_neg (β : ℝ) (z : ℂ) : sosLog β (-z) = sosLog β z := by
  unfold sosLog
  rw [sosRoot_neg, sosSeries_neg]

private theorem sosLog_conj {β : ℝ} (hβ : 0 ≤ β) {z : ℂ}
    (hz : β ^ (1 / 3 : ℝ) * |z.im| ≤ 1 / 2) :
    (starRingEnd ℂ) (sosLog β z) = sosLog β ((starRingEnd ℂ) z) := by
  have hroot := sosRoot_conj hβ hz
  have hB : (starRingEnd ℂ) (sosB β) = sosB β := by simp [sosB]
  unfold sosLog
  rw [map_sub, map_mul, map_neg, hB, hroot, sosSeries_conj]

theorem sosInterp_neg {β : ℝ} (z : ℂ) : sosInterp β (-z) = sosInterp β z := by
  rw [sosInterp_eq_exp_sosLog β (-z), sosInterp_eq_exp_sosLog β z, sosLog_neg]

theorem sosInterp_conj {β : ℝ} (hβ : 0 ≤ β) {z : ℂ}
    (hz : β ^ (1 / 3 : ℝ) * |z.im| ≤ 1 / 2) :
    (starRingEnd ℂ) (sosInterp β z) = sosInterp β ((starRingEnd ℂ) z) := by
  rw [sosInterp_eq_exp_sosLog β z, sosInterp_eq_exp_sosLog β ((starRingEnd ℂ) z)]
  calc
    (starRingEnd ℂ) (Complex.exp (sosLog β z)) =
        Complex.exp ((starRingEnd ℂ) (sosLog β z)) := (Complex.exp_conj _).symm
    _ = Complex.exp (sosLog β ((starRingEnd ℂ) z)) := by rw [sosLog_conj hβ hz]

/-! ## The contour-end majorant -/

private lemma sos_width_constraint {β : ℝ} (hβ : 0 < β) {u : ℝ}
    (hu : |u| ≤ (1 / 2 : ℝ) * β ^ (-(1 / 3 : ℝ))) :
    β ^ (1 / 3 : ℝ) * |u| ≤ 1 / 2 := by
  have hp : 0 < β ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hβ _
  have hcancel : β ^ (1 / 3 : ℝ) * β ^ (-(1 / 3 : ℝ)) = 1 := by
    rw [Real.rpow_neg hβ.le]
    exact mul_inv_cancel₀ hp.ne'
  calc
    β ^ (1 / 3 : ℝ) * |u| ≤ β ^ (1 / 3 : ℝ) * ((1 / 2 : ℝ) * β ^ (-(1 / 3 : ℝ))) :=
      mul_le_mul_of_nonneg_left hu (Real.rpow_nonneg hβ.le _)
    _ = 1 / 2 := by
      calc
        _ = (1 / 2 : ℝ) * (β ^ (1 / 3 : ℝ) * β ^ (-(1 / 3 : ℝ))) := by ring
        _ = 1 / 2 := by rw [hcancel, mul_one]

private lemma cEnvelope_bound_of_width {C W u : ℝ} (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hu : |u| ≤ W) : cEnvelope C u ≤ C * Real.exp (2 * Real.pi * W) := by
  unfold cEnvelope
  split_ifs with hsmall
  · have hu2 : u ^ 2 ≤ 1 := by
      rw [← sq_abs u]
      simpa using pow_le_pow_left₀ (abs_nonneg u) hsmall 2
    have hexp : 1 ≤ Real.exp (2 * Real.pi * W) := Real.one_le_exp (by positivity)
    calc C * u ^ 2 ≤ C * 1 := mul_le_mul_of_nonneg_left hu2 hC
      _ ≤ C * Real.exp (2 * Real.pi * W) := mul_le_mul_of_nonneg_left hexp hC
  · apply mul_le_mul_of_nonneg_left _ hC
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]

private lemma sos_real_axis_bound {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    ‖sosInterp β t‖ ≤ 2 * Real.exp (β ^ (2 / 3 : ℝ) * 2 * (3 * latticeSum)) *
      (1 + (β * t) ^ 2)⁻¹ := by
  let b := β ^ (2 / 3 : ℝ)
  rw [sosInterp_ofReal hβ.le, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
  have hS : -∑' n : ℤ, sosDefect β n * Real.sinc (Real.pi * (t - n)) ^ 2 ≤
      b * 2 * (3 * latticeSum) := by
    have h := norm_sosSeries_ofReal_le hβ.le t
    rw [sosSeries_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
    exact (neg_le_abs _).trans (by simpa [b] using h)
  have hL := exp_sosDebyeExponent_le hβ.le t
  have he := exp_neg_abs_le (β * t)
  rw [abs_mul, abs_of_pos hβ] at he
  calc Real.exp (-(β ^ (2 / 3 : ℝ)) * Real.sqrt (1 + β ^ (2 / 3 : ℝ) * t ^ 2)) *
        Real.exp (-∑' n : ℤ, sosDefect β n * Real.sinc (Real.pi * (t - n)) ^ 2)
      ≤ Real.exp (-(β * |t|)) * Real.exp (b * 2 * (3 * latticeSum)) := by
        exact mul_le_mul (by simpa [b] using hL) (Real.exp_le_exp.mpr hS)
          (Real.exp_pos _).le (Real.exp_pos _).le
    _ ≤ 2 * (1 + (β * t) ^ 2)⁻¹ * Real.exp (b * 2 * (3 * latticeSum)) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = 2 * Real.exp (β ^ (2 / 3 : ℝ) * 2 * (3 * latticeSum)) *
        (1 + (β * t) ^ 2)⁻¹ := by ring

private theorem sosInterp_strip_bound {β C : ℝ} (hβ : 0 < β)
    (hC : 0 ≤ C) (htrans : ∀ t u : ℝ,
      β ^ (1 / 3 : ℝ) * |u| ≤ 1 / 2 →
      ‖sosInterp β ((t : ℂ) + (u : ℂ) * I) / sosInterp β t‖ ≤
        Real.exp (β ^ (2 / 3 : ℝ) * cEnvelope C u)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t u : ℝ,
      |u| ≤ (1 / 2 : ℝ) * β ^ (-(1 / 3 : ℝ)) →
      ‖sosInterp β ((t : ℂ) + (u : ℂ) * I)‖ ≤ K * (1 + (β * t) ^ 2)⁻¹ := by
  let b := β ^ (2 / 3 : ℝ)
  let W := (1 / 2 : ℝ) * β ^ (-(1 / 3 : ℝ))
  let B := Real.exp (b * 2 * (3 * latticeSum))
  let K := 2 * B * Real.exp (b * C * Real.exp (2 * Real.pi * W))
  have hb : 0 ≤ b := Real.rpow_nonneg hβ.le _
  have hW : 0 ≤ W := by positivity
  have hK : 0 ≤ K := by positivity
  refine ⟨K, hK, fun t u hu => ?_⟩
  have ha := sos_width_constraint hβ hu
  have hcost := cEnvelope_bound_of_width hC hW hu
  have hr := htrans t u ha
  have hreal := sos_real_axis_bound hβ t
  have hden : 0 ≤ (1 + (β * t) ^ 2)⁻¹ := by positivity
  have hratio : ‖sosInterp β ((t : ℂ) + (u : ℂ) * I)‖ =
      ‖sosInterp β ((t : ℂ) + (u : ℂ) * I) / sosInterp β t‖ * ‖sosInterp β t‖ := by
    rw [norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (sosInterp_ne_zero β t))]
  calc
    ‖sosInterp β ((t : ℂ) + (u : ℂ) * I)‖ ≤
        Real.exp (b * cEnvelope C u) *
          (2 * Real.exp (b * 2 * (3 * latticeSum)) * (1 + (β * t) ^ 2)⁻¹) := by
      rw [hratio]
      exact mul_le_mul hr hreal (norm_nonneg _) (by positivity)
    _ ≤ Real.exp (b * C * Real.exp (2 * Real.pi * W)) *
          (2 * Real.exp (b * 2 * (3 * latticeSum)) * (1 + (β * t) ^ 2)⁻¹) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply Real.exp_le_exp.mpr
      calc b * cEnvelope C u ≤ b * (C * Real.exp (2 * Real.pi * W)) :=
            mul_le_mul_of_nonneg_left hcost hb
        _ = b * C * Real.exp (2 * Real.pi * W) := by ring
    _ = K * (1 + (β * t) ^ 2)⁻¹ := by dsimp [K, B, b]; ring

/-- The Appendix C interpolation is a strip weight for `0 < β ≤ 1`. -/
theorem exists_isStripWeight_sosInterp :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, 0 < β → β ≤ 1 →
      IsStripWeight (sosInterp β) ((1 / 2 : ℝ) * β ^ (-(1 / 3 : ℝ)))
        (fun u => β ^ (2 / 3 : ℝ) * cEnvelope C u) := by
  obtain ⟨C, hC, htrans⟩ := norm_sosInterp_translate_div_le_sharp
  refine ⟨C, hC, fun β hβ hβ1 => ?_⟩
  let W := (1 / 2 : ℝ) * β ^ (-(1 / 3 : ℝ))
  have hW : 0 ≤ W := by positivity
  obtain ⟨K, hK, hstrip⟩ := sosInterp_strip_bound hβ hC
    (fun t u hu => htrans β hβ hβ1 t u hu)
  refine
    { width_nonneg := hW
      ofReal_im := fun x => (sosInterp_ofReal_im_eq_zero_and_re_pos hβ.le x).1
      ofReal_re_pos := fun x => (sosInterp_ofReal_im_eq_zero_and_re_pos hβ.le x).2
      analyticAt := fun z hz => analyticAt_sosInterp hβ.le (sos_width_constraint hβ hz)
      even := fun z _ => sosInterp_neg z
      conj := fun z hz => sosInterp_conj hβ.le (sos_width_constraint hβ hz)
      ratio_le := fun t u hu => htrans β hβ hβ1 t u (sos_width_constraint hβ hu)
      bounded := ?_
      majorant := ?_
      cost_even := fun u => by rw [cEnvelope_neg]
      cost_zero := by simp [cEnvelope] }
  · refine ⟨K, fun t u hu => ?_⟩
    have h := hstrip t u hu
    have hden : 1 ≤ 1 + (β * t) ^ 2 := by nlinarith [sq_nonneg (β * t)]
    calc ‖sosInterp β ((t : ℂ) + (u : ℂ) * I)‖ ≤ K * (1 + (β * t) ^ 2)⁻¹ := h
      _ ≤ K := by simpa using mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hden) hK
  · let B : ℝ → ℝ := fun t => K * (1 + (β * t) ^ 2)⁻¹
    have hBint : Integrable B := by
      have h := (integrable_inv_one_add_sq.comp_mul_left' hβ.ne').const_mul K
      simpa [B] using h
    have hsq : Tendsto (fun t : ℝ => t ^ 2) (cocompact ℝ) atTop := by
      have h := (tendsto_pow_atTop (two_ne_zero (α := ℕ))).comp
        (tendsto_norm_cocompact_atTop (E := ℝ))
      refine h.congr fun t => ?_
      simp [Real.norm_eq_abs, sq_abs]
    have hden : Tendsto (fun t : ℝ => 1 + (β * t) ^ 2) (cocompact ℝ) atTop :=
      tendsto_atTop_mono (fun t => by nlinarith [sq_nonneg (β * t)])
        (hsq.const_mul_atTop (sq_pos_of_pos hβ))
    have hinv : Tendsto (fun t : ℝ => (1 + (β * t) ^ 2)⁻¹) (cocompact ℝ) (𝓝 0) := by
      simpa only [Function.comp_def] using (tendsto_inv_atTop_zero.comp hden)
    have hBlim : Tendsto B (cocompact ℝ) (𝓝 0) := by
      have hKconst : Tendsto (fun _ : ℝ => K) (cocompact ℝ) (𝓝 K) := tendsto_const_nhds
      simpa [B] using hKconst.mul hinv
    refine ⟨B, hBint, hBlim, fun t u hu => ?_⟩
    simpa [B] using hstrip t u hu

/-- The SOS interpolation satisfies the two logarithmic-derivative translation bounds. -/
theorem exists_hasLogDerivBounds_sosInterp :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, 0 < β → β ≤ 1 →
      HasLogDerivBounds (sosInterp β) ((1 / 2 : ℝ) * β ^ (-(1 / 3 : ℝ)))
        (fun u => C * β ^ (2 / 3 : ℝ) * Real.exp (2 * Real.pi * |u|)) := by
  obtain ⟨C, hC, h⟩ := logDeriv_sosInterp_translate_sub_le
  refine ⟨C, hC, fun β hβ hβ1 => ?_⟩
  let W := (1 / 2 : ℝ) * β ^ (-(1 / 3 : ℝ))
  refine ⟨?_, ?_⟩
  · intro t u hu
    exact (h β hβ hβ1 t u (sos_width_constraint hβ hu)).1
  · intro t u hu
    exact (h β hβ hβ1 t u (sos_width_constraint hβ hu)).2

private theorem tangent_lower_bound_sos (F F' F'' : ℝ → ℝ) {M : ℝ}
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

/-- The SOS interpolation has real-axis curvature of order `β^{2/3}` for `0 < β ≤ 1`. -/
theorem exists_hasCurvatureBound_sosInterp :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, 0 < β → β ≤ 1 →
      HasCurvatureBound (sosInterp β) (C * β ^ (2 / 3 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := norm_deriv_logDeriv_sosInterp_ofReal_le
  refine ⟨C, hC, fun β hβ hβ1 => ?_⟩
  let F : ℝ → ℝ := fun x => (sosLog β x).re
  let F' : ℝ → ℝ := fun x => (sosLogDeriv β x).re
  let F'' : ℝ → ℝ := fun x => (sosLogDeriv2 β x).re
  have hF : ∀ x, HasDerivAt F (F' x) x := by
    intro x
    have hx : β ^ (1 / 3 : ℝ) * |(x : ℂ).im| < 1 := by simp
    exact (hasDerivAt_sosLog hβ.le hx).real_of_complex
  have hF' : ∀ x, HasDerivAt F' (F'' x) x := by
    intro x
    have hx : β ^ (1 / 3 : ℝ) * |(x : ℂ).im| < 1 := by simp
    exact (hasDerivAt_sosLogDeriv hβ.le hx).real_of_complex
  have hsecond : ∀ x, |F'' x| ≤ C * β ^ (2 / 3 : ℝ) := by
    intro x
    have hx : β ^ (1 / 3 : ℝ) * |(x : ℂ).im| < 1 := by simp
    have h := hbound β hβ hβ1 x
    rw [deriv_logDeriv_sosInterp hβ.le hx] at h
    exact (abs_re_le_norm _).trans h
  have hvalue (x : ℝ) : (sosInterp β x).re = Real.exp (F x) := by
    have hpos := sosInterp_ofReal_im_eq_zero_and_re_pos hβ.le x
    have hreal : sosInterp β x = ((sosInterp β x).re : ℂ) := Complex.ext rfl hpos.1
    have hnorm : ‖sosInterp β x‖ = Real.exp (F x) := by
      have hx : β ^ (1 / 3 : ℝ) * |(x : ℂ).im| < 1 := by simp
      rw [sosInterp_eq_exp_sosLog β (x : ℂ), Complex.norm_exp]
    rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos.2] at hnorm
    exact hnorm
  have hlog (x : ℝ) : Real.log (sosInterp β x).re = F x := by
    rw [hvalue, Real.log_exp]
  have hlogDeriv (x : ℝ) : (logDeriv (sosInterp β) x).re = F' x := by
    have hx : β ^ (1 / 3 : ℝ) * |(x : ℂ).im| < 1 := by simp
    rw [logDeriv_sosInterp hβ.le hx]
  have hM : 0 ≤ C * β ^ (2 / 3 : ℝ) :=
    mul_nonneg hC (Real.rpow_nonneg hβ.le _)
  intro t s
  have ht := tangent_lower_bound_sos F F' F'' hF hF' hsecond t s
  calc
    Real.log (sosInterp β t).re + (logDeriv (sosInterp β) t).re * s -
        (C * β ^ (2 / 3 : ℝ)) * s ^ 2
      ≤ F t + F' t * s - (C * β ^ (2 / 3 : ℝ)) / 2 * s ^ 2 := by
        rw [hlog t, hlogDeriv t]
        nlinarith [mul_nonneg hM (sq_nonneg s)]
    _ ≤ F (t + s) := ht
    _ = Real.log (sosInterp β ((t + s : ℝ) : ℂ)).re := (hlog (t + s)).symm

end FroehlichSpencer.BKT.Generic

end
