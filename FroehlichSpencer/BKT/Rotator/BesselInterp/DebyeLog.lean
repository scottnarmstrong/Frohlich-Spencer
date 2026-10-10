/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.BesselInterp.Debye
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# An explicit holomorphic logarithm of the Debye factor

On the strip `|Im z| < β`, with `w = z/β`, the Debye factor `L_β` of FS81 J p.599 is `exp ℓ`, where

`ℓ(z) = -½ log 2π - ½ log β - ¼ Log(1 + w²) + β (1 + w²)^{1/2} - z sinh⁻¹ w`

(principal branches). Its derivatives are `ℓ' = -w/(2β(1+w²)) - sinh⁻¹ w` and
`ℓ'' = -(1-w²)/(2β²(1+w²)²) - 1/(β(1+w²)^{1/2})`. On `|Im z| ≤ β/2` one has `‖ℓ''‖ ≤ 20/β` for
`β ≥ 1`; on the real axis `ℓ'` is real. These are the inputs to FS81 (B.13) and to the
`L_β`-parts of properties (c), (d) (J p.576). The file also records the exponential decay of
`L_β` on the real axis used for integrability in property (b).
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.BesselInterp

open Complex
open scoped Real

/-- The explicit holomorphic logarithm `ℓ` of the Debye factor `L_β` on the strip `|Im z| < β`. -/
def debyeLog (β : ℝ) (z : ℂ) : ℂ :=
  -(1 / 2 : ℂ) * Real.log (2 * π) - (1 / 2 : ℂ) * Real.log β
    - (1 / 4 : ℂ) * Complex.log (1 + (z / β) ^ 2)
    + β * (1 + (z / β) ^ 2) ^ (1 / 2 : ℂ) - z * carsinh (z / β)

/-- The derivative `ℓ'` of `debyeLog`. -/
def debyeLogDeriv (β : ℝ) (z : ℂ) : ℂ :=
  -(z / β) / (2 * β * (1 + (z / β) ^ 2)) - carsinh (z / β)

/-- The second derivative `ℓ''` of `debyeLog`. -/
def debyeLogDeriv2 (β : ℝ) (z : ℂ) : ℂ :=
  -(1 - (z / β) ^ 2) / (2 * β ^ 2 * (1 + (z / β) ^ 2) ^ 2)
    - 1 / (β * (1 + (z / β) ^ 2) ^ (1 / 2 : ℂ))

/-! ### Algebra of the principal square root on the strip -/

lemma one_add_sq_ne_zero {w : ℂ} (hw : |w.im| < 1) : 1 + w ^ 2 ≠ 0 :=
  slitPlane_ne_zero (one_add_sq_mem_slitPlane hw)

lemma half_cpow_ne_zero {w : ℂ} (hw : |w.im| < 1) : (1 + w ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
  intro h
  have := half_cpow_re_pos (one_add_sq_mem_slitPlane hw)
  rw [h, zero_re] at this
  exact lt_irrefl _ this

lemma add_half_cpow_ne_zero {w : ℂ} (hw : |w.im| < 1) : w + (1 + w ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
  intro h
  have := add_sqrt_re_pos hw
  rw [h, zero_re] at this
  exact lt_irrefl _ this

/-- `Log (1+w²)^{1/2} = ½ Log (1+w²)` (principal branches). -/
lemma log_half_cpow {u : ℂ} (hu : u ≠ 0) :
    Complex.log (u ^ (1 / 2 : ℂ)) = (1 / 2 : ℂ) * Complex.log u := by
  rw [cpow_def_of_ne_zero hu, Complex.log_exp]
  · ring
  · have him : (Complex.log u * (1 / 2 : ℂ)).im = Complex.arg u / 2 := by
      simp only [mul_im, log_im, one_div, inv_re, inv_im, re_ofNat, im_ofNat, normSq_ofNat]
      ring
    rw [him]
    linarith [neg_pi_lt_arg u, Real.pi_pos]
  · have him : (Complex.log u * (1 / 2 : ℂ)).im = Complex.arg u / 2 := by
      simp only [mul_im, log_im, one_div, inv_re, inv_im, re_ofNat, im_ofNat, normSq_ofNat]
      ring
    rw [him]
    linarith [arg_le_pi u, Real.pi_pos]

/-! ### `L_β = exp ℓ` -/

theorem debye_eq_exp_debyeLog {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : |z.im| < β) :
    debye β z = Complex.exp (debyeLog β z) := by
  have hw := im_div_ofReal_lt hβ hz
  set w := z / (β : ℂ) with hwdef
  have hu0 := one_add_sq_ne_zero hw
  have hs0 := half_cpow_ne_zero hw
  have hdiv : 1 + z ^ 2 / (β : ℂ) ^ 2 = 1 + w ^ 2 := by rw [hwdef, div_pow]
  have h1 : ((Real.sqrt (2 * π))⁻¹ : ℂ) = Complex.exp (-(1 / 2 : ℂ) * Real.log (2 * π)) := by
    have hpos : (0 : ℝ) < 2 * π := by positivity
    have : (Real.sqrt (2 * π))⁻¹ = Real.exp (-(1 / 2) * Real.log (2 * π)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos, ← Real.exp_neg]
      ring_nf
    rw [← Complex.ofReal_inv, this, Complex.ofReal_exp]
    push_cast
    ring_nf
  have hbs0 : (β : ℂ) * (1 + w ^ 2) ^ (1 / 2 : ℂ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hβ.ne') hs0
  have h2 : ((β : ℂ) * (1 + w ^ 2) ^ (1 / 2 : ℂ)) ^ (-(1 / 2) : ℂ) =
      Complex.exp (Complex.log ((β : ℂ) * (1 + w ^ 2) ^ (1 / 2 : ℂ)) * (-(1 / 2))) :=
    cpow_def_of_ne_zero hbs0 _
  have h3 : Complex.log ((β : ℂ) * (1 + w ^ 2) ^ (1 / 2 : ℂ)) =
      Real.log β + (1 / 2 : ℂ) * Complex.log (1 + w ^ 2) := by
    rw [log_ofReal_mul hβ hs0, log_half_cpow hu0]
  unfold debye debyeLog
  rw [hdiv, h1, h2, h3, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-! ### The real axis -/

theorem debyeLogDeriv_ofReal_im {β : ℝ} (hβ : 0 < β) (x : ℝ) : (debyeLogDeriv β x).im = 0 := by
  have hβ' : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have h : debyeLogDeriv β x =
      ((-(x / β) / (2 * β * (1 + (x / β) ^ 2)) - Real.arsinh (x / β) : ℝ) : ℂ) := by
    unfold debyeLogDeriv
    rw [show (x : ℂ) / β = ((x / β : ℝ) : ℂ) by push_cast; rfl, carsinh_ofReal]
    push_cast
    ring
  rw [h, ofReal_im]

theorem exists_debyeRe_le_exp_neg_abs {β : ℝ} (hβ : 0 < β) :
    ∃ K : ℝ, ∀ x : ℝ, debyeRe β x ≤ K * Real.exp (-|x|) := by
  set X₀ := β * Real.sinh 2 with hX₀
  have hX₀0 : 0 ≤ X₀ := mul_nonneg hβ.le (Real.sinh_nonneg_iff.mpr (by norm_num))
  refine ⟨(Real.sqrt (2 * π))⁻¹ * β ^ (-(1 / 2) : ℝ) * Real.exp (β + 2 * X₀), fun x => ?_⟩
  have hsq : 1 ≤ Real.sqrt (1 + x ^ 2 / β ^ 2) := by
    rw [Real.one_le_sqrt]; have : 0 ≤ x ^ 2 / β ^ 2 := by positivity
    linarith
  have hsq2 : Real.sqrt (1 + x ^ 2 / β ^ 2) ≤ 1 + |x| / β := by
    rw [Real.sqrt_le_left (by positivity)]
    have : (1 + |x| / β) ^ 2 = 1 + 2 * (|x| / β) + x ^ 2 / β ^ 2 := by
      rw [add_sq, div_pow, sq_abs]; ring
    rw [this]
    have : 0 ≤ |x| / β := by positivity
    linarith
  have hpow : (β * Real.sqrt (1 + x ^ 2 / β ^ 2)) ^ (-(1 / 2) : ℝ) ≤ β ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hβ (le_mul_of_one_le_right hβ.le hsq) (by norm_num)
  have heven : -x * Real.arsinh (x / β) = -|x| * Real.arsinh (|x| / β) := by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, neg_div, Real.arsinh_neg]; ring
  have hexp : -x * Real.arsinh (x / β) + β * Real.sqrt (1 + x ^ 2 / β ^ 2) ≤
      β + 2 * X₀ - |x| := by
    rw [heven]
    have h1 : β * Real.sqrt (1 + x ^ 2 / β ^ 2) ≤ β + |x| := by
      calc β * Real.sqrt (1 + x ^ 2 / β ^ 2) ≤ β * (1 + |x| / β) := by gcongr
        _ = β + |x| := by field_simp
    have h2 : |x| - |x| * Real.arsinh (|x| / β) ≤ 2 * X₀ - |x| := by
      rcases le_or_gt |x| X₀ with h | h
      · have : 0 ≤ Real.arsinh (|x| / β) := Real.arsinh_nonneg_iff.mpr (by positivity)
        nlinarith [abs_nonneg x]
      · have hge : 2 ≤ Real.arsinh (|x| / β) := by
          rw [← Real.arsinh_sinh 2, Real.arsinh_le_arsinh, le_div_iff₀ hβ]
          linarith
        nlinarith [abs_nonneg x]
    linarith
  have hpos : 0 ≤ (Real.sqrt (2 * π))⁻¹ := by positivity
  unfold debyeRe
  calc (Real.sqrt (2 * π))⁻¹ * (β * Real.sqrt (1 + x ^ 2 / β ^ 2)) ^ (-(1 / 2) : ℝ) *
        Real.exp (-x * Real.arsinh (x / β) + β * Real.sqrt (1 + x ^ 2 / β ^ 2))
      ≤ (Real.sqrt (2 * π))⁻¹ * β ^ (-(1 / 2) : ℝ) * Real.exp (β + 2 * X₀ - |x|) := by
        gcongr
    _ = (Real.sqrt (2 * π))⁻¹ * β ^ (-(1 / 2) : ℝ) * Real.exp (β + 2 * X₀) * Real.exp (-|x|) := by
        rw [sub_eq_add_neg, Real.exp_add]; ring

/-! ### Derivatives -/

lemma hasDerivAt_one_add_div_sq (β : ℝ) (z : ℂ) :
    HasDerivAt (fun z : ℂ => 1 + (z / β) ^ 2) (2 * (z / β) / β) z := by
  have h := (((hasDerivAt_id' z).div_const (β : ℂ)).pow 2).const_add 1
  convert h using 1
  push_cast
  ring

lemma hasDerivAt_half_cpow_div {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : |z.im| < β) :
    HasDerivAt (fun z : ℂ => (1 + (z / β) ^ 2) ^ (1 / 2 : ℂ))
      ((z / β) * (1 + (z / β) ^ 2) ^ (1 / 2 : ℂ) / (β * (1 + (z / β) ^ 2))) z := by
  have hw := im_div_ofReal_lt hβ hz
  have hu0 := one_add_sq_ne_zero hw
  have hβ' : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have h := (hasDerivAt_one_add_div_sq β z).cpow_const (c := (1 / 2 : ℂ))
    (one_add_sq_mem_slitPlane hw)
  convert h using 1
  rw [cpow_sub _ _ hu0, cpow_one]
  field_simp

lemma hasDerivAt_carsinh_div {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : |z.im| < β) :
    HasDerivAt (fun z : ℂ => carsinh (z / β)) (1 / (β * (1 + (z / β) ^ 2) ^ (1 / 2 : ℂ))) z := by
  have hw := im_div_ofReal_lt hβ hz
  have hu0 := one_add_sq_ne_zero hw
  have hs0 := half_cpow_ne_zero hw
  have hws0 := add_half_cpow_ne_zero hw
  have hβ' : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have hsq : ((1 + (z / β) ^ 2) ^ (1 / 2 : ℂ)) ^ 2 = 1 + (z / β) ^ 2 := half_cpow_sq _
  have hf : HasDerivAt (fun z : ℂ => z / β + (1 + (z / β) ^ 2) ^ (1 / 2 : ℂ))
      (1 / β + (z / β) * (1 + (z / β) ^ 2) ^ (1 / 2 : ℂ) / (β * (1 + (z / β) ^ 2))) z :=
    ((hasDerivAt_id' z).div_const (β : ℂ)).add (hasDerivAt_half_cpow_div hβ hz)
  have h := hf.clog (mem_slitPlane_iff.mpr (Or.inl (add_sqrt_re_pos hw)))
  unfold carsinh
  convert h using 1
  set w := z / (β : ℂ) with hwdef
  set s := (1 + w ^ 2) ^ (1 / 2 : ℂ) with hsdef
  clear_value s w
  rw [← hsq]
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs0
  field_simp
  ring

theorem hasDerivAt_debyeLog {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : |z.im| < β) :
    HasDerivAt (debyeLog β) (debyeLogDeriv β z) z := by
  have hw := im_div_ofReal_lt hβ hz
  have hu0 := one_add_sq_ne_zero hw
  have hs0 := half_cpow_ne_zero hw
  have hβ' : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have hsq : ((1 + (z / β) ^ 2) ^ (1 / 2 : ℂ)) ^ 2 = 1 + (z / β) ^ 2 := half_cpow_sq _
  have hlog := (hasDerivAt_one_add_div_sq β z).clog (one_add_sq_mem_slitPlane hw)
  have h := ((((hasDerivAt_const z (-(1 / 2 : ℂ) * Real.log (2 * π))).sub
    (hasDerivAt_const z ((1 / 2 : ℂ) * Real.log β))).sub (hlog.const_mul (1 / 4 : ℂ))).add
    ((hasDerivAt_half_cpow_div hβ hz).const_mul (β : ℂ))).sub
    ((hasDerivAt_id' z).mul (hasDerivAt_carsinh_div hβ hz))
  unfold debyeLog debyeLogDeriv
  convert h using 1
  have hz' : z = (z / β) * β := by field_simp
  set w := z / (β : ℂ) with hwdef
  set s := (1 + w ^ 2) ^ (1 / 2 : ℂ) with hsdef
  clear_value s w
  rw [hz', ← hsq]
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs0
  field_simp
  ring

theorem hasDerivAt_debyeLogDeriv {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : |z.im| < β) :
    HasDerivAt (debyeLogDeriv β) (debyeLogDeriv2 β z) z := by
  have hw := im_div_ofReal_lt hβ hz
  have hu0 := one_add_sq_ne_zero hw
  have hβ' : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have hg : HasDerivAt (fun z : ℂ => 2 * β * (1 + (z / β) ^ 2)) (2 * β * (2 * (z / β) / β)) z :=
    (hasDerivAt_one_add_div_sq β z).const_mul _
  have hg0 : (2 * β * (1 + (z / β) ^ 2) : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hβ') hu0
  have h := ((((hasDerivAt_id' z).div_const (β : ℂ)).neg).div hg hg0).sub
    (hasDerivAt_carsinh_div hβ hz)
  unfold debyeLogDeriv debyeLogDeriv2
  convert h using 1
  simp only [Pi.neg_apply]
  set w := z / (β : ℂ) with hwdef
  set s := (1 + w ^ 2) ^ (1 / 2 : ℂ) with hsdef
  clear_value s w
  field_simp
  ring

/-! ### The bound `‖ℓ''‖ ≤ 20/β` on `|Im z| ≤ β/2` -/

lemma quarter_le_norm_one_add_sq {w : ℂ} (hw : |w.im| ≤ 1 / 2) : 1 / 4 ≤ ‖1 + w ^ 2‖ := by
  have hfac : 1 + w ^ 2 = (w + I) * (w - I) := by
    have : I ^ 2 = -1 := I_sq
    linear_combination this
  have h1 : 1 / 2 ≤ ‖w + I‖ := by
    refine le_trans ?_ (abs_im_le_norm (w + I))
    rw [add_im, I_im]
    have := abs_le.mp hw
    rw [abs_of_pos (by linarith)]
    linarith
  have h2 : 1 / 2 ≤ ‖w - I‖ := by
    refine le_trans ?_ (abs_im_le_norm (w - I))
    rw [sub_im, I_im]
    have := abs_le.mp hw
    rw [abs_of_neg (by linarith)]
    linarith
  rw [hfac, norm_mul]
  nlinarith [norm_nonneg (w + I), norm_nonneg (w - I)]

theorem norm_debyeLogDeriv2_le {β : ℝ} (hβ : 1 ≤ β) {z : ℂ} (hz : |z.im| ≤ β / 2) :
    ‖debyeLogDeriv2 β z‖ ≤ 20 / β := by
  have hβ0 : 0 < β := by linarith
  have hwim : |(z / β).im| ≤ 1 / 2 := by
    rw [div_ofReal_im, abs_div, abs_of_pos hβ0, div_le_iff₀ hβ0]
    linarith
  set w := z / (β : ℂ) with hwdef
  set u := 1 + w ^ 2 with hudef
  set s := u ^ (1 / 2 : ℂ) with hsdef
  have ha : 1 / 4 ≤ ‖u‖ := quarter_le_norm_one_add_sq hwim
  have hsq : s ^ 2 = u := half_cpow_sq _
  have hb : 1 / 2 ≤ ‖s‖ := by
    have h : ‖s‖ ^ 2 = ‖u‖ := by rw [← norm_pow, hsq]
    nlinarith [norm_nonneg s]
  have hnum : ‖1 - w ^ 2‖ ≤ 2 + ‖u‖ := by
    have : 1 - w ^ 2 = 2 - u := by rw [hudef]; ring
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    simp
  have hβn : ‖(β : ℂ)‖ = β := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0]
  have hu0 : 0 < ‖u‖ := by linarith
  have hs0 : 0 < ‖s‖ := by linarith
  have hT1 : ‖-(1 - w ^ 2) / (2 * (β : ℂ) ^ 2 * u ^ 2)‖ ≤ 18 / β := by
    rw [norm_div, norm_neg, norm_mul, norm_mul, norm_pow, norm_pow, hβn, Complex.norm_two]
    rw [div_le_div_iff₀ (by positivity) hβ0]
    have key : 2 + ‖u‖ ≤ 36 * ‖u‖ ^ 2 := by nlinarith
    have hββ : β ≤ β ^ 2 := by nlinarith
    calc ‖1 - w ^ 2‖ * β ≤ (2 + ‖u‖) * β := by gcongr
      _ ≤ 36 * ‖u‖ ^ 2 * β := by gcongr
      _ ≤ 36 * ‖u‖ ^ 2 * β ^ 2 := by gcongr
      _ = 18 * (2 * β ^ 2 * ‖u‖ ^ 2) := by ring
  have hT2 : ‖1 / ((β : ℂ) * s)‖ ≤ 2 / β := by
    rw [norm_div, norm_one, norm_mul, hβn, div_le_div_iff₀ (by positivity) hβ0]
    nlinarith
  unfold debyeLogDeriv2
  calc ‖-(1 - w ^ 2) / (2 * (β : ℂ) ^ 2 * u ^ 2) - 1 / ((β : ℂ) * s)‖
      ≤ ‖-(1 - w ^ 2) / (2 * (β : ℂ) ^ 2 * u ^ 2)‖ + ‖1 / ((β : ℂ) * s)‖ := norm_sub_le _ _
    _ ≤ 18 / β + 2 / β := add_le_add hT1 hT2
    _ = 20 / β := by ring

end FroehlichSpencer.BKT.Rotator.BesselInterp
