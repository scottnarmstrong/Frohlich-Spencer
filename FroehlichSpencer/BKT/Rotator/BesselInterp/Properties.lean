/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.BesselInterp.Series
public import FroehlichSpencer.BKT.Rotator.CosineFourierSummable
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import FroehlichSpencer.BKT.Rotator.BesselInterp.Vertical
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Properties (a)–(d) of the Appendix B interpolation (FS81 J p.576)

For the literal interpolation `I_β = L_β · exp S_β` of FS81 Appendix B (J p.599):

* it is holomorphic and nonzero on the strip `|Im φ| < β`, in particular analytic and nonzero at
  every point of the closed strip `|Im φ| ≤ β/2` (`analyticAt_besselInterp`,
  `besselInterp_ne_zero`), for every `β > 0`;
* (a) it agrees with the Bessel coefficient at every integer, for every `β > 0`
  (`besselInterp_intCast`, `besselInterp_intCast_eq_rotatorI`);
* (b) it is real, positive and even on the real axis, and integrable there, for every `β > 0`;
* (c) `|I_β(φ+ia)/I_β(φ)| ≤ e^{g(a)/β}` with `g(a) = C a²` for `|a| ≤ 1` and `C e^{2π|a|}` for
  `1 < |a| ≤ β/2`, for all `β ≥ β₀`, real `φ` (`norm_besselInterp_translate_div_le`);
* (d) the first two derivatives of `log (I_β(φ+ia)/I_β(φ))` in `φ`, stated branch-free through the
  logarithmic derivative, are at most `C β⁻¹ e^{2π|a|}` (`logDeriv_besselInterp_translate_sub_le`).

The constants `β₀` and `C` are absolute.
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.BesselInterp

open Complex Metric MeasureTheory
open scoped Real

/-! ### (a) Integer agreement -/

/-- FS81 J p.576 (a): `I_β(m)` is the Bessel coefficient (B.1), for every `β > 0`. -/
theorem besselInterp_intCast {β : ℝ} (hβ : 0 < β) (m : ℤ) :
    besselInterp β m = besselCoeff β m := by
  unfold besselInterp defectFactor defectSeries
  have hsum : ∑' n : ℤ, (logDefect β n : ℂ) * sincSq ((m : ℂ) - n) = logDefect β m := by
    rw [tsum_eq_single m]
    · simp [sincSq_zero]
    · intro n hn
      have : ((m : ℂ) - n) = ((m - n : ℤ) : ℂ) := by push_cast; ring
      rw [this, sincSq_intCast, ite_eq_right (sub_ne_zero.mpr (Ne.symm hn)), mul_zero]
  have hm : ((m : ℂ)) = ((m : ℝ) : ℂ) := by push_cast; rfl
  rw [hsum, hm, debye_ofReal hβ, besselCoeff_eq, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  congr 1
  unfold logDefect
  rw [Real.exp_sub, Real.exp_log (besselCoeffRe_pos hβ m), Real.exp_log (debyeRe_pos hβ _)]
  field_simp [(debyeRe_pos hβ (m : ℝ)).ne']

/-- (a) stated against the plane-rotator coefficient `rotatorI` of FS81 (1.34). -/
theorem besselInterp_intCast_eq_rotatorI {β : ℝ} (hβ : 0 < β) (m : ℤ) :
    besselInterp β m = rotatorI β m := by
  rw [besselInterp_intCast hβ, rotatorI_eq_besselCoeff]

/-! ### (b) The real axis -/

theorem besselInterp_ofReal {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    besselInterp β x = ((debyeRe β x *
      Real.exp (∑' n : ℤ, logDefect β n * Real.sinc (π * (x - n)) ^ 2)) : ℝ) := by
  unfold besselInterp defectFactor
  rw [debye_ofReal hβ, defectSeries_ofReal, ← Complex.ofReal_exp, ← Complex.ofReal_mul]

/-- (b): `I_β` is real and positive on the real axis. -/
theorem besselInterp_ofReal_im_eq_zero_and_re_pos {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    (besselInterp β x).im = 0 ∧ 0 < (besselInterp β x).re := by
  rw [besselInterp_ofReal hβ, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨rfl, mul_pos (debyeRe_pos hβ x) (Real.exp_pos _)⟩

/-- (b): `I_β` is even on the real axis. -/
theorem besselInterp_neg_ofReal {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    besselInterp β (-x : ℝ) = besselInterp β x := by
  rw [besselInterp_ofReal hβ, besselInterp_ofReal hβ, debyeRe_neg]
  congr 3
  rw [← (Equiv.neg ℤ).tsum_eq]
  congr 1
  funext n
  have hc : logDefect β (-n) = logDefect β n := by
    unfold logDefect; rw [besselCoeffRe_neg, Int.cast_neg, debyeRe_neg]
  simp only [Equiv.neg_apply, hc, Int.cast_neg]
  congr 1
  rw [show π * (-x - -(n : ℝ)) = -(π * (x - n)) by ring, Real.sinc_neg]

lemma exp_neg_abs_le (x : ℝ) : Real.exp (-|x|) ≤ 2 * (1 + x ^ 2)⁻¹ := by
  have h := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
  rw [sq_abs] at h
  have h2 : (1 + x ^ 2) / 2 ≤ Real.exp |x| := by nlinarith [abs_nonneg x]
  have hpos : 0 < (1 + x ^ 2) / 2 := by positivity
  calc Real.exp (-|x|) = (Real.exp |x|)⁻¹ := Real.exp_neg _
    _ ≤ ((1 + x ^ 2) / 2)⁻¹ := inv_anti₀ hpos h2
    _ = 2 * (1 + x ^ 2)⁻¹ := by rw [inv_div, div_eq_mul_inv]

/-- (b): `I_β` is integrable on the real axis. -/
theorem integrable_besselInterp {β : ℝ} (hβ : 0 < β) :
    Integrable fun x : ℝ => besselInterp β x := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_logDefect_le hβ
  obtain ⟨K, hK⟩ := exists_debyeRe_le_exp_neg_abs hβ
  have hK0 : 0 ≤ K := by
    have := (debyeRe_pos hβ 0).le.trans (hK 0)
    simpa using this
  have hcont : Continuous fun x : ℝ => besselInterp β x := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have hx : |((x : ℂ)).im| < β := by simpa using hβ
    exact (hasDerivAt_besselInterp hβ hx).continuousAt.comp Complex.continuous_ofReal.continuousAt
  refine Integrable.mono'
    ((integrable_inv_one_add_sq).const_mul (2 * (K * Real.exp (M * 2 * (3 * latticeSum)))))
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have hx : |((x : ℂ)).im| < β := by simpa using hβ
  rw [besselInterp_eq_exp_interpLog hβ hx]
  unfold interpLog
  rw [Complex.exp_add, ← debye_eq_exp_debyeLog hβ hx, norm_mul, debye_ofReal hβ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (debyeRe_pos hβ x), Complex.norm_exp]
  have hS : (defectSeries β x).re ≤ M * 2 * (3 * latticeSum) := by
    have := norm_defectSeries_le hM (x : ℂ)
    simp only [ofReal_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at this
    exact (re_le_norm _).trans this
  calc debyeRe β x * Real.exp (defectSeries β x).re
      ≤ (K * Real.exp (-|x|)) * Real.exp (M * 2 * (3 * latticeSum)) :=
        mul_le_mul (hK x) (Real.exp_le_exp.mpr hS) (Real.exp_pos _).le
          (mul_nonneg hK0 (Real.exp_pos _).le)
    _ ≤ (K * (2 * (1 + x ^ 2)⁻¹)) * Real.exp (M * 2 * (3 * latticeSum)) := by
        gcongr; exact exp_neg_abs_le x
    _ = 2 * (K * Real.exp (M * 2 * (3 * latticeSum))) * (1 + x ^ 2)⁻¹ := by ring

/-! ### The strip -/

/-- `I_β` is analytic at every point of the closed strip `|Im φ| ≤ β/2`, for every `β > 0`. -/
theorem analyticAt_besselInterp {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : |z.im| ≤ β / 2) :
    AnalyticAt ℂ (besselInterp β) z :=
  DifferentiableOn.analyticAt (s := {w : ℂ | |w.im| < β})
    (fun _ hw => (hasDerivAt_besselInterp hβ hw).differentiableAt.differentiableWithinAt)
    ((isOpen_strip β).mem_nhds (show |z.im| < β by linarith))

/-- `I_β` has no zero on the strip `|Im φ| < β`. -/
theorem besselInterp_ne_zero {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : |z.im| < β) :
    besselInterp β z ≠ 0 := by
  rw [besselInterp_eq_exp_interpLog hβ hz]; exact Complex.exp_ne_zero _

/-! ### (c), (d) Translation estimates -/

lemma abs_im_le_of_mem_closedBall {x r : ℝ} {z : ℂ} (hz : z ∈ closedBall (x : ℂ) r) :
    |z.im| ≤ r := by
  have h := abs_im_le_norm (z - x)
  rw [sub_im, ofReal_im, sub_zero] at h
  exact h.trans (by rwa [mem_closedBall, dist_eq_norm] at hz)

lemma one_le_exp_two_pi_abs (a : ℝ) : 1 ≤ Real.exp (2 * π * |a|) :=
  Real.one_le_exp (by positivity)

lemma abs_le_exp_two_pi_abs (a : ℝ) : |a| ≤ Real.exp (2 * π * |a|) := by
  have h := Real.add_one_le_exp (2 * π * |a|)
  nlinarith [Real.two_le_pi, abs_nonneg a]

lemma sq_le_exp_two_pi_abs (a : ℝ) : a ^ 2 ≤ Real.exp (2 * π * |a|) := by
  have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * π * |a| by positivity)
  have hpi : 1 ≤ (2 * π) ^ 2 / 2 := by nlinarith [Real.two_le_pi]
  have h2 : a ^ 2 ≤ (2 * π * |a|) ^ 2 / 2 := by
    rw [mul_pow, ← sq_abs a]
    have : (2 * π) ^ 2 * |a| ^ 2 / 2 = ((2 * π) ^ 2 / 2) * |a| ^ 2 := by ring
    rw [this]
    exact le_mul_of_one_le_left (sq_nonneg _) hpi
  have h3 : 0 ≤ 2 * π * |a| := by positivity
  linarith

/-- FS81 J p.576 (c): `|I_β(φ+ia)/I_β(φ)| ≤ e^{g(a)/β}` with `g(a) = C a²` for `|a| ≤ 1` and
`g(a) = C e^{2π|a|}` for `1 < |a| ≤ β/2`, uniformly in real `φ` and `β ≥ β₀`. -/
theorem norm_besselInterp_translate_div_le :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 ≤ C ∧ ∀ β : ℝ, β₀ ≤ β → ∀ φ a : ℝ, |a| ≤ β / 2 →
      ‖besselInterp β (φ + a * I) / besselInterp β φ‖ ≤
        Real.exp ((if |a| ≤ 1 then C * a ^ 2 else C * Real.exp (2 * π * |a|)) / β) := by
  set D := debyeConst with hDdef
  set L := latticeSum with hLdef
  have hD : 0 < D := debyeConst_pos
  have hL : 0 ≤ L := latticeSum_nonneg
  have hk2 := kernelConst2_nonneg
  set C₁ := 20 + 2 * D * kernelConst2 * Real.exp (2 * π) * (3 * L) with hC₁
  set C₂ := 20 + 24 * D * L with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  refine ⟨max 1 (2 * D), max C₁ C₂, lt_max_of_lt_left one_pos, le_max_of_le_right hC₂0, ?_⟩
  intro β hβ φ a ha
  have hβ1 : 1 ≤ β := le_of_max_le_left hβ
  have hβD : 2 * D ≤ β := le_of_max_le_right hβ
  have hβ0 : 0 < β := by linarith
  have hM : ∀ n : ℤ, |logDefect β n| ≤ 2 * D / β := abs_logDefect_le_of_le hβD
  have hM0 : 0 ≤ 2 * D / β := by positivity
  have hz1 : |((φ : ℂ) + a * I).im| < β := by simp; linarith [abs_nonneg a]
  have hz0 : |((φ : ℂ)).im| < β := by simpa using hβ0
  rw [besselInterp_eq_exp_interpLog hβ0 hz1, besselInterp_eq_exp_interpLog hβ0 hz0,
    ← Complex.exp_sub, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hsplit : (interpLog β (φ + a * I) - interpLog β φ).re =
      (debyeLog β (φ + a * I) - debyeLog β φ).re +
        (defectSeries β (φ + a * I) - defectSeries β φ).re := by
    unfold interpLog; rw [← add_re]; congr 1; ring
  have hball : ∀ z ∈ closedBall (φ : ℂ) |a|, |z.im| ≤ β / 2 :=
    fun z hz => (abs_im_le_of_mem_closedBall hz).trans ha
  have hstrip : ∀ z ∈ closedBall (φ : ℂ) |a|, |z.im| < β :=
    fun z hz => lt_of_le_of_lt (hball z hz) (by linarith)
  have hℓ : (debyeLog β (φ + a * I) - debyeLog β φ).re ≤ 20 / β * a ^ 2 :=
    re_sub_le_of_hasDerivAt (fun z hz => hasDerivAt_debyeLog hβ0 (hstrip z hz))
      (fun z hz => hasDerivAt_debyeLogDeriv hβ0 (hstrip z hz))
      (fun z hz => norm_debyeLogDeriv2_le hβ1 (hball z hz)) (debyeLogDeriv_ofReal_im hβ0 φ)
  rw [hsplit]
  have hE1 := one_le_exp_two_pi_abs a
  have hEa := sq_le_exp_two_pi_abs a
  split_ifs with h1
  · have hS : (defectSeries β (φ + a * I) - defectSeries β φ).re ≤
        (2 * D / β * kernelConst2 * Real.exp (2 * π) * (3 * L)) * a ^ 2 := by
      refine re_sub_le_of_hasDerivAt (fun z _ => hasDerivAt_defectSeries hM z)
        (fun z _ => hasDerivAt_defectSeriesDeriv hM z) (fun z hz => ?_)
        (defectSeriesDeriv_ofReal_im hβ0 φ)
      refine (norm_defectSeriesDeriv2_le hM z).trans ?_
      have him : |z.im| ≤ 1 := (abs_im_le_of_mem_closedBall hz).trans h1
      have hexp : Real.exp (2 * π * |z.im|) ≤ Real.exp (2 * π) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      have h0 : 0 ≤ 2 * D / β * kernelConst2 := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp h0) (by positivity)
    have hcomb : 20 / β * a ^ 2 + 2 * D / β * kernelConst2 * Real.exp (2 * π) * (3 * L) * a ^ 2 =
        C₁ * a ^ 2 / β := by
      rw [hC₁]; field_simp
    have hmax : C₁ * a ^ 2 / β ≤ max C₁ C₂ * a ^ 2 / β := by
      gcongr
      exact le_max_left C₁ C₂
    have hsum := add_le_add hℓ hS
    rw [hcomb] at hsum
    exact hsum.trans hmax
  · have hS : (defectSeries β (φ + a * I) - defectSeries β φ).re ≤
        2 * D / β * 2 * (3 * L) * (Real.exp (2 * π * |a|) + 1) := by
      refine (re_le_norm _).trans ((norm_sub_le _ _).trans ?_)
      have h1' := norm_defectSeries_le hM ((φ : ℂ) + a * I)
      have h2' := norm_defectSeries_le hM (φ : ℂ)
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add, abs_zero, Real.exp_zero] at h1' h2'
      linarith
    generalize Real.exp (2 * π * |a|) = E at hE1 hEa hS ⊢
    have hDL : 0 ≤ D * L := mul_nonneg hD.le hL
    have key : 20 * a ^ 2 + 12 * (D * L) * (E + 1) ≤ C₂ * E := by
      rw [hC₂]; nlinarith
    have hcomb : 20 / β * a ^ 2 + 2 * D / β * 2 * (3 * L) * (E + 1) =
        (20 * a ^ 2 + 12 * (D * L) * (E + 1)) / β := by
      field_simp; ring
    calc (debyeLog β (φ + a * I) - debyeLog β φ).re +
          (defectSeries β (φ + a * I) - defectSeries β φ).re
        ≤ 20 / β * a ^ 2 + 2 * D / β * 2 * (3 * L) * (E + 1) := add_le_add hℓ hS
      _ = (20 * a ^ 2 + 12 * (D * L) * (E + 1)) / β := hcomb
      _ ≤ C₂ * E / β := by gcongr
      _ ≤ max C₁ C₂ * E / β :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (by linarith)) hβ0.le

/-- FS81 J p.576 (d), for `m = 1, 2`, stated through the logarithmic derivative (no branch of
`log` enters): the first two `φ`-derivatives of `log (I_β(φ+ia)/I_β(φ))` are at most
`C β⁻¹ e^{2π|a|}`, uniformly in real `φ`, `|a| ≤ β/2` and `β ≥ β₀`. -/
theorem logDeriv_besselInterp_translate_sub_le :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 ≤ C ∧ ∀ β : ℝ, β₀ ≤ β → ∀ φ a : ℝ, |a| ≤ β / 2 →
      ‖logDeriv (besselInterp β) (φ + a * I) - logDeriv (besselInterp β) φ‖ ≤
          C / β * Real.exp (2 * π * |a|) ∧
      ‖deriv (logDeriv (besselInterp β)) (φ + a * I) -
          deriv (logDeriv (besselInterp β)) φ‖ ≤ C / β * Real.exp (2 * π * |a|) := by
  set D := debyeConst with hDdef
  set L := latticeSum with hLdef
  have hD : 0 < D := debyeConst_pos
  have hL : 0 ≤ L := latticeSum_nonneg
  have hk1 := kernelConst1_nonneg
  have hk2 := kernelConst2_nonneg
  set C₁ := 20 + 12 * D * L * kernelConst1 with hC₁
  set C₂ := 40 + 12 * D * L * kernelConst2 with hC₂
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨max 1 (2 * D), max C₁ C₂, lt_max_of_lt_left one_pos, le_max_of_le_left hC₁0, ?_⟩
  intro β hβ φ a ha
  have hβ1 : 1 ≤ β := le_of_max_le_left hβ
  have hβD : 2 * D ≤ β := le_of_max_le_right hβ
  have hβ0 : 0 < β := by linarith
  have hM : ∀ n : ℤ, |logDefect β n| ≤ 2 * D / β := abs_logDefect_le_of_le hβD
  have hz1 : |((φ : ℂ) + a * I).im| < β := by simp; linarith [abs_nonneg a]
  have hz0 : |((φ : ℂ)).im| < β := by simpa using hβ0
  have hball : ∀ z ∈ closedBall (φ : ℂ) |a|, |z.im| ≤ β / 2 :=
    fun z hz => (abs_im_le_of_mem_closedBall hz).trans ha
  have hstrip : ∀ z ∈ closedBall (φ : ℂ) |a|, |z.im| < β :=
    fun z hz => lt_of_le_of_lt (hball z hz) (by linarith)
  have hmem := ofReal_add_mul_I_mem_closedBall φ a
  have hnorm : ‖(φ : ℂ) + a * I - φ‖ = |a| := by
    rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  have hE1 := one_le_exp_two_pi_abs a
  have hEa := abs_le_exp_two_pi_abs a
  have himz1 : |((φ : ℂ) + a * I).im| = |a| := by simp
  have himz0 : |((φ : ℂ)).im| = 0 := by simp
  rw [logDeriv_besselInterp hβ0 hz1, logDeriv_besselInterp hβ0 hz0,
    deriv_logDeriv_besselInterp hβ0 hz1, deriv_logDeriv_besselInterp hβ0 hz0]
  have hDL : 0 ≤ D * L := mul_nonneg hD.le hL
  constructor
  · have hℓ : ‖debyeLogDeriv β (φ + a * I) - debyeLogDeriv β φ‖ ≤ 20 / β * |a| := by
      have := norm_sub_le_of_hasDerivAt_closedBall
        (fun z hz => hasDerivAt_debyeLogDeriv hβ0 (hstrip z hz))
        (fun z hz => norm_debyeLogDeriv2_le hβ1 (hball z hz)) hmem
      rwa [hnorm] at this
    have hS1 := norm_defectSeriesDeriv_le hM ((φ : ℂ) + a * I)
    have hS0 := norm_defectSeriesDeriv_le hM (φ : ℂ)
    rw [himz1] at hS1
    rw [himz0, mul_zero, Real.exp_zero, mul_one] at hS0
    have hsplit : interpLogDeriv β (φ + a * I) - interpLogDeriv β φ =
        (debyeLogDeriv β (φ + a * I) - debyeLogDeriv β φ) +
          (defectSeriesDeriv β (φ + a * I) - defectSeriesDeriv β φ) := by
      unfold interpLogDeriv; ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add hℓ ((norm_sub_le _ _).trans (add_le_add hS1 hS0))).trans ?_
    generalize Real.exp (2 * π * |a|) = E at hE1 hEa hS1 ⊢
    have key : 20 * |a| + 6 * (D * L) * kernelConst1 * (E + 1) ≤ C₁ * E := by
      have : 0 ≤ D * L * kernelConst1 := mul_nonneg hDL hk1
      rw [hC₁]; nlinarith
    calc 20 / β * |a| + (2 * D / β * kernelConst1 * E * (3 * L) +
          2 * D / β * kernelConst1 * (3 * L))
        = (20 * |a| + 6 * (D * L) * kernelConst1 * (E + 1)) / β := by field_simp; ring
      _ ≤ C₁ * E / β := by gcongr
      _ ≤ max C₁ C₂ / β * E := by
          rw [div_mul_eq_mul_div]
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (by linarith)) hβ0.le
  · have hℓ1 := norm_debyeLogDeriv2_le hβ1 (hball _ hmem)
    have hℓ0 := norm_debyeLogDeriv2_le hβ1 (hball _ (mem_closedBall_self (abs_nonneg a)))
    have hS1 := norm_defectSeriesDeriv2_le hM ((φ : ℂ) + a * I)
    have hS0 := norm_defectSeriesDeriv2_le hM (φ : ℂ)
    rw [himz1] at hS1
    rw [himz0, mul_zero, Real.exp_zero, mul_one] at hS0
    have hsplit : interpLogDeriv2 β (φ + a * I) - interpLogDeriv2 β φ =
        (debyeLogDeriv2 β (φ + a * I) - debyeLogDeriv2 β φ) +
          (defectSeriesDeriv2 β (φ + a * I) - defectSeriesDeriv2 β φ) := by
      unfold interpLogDeriv2; ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add ((norm_sub_le _ _).trans (add_le_add hℓ1 hℓ0))
      ((norm_sub_le _ _).trans (add_le_add hS1 hS0))).trans ?_
    generalize Real.exp (2 * π * |a|) = E at hE1 hEa hS1 ⊢
    have key : 40 + 6 * (D * L) * kernelConst2 * (E + 1) ≤ C₂ * E := by
      have : 0 ≤ D * L * kernelConst2 := mul_nonneg hDL hk2
      rw [hC₂]; nlinarith
    calc 20 / β + 20 / β + (2 * D / β * kernelConst2 * E * (3 * L) +
          2 * D / β * kernelConst2 * (3 * L))
        = (40 + 6 * (D * L) * kernelConst2 * (E + 1)) / β := by field_simp; ring
      _ ≤ C₂ * E / β := by gcongr
      _ ≤ max C₁ C₂ / β * E := by
          rw [div_mul_eq_mul_div]
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (by linarith)) hβ0.le

end FroehlichSpencer.BKT.Rotator.BesselInterp
