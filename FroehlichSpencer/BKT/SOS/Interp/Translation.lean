/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Interp.Strip
public import FroehlichSpencer.BKT.Rotator.Contour.Factor
import FroehlichSpencer.BKT.Rotator.BesselInterp.Vertical

/-!
# Appendix C: translation-ratio and logarithmic-derivative bounds (FS81 §7.2 (c), (d))

For `0 < β ≤ 1`, real `φ` and `|a| ≤ ½β^{-1/3}` (that is, `β^{1/3}|a| ≤ 1/2`):

* (c), sharp form: `|I_β(φ + ia)/I_β(φ)| ≤ exp(β^{2/3} g(a))`, with the §6 envelope
  `g(a) = C a²` (`|a| ≤ 1`), `C e^{2π|a|}` (`|a| > 1`) of `cEnvelope`; since `β^{2/3} ≤ β^{1/3}`
  this implies the printed (c), `≤ exp(β^{1/3} g(a))`;
* (d) is **corrected**: the printed bound `≤ C β^{1/3} g(a)` with `g(a) = O(a²)` cannot hold for any
  interpolation (see `Inconsistency`); what holds is
  `|d^m/dφ^m log(I_β(φ+ia)/I_β(φ))| ≤ C β^{2/3} e^{2π|a|}` for `m = 1, 2`, and, for `|a| ≤ 1`,
  the linear bound `≤ C β^{2/3} |a|` for `m = 1`;
* on the real axis `|(log I_β)''| ≤ C β^{2/3}`.

All constants are absolute. The proofs use the explicit logarithm `Φ = -β^{2/3}s - S_β`, the
second-order vertical bound and the mean value inequality.
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Interp

open Complex Metric
open scoped Real
open FroehlichSpencer.BKT.Rotator.BesselInterp
open FroehlichSpencer.BKT.Rotator.Contour (cEnvelope)

/-- The Debye-type part `-b s` of the logarithm, and its first two derivatives. -/
def sosLogL (β : ℝ) (z : ℂ) : ℂ := -sosB β * sosRoot β z

def sosLogL1 (β : ℝ) (z : ℂ) : ℂ := -(sosB β ^ 2 * z / sosRoot β z)

def sosLogL2 (β : ℝ) (z : ℂ) : ℂ := -(sosB β ^ 2 / sosRoot β z ^ 3)

lemma hasDerivAt_sosLogL {β : ℝ} (hβ : 0 ≤ β) {z : ℂ} (hz : β ^ (1 / 3 : ℝ) * |z.im| < 1) :
    HasDerivAt (sosLogL β) (sosLogL1 β z) z := by
  have h := (hasDerivAt_sosRoot hβ hz).const_mul (-sosB β)
  unfold sosLogL sosLogL1
  convert h using 1; ring

lemma hasDerivAt_sosLogL1 {β : ℝ} (hβ : 0 ≤ β) {z : ℂ} (hz : β ^ (1 / 3 : ℝ) * |z.im| < 1) :
    HasDerivAt (sosLogL1 β) (sosLogL2 β z) z :=
  (hasDerivAt_sosRoot_quot hβ hz).neg

lemma sosSeriesDeriv_ofReal_im {β : ℝ} (hβ : 0 ≤ β) (x : ℝ) : (sosSeriesDeriv β x).im = 0 :=
  im_eq_zero_of_hasDerivAt_of_real (hasDerivAt_sosSeries hβ x)
    fun t => by rw [sosSeries_ofReal, ofReal_im]

lemma sosLogL1_ofReal_im {β : ℝ} (hβ : 0 ≤ β) (x : ℝ) : (sosLogL1 β x).im = 0 := by
  have h := sosLogDeriv_ofReal_im hβ x
  unfold sosLogDeriv at h
  unfold sosLogL1
  rw [sub_im, sosSeriesDeriv_ofReal_im hβ x, sub_zero] at h
  exact h

lemma rpow_two_thirds_sq_le {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    (β ^ (2 / 3 : ℝ)) ^ 2 ≤ β ^ (2 / 3 : ℝ) := by
  have h0 := Real.rpow_nonneg hβ (2 / 3 : ℝ)
  have h1 : β ^ (2 / 3 : ℝ) ≤ 1 := Real.rpow_le_one hβ hβ1 (by norm_num)
  nlinarith

lemma rpow_two_thirds_le_one_third {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    β ^ (2 / 3 : ℝ) ≤ β ^ (1 / 3 : ℝ) :=
  Real.rpow_le_rpow_of_exponent_ge hβ hβ1 (by norm_num)

lemma im_le_of_mem_closedBall {β x r : ℝ} (hβ : 0 ≤ β) {z : ℂ} (hz : z ∈ closedBall (x : ℂ) r)
    (hr : β ^ (1 / 3 : ℝ) * r ≤ 1 / 2) : β ^ (1 / 3 : ℝ) * |z.im| ≤ 1 / 2 := by
  have h := abs_im_le_norm (z - x)
  rw [sub_im, ofReal_im, sub_zero] at h
  have hz' : ‖z - x‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hz
  exact (mul_le_mul_of_nonneg_left (h.trans hz') (Real.rpow_nonneg hβ _)).trans hr

lemma exp_two_pi_bounds (a : ℝ) :
    1 ≤ Real.exp (2 * π * |a|) ∧ |a| ≤ Real.exp (2 * π * |a|) ∧ a ^ 2 ≤ Real.exp (2 * π * |a|) := by
  refine ⟨Real.one_le_exp (by positivity), ?_, ?_⟩
  · have h := Real.add_one_le_exp (2 * π * |a|)
    nlinarith [Real.two_le_pi, abs_nonneg a]
  · have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * π * |a| by positivity)
    have hpi : 1 ≤ (2 * π) ^ 2 / 2 := by nlinarith [Real.two_le_pi]
    have h2 : a ^ 2 ≤ (2 * π * |a|) ^ 2 / 2 := by
      rw [mul_pow, ← sq_abs a]
      have : (2 * π) ^ 2 * |a| ^ 2 / 2 = ((2 * π) ^ 2 / 2) * |a| ^ 2 := by ring
      rw [this]; exact le_mul_of_one_le_left (sq_nonneg _) hpi
    have h3 : 0 ≤ 2 * π * |a| := by positivity
    linarith

/-- FS81 §7.2 (c) for the Appendix C interpolation, sharp form:
`|I_β(φ+ia)/I_β(φ)| ≤ exp(β^{2/3} g(a))` with the §6 envelope `g = cEnvelope C`. -/
theorem norm_sosInterp_translate_div_le_sharp :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, 0 < β → β ≤ 1 → ∀ φ a : ℝ, β ^ (1 / 3 : ℝ) * |a| ≤ 1 / 2 →
      ‖sosInterp β (φ + a * I) / sosInterp β φ‖ ≤ Real.exp (β ^ (2 / 3 : ℝ) * cEnvelope C a) := by
  set L := latticeSum
  have hL := latticeSum_nonneg
  have hk2 := kernelConst2_nonneg
  set C₁ := 8 + kernelConst2 * Real.exp (2 * π) * (3 * L) with hC₁
  set C₂ := 8 + 12 * L with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  refine ⟨max C₁ C₂, le_max_of_le_right hC₂0, fun β hβ hβ1 φ a ha => ?_⟩
  set b := β ^ (2 / 3 : ℝ) with hb
  have hb0 : 0 ≤ b := Real.rpow_nonneg hβ.le _
  have hbsq := rpow_two_thirds_sq_le hβ.le hβ1
  rw [sosInterp_eq_exp_sosLog, sosInterp_eq_exp_sosLog, ← Complex.exp_sub, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hball : ∀ z ∈ closedBall (φ : ℂ) |a|, β ^ (1 / 3 : ℝ) * |z.im| ≤ 1 / 2 :=
    fun z hz => im_le_of_mem_closedBall hβ.le hz ha
  have hstrip : ∀ z ∈ closedBall (φ : ℂ) |a|, β ^ (1 / 3 : ℝ) * |z.im| < 1 :=
    fun z hz => by linarith [hball z hz]
  have hLpart : (sosLogL β (φ + a * I) - sosLogL β φ).re ≤ 8 * b ^ 2 * a ^ 2 :=
    re_sub_le_of_hasDerivAt (fun z hz => hasDerivAt_sosLogL hβ.le (hstrip z hz))
      (fun z hz => hasDerivAt_sosLogL1 hβ.le (hstrip z hz))
      (fun z hz => by
        unfold sosLogL2; rw [norm_neg]
        exact norm_sosB_sq_div_sosRoot_cube_le hβ.le (hball z hz))
      (sosLogL1_ofReal_im hβ.le φ)
  have hsplit : (sosLog β (φ + a * I) - sosLog β φ).re =
      (sosLogL β (φ + a * I) - sosLogL β φ).re +
        ((fun z => -sosSeries β z) (φ + a * I) - (fun z => -sosSeries β z) φ).re := by
    unfold sosLog sosLogL; simp only [sub_re, neg_re]; ring
  rw [hsplit]
  have hE := exp_two_pi_bounds a
  unfold cEnvelope
  split_ifs with h1
  · have hS : ((fun z => -sosSeries β z) (φ + a * I) - (fun z => -sosSeries β z) φ).re ≤
        (b * kernelConst2 * Real.exp (2 * π) * (3 * L)) * a ^ 2 := by
      refine re_sub_le_of_hasDerivAt (f' := fun z => -sosSeriesDeriv β z)
        (f'' := fun z => -sosSeriesDeriv2 β z)
        (fun z _ => (hasDerivAt_sosSeries hβ.le z).neg)
        (fun z _ => (hasDerivAt_sosSeriesDeriv hβ.le z).neg) (fun z hz => ?_) ?_
      · rw [norm_neg]
        refine (norm_sosSeriesDeriv2_le hβ.le z).trans ?_
        have him : |z.im| ≤ 1 := by
          have h := abs_im_le_norm (z - φ)
          rw [sub_im, ofReal_im, sub_zero] at h
          exact h.trans ((by rwa [mem_closedBall, dist_eq_norm] at hz : ‖z - φ‖ ≤ |a|).trans h1)
        have hexp : Real.exp (2 * π * |z.im|) ≤ Real.exp (2 * π) :=
          Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
        have h0 : 0 ≤ b * kernelConst2 := mul_nonneg hb0 hk2
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp h0) (by positivity)
      · simp only [neg_im, sosSeriesDeriv_ofReal_im hβ.le φ, neg_zero]
    have h8 : 8 * b ^ 2 * a ^ 2 ≤ 8 * b * a ^ 2 := by nlinarith [sq_nonneg a]
    have hfin : 8 * b * a ^ 2 + b * kernelConst2 * Real.exp (2 * π) * (3 * L) * a ^ 2 =
        b * (C₁ * a ^ 2) := by rw [hC₁]; ring
    have hmax : b * (C₁ * a ^ 2) ≤ b * (max C₁ C₂ * a ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg a)) hb0
    linarith
  · have hS : ((fun z => -sosSeries β z) (φ + a * I) - (fun z => -sosSeries β z) φ).re ≤
        b * 2 * (3 * L) * (Real.exp (2 * π * |a|) + 1) := by
      refine (re_le_norm _).trans ((norm_sub_le _ _).trans ?_)
      simp only [norm_neg]
      have h1' := norm_sosSeries_le hβ.le ((φ : ℂ) + a * I)
      have h2' := norm_sosSeries_le hβ.le (φ : ℂ)
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add, abs_zero, Real.exp_zero] at h1' h2'
      linarith
    obtain ⟨hE1, -, hEa⟩ := hE
    generalize Real.exp (2 * π * |a|) = E at hE1 hEa hS ⊢
    have h8 : 8 * b ^ 2 * a ^ 2 ≤ 8 * b * E := by nlinarith [sq_nonneg a]
    have hS' : b * 2 * (3 * L) * (E + 1) ≤ b * (12 * L) * E := by nlinarith [mul_nonneg hb0 hL]
    have hfin : 8 * b * E + b * (12 * L) * E = b * (C₂ * E) := by rw [hC₂]; ring
    have hmax : b * (C₂ * E) ≤ b * (max C₁ C₂ * E) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)) hb0
    linarith

/-- FS81 §7.2 (c) as printed: `|I_β(φ+ia)/I_β(φ)| ≤ exp(β^{1/3} g(a))` for `|a| ≤ ½β^{-1/3}`. -/
theorem norm_sosInterp_translate_div_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, 0 < β → β ≤ 1 → ∀ φ a : ℝ, β ^ (1 / 3 : ℝ) * |a| ≤ 1 / 2 →
      ‖sosInterp β (φ + a * I) / sosInterp β φ‖ ≤ Real.exp (β ^ (1 / 3 : ℝ) * cEnvelope C a) := by
  obtain ⟨C, hC, h⟩ := norm_sosInterp_translate_div_le_sharp
  refine ⟨C, hC, fun β hβ hβ1 φ a ha => (h β hβ hβ1 φ a ha).trans (Real.exp_le_exp.mpr ?_)⟩
  exact mul_le_mul_of_nonneg_right (rpow_two_thirds_le_one_third hβ hβ1)
    (Rotator.Contour.cEnvelope_nonneg hC a)

/-- FS81 §7.2 (d), **corrected**: for `m = 1, 2` the `φ`-derivatives of
`log(I_β(φ+ia)/I_β(φ))` (branch-free, via `logDeriv`) are at most `C β^{2/3} e^{2π|a|}`. -/
theorem logDeriv_sosInterp_translate_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, 0 < β → β ≤ 1 → ∀ φ a : ℝ, β ^ (1 / 3 : ℝ) * |a| ≤ 1 / 2 →
      ‖logDeriv (sosInterp β) (φ + a * I) - logDeriv (sosInterp β) φ‖ ≤
          C * β ^ (2 / 3 : ℝ) * Real.exp (2 * π * |a|) ∧
      ‖deriv (logDeriv (sosInterp β)) (φ + a * I) - deriv (logDeriv (sosInterp β)) φ‖ ≤
          C * β ^ (2 / 3 : ℝ) * Real.exp (2 * π * |a|) := by
  set L := latticeSum
  have hL := latticeSum_nonneg
  have hk1 := kernelConst1_nonneg
  have hk2 := kernelConst2_nonneg
  set C := 16 + 6 * L * kernelConst1 + 6 * L * kernelConst2 with hCdef
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, hC0, fun β hβ hβ1 φ a ha => ?_⟩
  set b := β ^ (2 / 3 : ℝ) with hb
  have hb0 : 0 ≤ b := Real.rpow_nonneg hβ.le _
  have hbsq := rpow_two_thirds_sq_le hβ.le hβ1
  have hz1 : β ^ (1 / 3 : ℝ) * |((φ : ℂ) + a * I).im| < 1 := by simp; linarith
  have hz0 : β ^ (1 / 3 : ℝ) * |((φ : ℂ)).im| < 1 := by simp
  have hball : ∀ z ∈ closedBall (φ : ℂ) |a|, β ^ (1 / 3 : ℝ) * |z.im| ≤ 1 / 2 :=
    fun z hz => im_le_of_mem_closedBall hβ.le hz ha
  have hmem := ofReal_add_mul_I_mem_closedBall φ a
  have hnorm : ‖(φ : ℂ) + a * I - φ‖ = |a| := by
    rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  have himz1 : |((φ : ℂ) + a * I).im| = |a| := by simp
  have himz0 : |((φ : ℂ)).im| = 0 := by simp
  obtain ⟨hE1, hEa, -⟩ := exp_two_pi_bounds a
  rw [logDeriv_sosInterp hβ.le hz1, logDeriv_sosInterp hβ.le hz0,
    deriv_logDeriv_sosInterp hβ.le hz1, deriv_logDeriv_sosInterp hβ.le hz0]
  constructor
  · have hLd : ‖sosLogL1 β (φ + a * I) - sosLogL1 β φ‖ ≤ 8 * b ^ 2 * |a| := by
      have := norm_sub_le_of_hasDerivAt_closedBall
        (fun z hz => hasDerivAt_sosLogL1 hβ.le (by linarith [hball z hz]))
        (fun z hz => by
          unfold sosLogL2; rw [norm_neg]
          exact norm_sosB_sq_div_sosRoot_cube_le hβ.le (hball z hz)) hmem
      rwa [hnorm] at this
    have hS1 := norm_sosSeriesDeriv_le hβ.le ((φ : ℂ) + a * I)
    have hS0 := norm_sosSeriesDeriv_le hβ.le (φ : ℂ)
    rw [himz1] at hS1
    rw [himz0, mul_zero, Real.exp_zero, mul_one] at hS0
    have hsplit : sosLogDeriv β (φ + a * I) - sosLogDeriv β φ =
        (sosLogL1 β (φ + a * I) - sosLogL1 β φ) -
          (sosSeriesDeriv β (φ + a * I) - sosSeriesDeriv β φ) := by
      unfold sosLogDeriv sosLogL1; ring
    rw [hsplit]
    refine (norm_sub_le _ _).trans ((add_le_add hLd ((norm_sub_le _ _).trans
      (add_le_add hS1 hS0))).trans ?_)
    generalize Real.exp (2 * π * |a|) = E at hE1 hEa hS1 ⊢
    have h1 : 8 * b ^ 2 * |a| ≤ 8 * b * E := by nlinarith [abs_nonneg a]
    have h2 : b * kernelConst1 * E * (3 * L) + b * kernelConst1 * (3 * L) ≤
        b * (6 * L * kernelConst1) * E := by
      have : 0 ≤ b * kernelConst1 * (3 * L) := by positivity
      nlinarith
    have h3 : 8 * b * E + b * (6 * L * kernelConst1) * E ≤ C * b * E := by
      rw [hCdef]
      have : 0 ≤ b * E := by nlinarith
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hL hk2) hb0) (by linarith : (0:ℝ) ≤ E)]
    linarith
  · have hL1 := norm_sosB_sq_div_sosRoot_cube_le hβ.le (hball _ hmem)
    have hL0 := norm_sosB_sq_div_sosRoot_cube_le hβ.le (hball _ (mem_closedBall_self (abs_nonneg a)))
    have hS1 := norm_sosSeriesDeriv2_le hβ.le ((φ : ℂ) + a * I)
    have hS0 := norm_sosSeriesDeriv2_le hβ.le (φ : ℂ)
    rw [himz1] at hS1
    rw [himz0, mul_zero, Real.exp_zero, mul_one] at hS0
    have hsplit : sosLogDeriv2 β (φ + a * I) - sosLogDeriv2 β φ =
        -(sosB β ^ 2 / sosRoot β (φ + a * I) ^ 3 - sosB β ^ 2 / sosRoot β φ ^ 3) -
          (sosSeriesDeriv2 β (φ + a * I) - sosSeriesDeriv2 β φ) := by
      unfold sosLogDeriv2; ring
    rw [hsplit]
    have hLsum : ‖-(sosB β ^ 2 / sosRoot β (φ + a * I) ^ 3 - sosB β ^ 2 / sosRoot β φ ^ 3)‖ ≤
        8 * b ^ 2 + 8 * b ^ 2 := by
      rw [norm_neg]; exact (norm_sub_le _ _).trans (add_le_add hL1 hL0)
    refine (norm_sub_le _ _).trans ((add_le_add hLsum
      ((norm_sub_le _ _).trans (add_le_add hS1 hS0))).trans ?_)
    generalize Real.exp (2 * π * |a|) = E at hE1 hEa hS1 ⊢
    have h1 : 8 * b ^ 2 + 8 * b ^ 2 ≤ 16 * b * E := by nlinarith
    have h2 : b * kernelConst2 * E * (3 * L) + b * kernelConst2 * (3 * L) ≤
        b * (6 * L * kernelConst2) * E := by
      have : 0 ≤ b * kernelConst2 * (3 * L) := by positivity
      nlinarith
    have h3 : 16 * b * E + b * (6 * L * kernelConst2) * E ≤ C * b * E := by
      rw [hCdef]
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hL hk1) hb0) (by linarith : (0:ℝ) ≤ E)]
    linarith

/-- The corrected (d) for `m = 1` at small translations is linear in `a`:
`|d/dφ log(I_β(φ+ia)/I_β(φ))| ≤ C β^{2/3} |a|` for `|a| ≤ 1`. -/
theorem logDeriv_sosInterp_translate_sub_le_linear :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, 0 < β → β ≤ 1 → ∀ φ a : ℝ, |a| ≤ 1 →
      β ^ (1 / 3 : ℝ) * |a| ≤ 1 / 2 →
      ‖logDeriv (sosInterp β) (φ + a * I) - logDeriv (sosInterp β) φ‖ ≤
        C * β ^ (2 / 3 : ℝ) * |a| := by
  set L := latticeSum
  have hL := latticeSum_nonneg
  have hk2 := kernelConst2_nonneg
  set C := 8 + kernelConst2 * Real.exp (2 * π) * (3 * L) with hCdef
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, hC0, fun β hβ hβ1 φ a ha1 ha => ?_⟩
  set b := β ^ (2 / 3 : ℝ) with hb
  have hb0 : 0 ≤ b := Real.rpow_nonneg hβ.le _
  have hbsq := rpow_two_thirds_sq_le hβ.le hβ1
  have hball : ∀ z ∈ closedBall (φ : ℂ) |a|, β ^ (1 / 3 : ℝ) * |z.im| ≤ 1 / 2 :=
    fun z hz => im_le_of_mem_closedBall hβ.le hz ha
  have hz1 : β ^ (1 / 3 : ℝ) * |((φ : ℂ) + a * I).im| < 1 := by simp; linarith
  have hz0 : β ^ (1 / 3 : ℝ) * |((φ : ℂ)).im| < 1 := by simp
  rw [logDeriv_sosInterp hβ.le hz1, logDeriv_sosInterp hβ.le hz0]
  have h := norm_sub_le_of_hasDerivAt_closedBall (f := sosLogDeriv β) (f' := sosLogDeriv2 β)
    (M := C * b)
    (fun z hz => hasDerivAt_sosLogDeriv hβ.le (by linarith [hball z hz]))
    (fun z hz => by
      have hL2 := norm_sosB_sq_div_sosRoot_cube_le hβ.le (hball z hz)
      have hS2 := norm_sosSeriesDeriv2_le hβ.le z
      have him : |z.im| ≤ 1 := by
        have h := abs_im_le_norm (z - φ)
        rw [sub_im, ofReal_im, sub_zero] at h
        exact h.trans ((by rwa [mem_closedBall, dist_eq_norm] at hz : ‖z - φ‖ ≤ |a|).trans ha1)
      have hexp : Real.exp (2 * π * |z.im|) ≤ Real.exp (2 * π) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      unfold sosLogDeriv2
      refine (norm_sub_le _ _).trans ?_
      rw [norm_neg]
      have h0 : 0 ≤ b * kernelConst2 := mul_nonneg hb0 hk2
      have hS2' : ‖sosSeriesDeriv2 β z‖ ≤ b * kernelConst2 * Real.exp (2 * π) * (3 * L) :=
        hS2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp h0) (by positivity))
      rw [hCdef]
      nlinarith)
    (ofReal_add_mul_I_mem_closedBall φ a)
  rw [show ‖(φ : ℂ) + a * I - φ‖ = |a| by
    rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]] at h
  calc ‖sosLogDeriv β (φ + a * I) - sosLogDeriv β φ‖ ≤ C * b * |a| := h

/-- The curvature of `log I_β` on the real axis: `|(log I_β)''(x)| ≤ C β^{2/3}`. This is the input
`c_J(β)` of the SOS endpoint repair (Appendix C). -/
theorem norm_deriv_logDeriv_sosInterp_ofReal_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, 0 < β → β ≤ 1 → ∀ x : ℝ,
      ‖deriv (logDeriv (sosInterp β)) x‖ ≤ C * β ^ (2 / 3 : ℝ) := by
  set L := latticeSum
  have hL := latticeSum_nonneg
  have hk2 := kernelConst2_nonneg
  refine ⟨8 + kernelConst2 * (3 * L), by positivity, fun β hβ hβ1 x => ?_⟩
  have hx : β ^ (1 / 3 : ℝ) * |((x : ℂ)).im| < 1 := by simp
  rw [deriv_logDeriv_sosInterp hβ.le hx]
  have hL2 := norm_sosB_sq_div_sosRoot_cube_le hβ.le (z := (x : ℂ)) (by simp)
  have hS2 := norm_sosSeriesDeriv2_le hβ.le (x : ℂ)
  simp only [ofReal_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at hS2
  have hbsq := rpow_two_thirds_sq_le hβ.le hβ1
  unfold sosLogDeriv2
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg]
  nlinarith
