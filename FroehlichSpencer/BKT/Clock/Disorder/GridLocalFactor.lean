/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Moment.Taylor
public import FroehlichSpencer.BKT.Clock.Periodic.ClockWeight
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The per-factor Taylor step for a locally analytic weight

The generic T1.5 per-factor Taylor bound `one_add_mul_lineFactor_ge` (FS81 (6.30)–(6.37);
`Generic/Moment/Taylor.lean`, `Generic/LocalFactorBounds.lean`) is stated for `IsStripWeight`. Its
proof uses only the local strip clauses: analyticity on the strip, the ratio bound, the cost
normalization and nonvanishing on the real axis. The integrable real-line majorant of
`IsStripWeight` is never used. That majorant fails for the periodic clock weight
`exp(β cos(z/N))`.

This file packages the local clauses as `IsLocalStripWeight` and proves that the clock weight
satisfies them (`clockEdgeWeight_isLocalStripWeight`). It then repeats the generic derivative
bounds and the Taylor step verbatim under the weaker hypothesis (suffix `_loc`):
* `genericLocalF_bounds_loc`, `lineFactor_derivs_loc`;
* **`one_add_mul_lineFactor_ge_loc`**: `(1 + z f(0)) exp(z f'(0)/(1 + z f(0)) − err) ≤ 1 + z f(1)`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open Complex
open scoped Real
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Clock.Periodic

variable {ι : Type*}

/-- The local clauses of a strip weight: those used by the T1.5 per-factor Taylor step. -/
structure IsLocalStripWeight (w : ℂ → ℂ) (W : ℝ) (c : ℝ → ℝ) : Prop where
  width_nonneg : 0 ≤ W
  ofReal_ne_zero : ∀ x : ℝ, w x ≠ 0
  analyticAt : ∀ z : ℂ, |z.im| ≤ W → AnalyticAt ℂ w z
  even : ∀ z : ℂ, |z.im| ≤ W → w (-z) = w z
  conj : ∀ z : ℂ, |z.im| ≤ W → (starRingEnd ℂ) (w z) = w ((starRingEnd ℂ) z)
  ratio_le : ∀ t u : ℝ, |u| ≤ W → ‖w ((t : ℂ) + (u : ℂ) * I) / w t‖ ≤ Real.exp (c u)
  cost_even : ∀ u, c (-u) = c u
  cost_zero : c 0 = 0

/-- **The clock weight satisfies the local strip clauses** at every width. -/
theorem clockEdgeWeight_isLocalStripWeight {β n W : ℝ} (hβ : 0 ≤ β) (hn : 0 < n) (hW : 0 ≤ W) :
    IsLocalStripWeight (clockEdgeWeight β n) W (clockShiftCost β n) := by
  have h := clockEdgeWeight_isCompactPeriodicWeight hβ hn
  exact ⟨hW, fun x => h.nonzero x, fun z _ => h.analyticAt z, fun z _ => h.even z,
    fun z _ => h.conj z, fun t u _ => h.ratio_le t u, h.cost_even, h.cost_zero⟩

section Calculus

variable {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

/-- The line derivative of a normalized edge factor. -/
theorem hasDerivAt_normalizedEdgeFactor_line_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {a x θ μ₀ : ℝ} (ha : |a| ≤ W) :
    HasDerivAt (fun μ : ℝ => normalizedEdgeFactor w c a (x + μ * θ))
      ((θ : ℂ) * factorLogDeriv w a ((x : ℂ) + (μ₀ : ℂ) * θ) *
        normalizedEdgeFactor w c a (x + μ₀ * θ)) μ₀ := by
  let f : ℂ → ℂ := fun z =>
    w (z + (a : ℂ) * I) / w z * Complex.exp (-((c a : ℝ) : ℂ))
  let z₀ : ℂ := (x : ℂ) + (μ₀ : ℂ) * θ
  have hz₀ : |z₀.im| ≤ W := by
    rw [show z₀.im = 0 by simp [z₀], abs_zero]
    exact hw.width_nonneg
  have hza : |(z₀ + (a : ℂ) * I).im| ≤ W := by
    calc |(z₀ + (a : ℂ) * I).im| = |a| := by simp [z₀]
      _ ≤ W := ha
  have hnum := (hw.analyticAt (z₀ + (a : ℂ) * I) hza).differentiableAt.hasDerivAt
  have hden := (hw.analyticAt z₀ hz₀).differentiableAt.hasDerivAt
  have hnum' := HasDerivAt.comp_add_const z₀ ((a : ℂ) * I) hnum
  have hquot := hnum'.div hden (hnzero z₀ hz₀)
  let dquot : ℂ :=
    (deriv w (z₀ + (a : ℂ) * I) * w z₀ - w (z₀ + (a : ℂ) * I) * deriv w z₀) / w z₀ ^ 2
  have hfun : HasDerivAt f (dquot * Complex.exp (-((c a : ℝ) : ℂ))) z₀ := by
    have h := hquot.mul_const (Complex.exp (-((c a : ℝ) : ℂ)))
    simpa [f, dquot] using h
  have hline := hasDerivAt_realLine hfun
  have hlineEq : (fun μ : ℝ => normalizedEdgeFactor w c a (x + μ * θ)) =
      fun μ : ℝ => f ((x : ℂ) + (μ : ℂ) * θ) := by
    funext μ
    simp [normalizedEdgeFactor, f]
  have hz₀eq : z₀ = ((x + μ₀ * θ : ℝ) : ℂ) := by
    dsimp [z₀]
    push_cast
    ring
  have hderivEq :
      (θ : ℂ) * (dquot * Complex.exp (-((c a : ℝ) : ℂ))) =
        (θ : ℂ) * factorLogDeriv w a z₀ * normalizedEdgeFactor w c a
          (x + μ₀ * θ) := by
    simp only [factorLogDeriv, normalizedEdgeFactor, logDeriv_apply]
    rw [← hz₀eq]
    simp only [dquot]
    field_simp [hnzero z₀ hz₀, hnzero (z₀ + (a : ℂ) * I) hza]
  rw [← hlineEq] at hline
  rw [hderivEq] at hline
  simpa [z₀] using hline

end Calculus

section Bounds

variable {w : ℂ → ℂ} {W : ℝ} {c M : ℝ → ℝ} [DecidableEq ι]

omit [DecidableEq ι] in
/-- The normalized edge factor has norm at most one by the strip ratio bound. -/
theorem norm_normalizedEdgeFactor_le_one_loc
    (hw : IsLocalStripWeight w W c) {a x : ℝ} (ha : |a| ≤ W) :
    ‖normalizedEdgeFactor w c a x‖ ≤ 1 := by
  unfold normalizedEdgeFactor
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  calc ‖w ((x : ℂ) + (a : ℂ) * I) / w x‖ * Real.exp (-c a)
      ≤ Real.exp (c a) * Real.exp (-c a) := by
        exact mul_le_mul_of_nonneg_right (hw.ratio_le x a ha) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

omit [DecidableEq ι] in
/-- A product of normalized edge factors has norm at most one. -/
theorem norm_genericEdgeProduct_le_one_loc
    (hw : IsLocalStripWeight w W c) {S : Finset ι} (a x θ : ι → ℝ) (μ : ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) :
    ‖genericEdgeProduct w c S a x θ μ‖ ≤ 1 := by
  unfold genericEdgeProduct
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun e he => norm_nonneg _)
    (fun e he => norm_normalizedEdgeFactor_le_one_loc hw (ha e he))

/-- A finite product rule using the logarithmic derivative of each normalized edge factor. -/
theorem hasDerivAt_genericEdgeProduct_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) (μ₀ : ℝ) :
    HasDerivAt (genericEdgeProduct w c S a x θ)
      (genericEdgeLogDeriv w S a x θ μ₀ * genericEdgeProduct w c S a x θ μ₀) μ₀ := by
  have hprod := hasDerivAt_product_of_logDeriv
    (f := fun e μ => normalizedEdgeFactor w c (a e) (x e + μ * θ e))
    (q := fun e μ => (θ e : ℂ) *
      factorLogDeriv w (a e) ((x e : ℂ) + (μ : ℂ) * θ e)) μ₀
    (fun e he => hasDerivAt_normalizedEdgeFactor_line_loc hw hnzero
      (a := a e) (x := x e) (θ := θ e) (μ₀ := μ₀) (ha e he))
  change HasDerivAt
    (fun μ => ∏ e ∈ S, normalizedEdgeFactor w c (a e) (x e + μ * θ e))
    ((∑ e ∈ S, (θ e : ℂ) * factorLogDeriv w (a e)
      ((x e : ℂ) + (μ₀ : ℂ) * θ e)) *
        ∏ e ∈ S, normalizedEdgeFactor w c (a e) (x e + μ₀ * θ e)) μ₀
  exact hprod

/-- The derivative of the finite product is its log-derivative sum times the product. -/
theorem deriv_genericEdgeProduct_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) :
    deriv (genericEdgeProduct w c S a x θ) =
      fun μ => genericEdgeLogDeriv w S a x θ μ * genericEdgeProduct w c S a x θ μ := by
  funext μ
  exact (hasDerivAt_genericEdgeProduct_loc hw hnzero a x θ ha μ).deriv

omit [DecidableEq ι] in
/-- The product log-derivative varies with derivative `genericEdgeLogDeriv2`. -/
theorem hasDerivAt_genericEdgeLogDeriv_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) (μ₀ : ℝ) :
    HasDerivAt (genericEdgeLogDeriv w S a x θ)
      (genericEdgeLogDeriv2 w S a x θ μ₀) μ₀ := by
  unfold genericEdgeLogDeriv genericEdgeLogDeriv2
  refine HasDerivAt.fun_sum fun e he => ?_
  have h := hasDerivAt_factorLogDeriv_line
    (fun z hz => hw.analyticAt z hz) hnzero
    (a := a e) (x := x e) (θ := θ e) (μ₀ := μ₀) (ha e he) hw.width_nonneg
  have h' := h.const_mul (θ e : ℂ)
  convert h' using 1
  ring

/-- The second derivative of the finite product. -/
theorem hasDerivAt_deriv_genericEdgeProduct_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) (μ₀ : ℝ) :
    HasDerivAt (deriv (genericEdgeProduct w c S a x θ))
      ((genericEdgeLogDeriv w S a x θ μ₀ ^ 2 +
        genericEdgeLogDeriv2 w S a x θ μ₀) *
          genericEdgeProduct w c S a x θ μ₀) μ₀ := by
  rw [deriv_genericEdgeProduct_loc hw hnzero a x θ ha]
  have h := (hasDerivAt_genericEdgeLogDeriv_loc hw hnzero a x θ ha μ₀).mul
    (hasDerivAt_genericEdgeProduct_loc hw hnzero a x θ ha μ₀)
  convert h using 1
  ring

/-- One generic finite product and its first two line derivatives. -/
theorem genericEdgeProduct_bounds_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    (hlog : HasLogDerivBounds w W M)
    {S : Finset ι} (a x θ : ι → ℝ) (A T m μ : ℝ)
    (haA : ∀ e ∈ S, |a e| ≤ A) (hAW : A ≤ W)
    (hθT : ∀ e ∈ S, |θ e| ≤ T) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hM : ∀ u : ℝ, |u| ≤ A → M u ≤ m) :
    ‖genericEdgeProduct w c S a x θ μ‖ ≤ 1 ∧
      ‖deriv (genericEdgeProduct w c S a x θ) μ‖ ≤ S.card * m * T ∧
      ‖deriv (deriv (genericEdgeProduct w c S a x θ)) μ‖ ≤
        2 * S.card ^ 2 * m * T ^ 2 := by
  have haW : ∀ e ∈ S, |a e| ≤ W := fun e he => (haA e he).trans hAW
  have hP := norm_genericEdgeProduct_le_one_loc hw a x θ μ haW
  have hQ := norm_genericEdgeLogDeriv_bounds hlog a x θ A T m μ haA hAW hθT hM
  have hderiv : ‖deriv (genericEdgeProduct w c S a x θ) μ‖ ≤ S.card * m * T := by
    rw [deriv_genericEdgeProduct_loc hw hnzero a x θ haW, norm_mul]
    calc ‖genericEdgeLogDeriv w S a x θ μ‖ *
          ‖genericEdgeProduct w c S a x θ μ‖ ≤ (S.card * m * T) * 1 :=
        mul_le_mul hQ.1 hP (norm_nonneg _) ((norm_nonneg _).trans hQ.1)
      _ = S.card * m * T := mul_one _
  have hderiv2 :
      ‖deriv (deriv (genericEdgeProduct w c S a x θ)) μ‖ ≤
        2 * S.card ^ 2 * m * T ^ 2 := by
    rw [(hasDerivAt_deriv_genericEdgeProduct_loc hw hnzero a x θ haW μ).deriv, norm_mul]
    have hsq : ‖genericEdgeLogDeriv w S a x θ μ‖ ^ 2 ≤
        (S.card * m * T) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hQ.1 2
    have hNN : (S.card : ℝ) ≤ S.card ^ 2 := by
      rcases Nat.eq_zero_or_pos S.card with h0 | hpos
      · rw [h0]
        norm_num
      · have : (1 : ℝ) ≤ S.card := by exact_mod_cast hpos
        nlinarith
    have hT2 : 0 ≤ T ^ 2 := sq_nonneg T
    have hM2 : m ^ 2 ≤ m := by nlinarith
    have hsum :
        ‖genericEdgeLogDeriv w S a x θ μ ^ 2 +
          genericEdgeLogDeriv2 w S a x θ μ‖ ≤
            (S.card * m * T) ^ 2 + S.card * m * T ^ 2 := by
      calc _ ≤ ‖genericEdgeLogDeriv w S a x θ μ‖ ^ 2 +
            ‖genericEdgeLogDeriv2 w S a x θ μ‖ := by
              refine (norm_add_le _ _).trans ?_
              rw [norm_pow]
        _ ≤ _ := add_le_add hsq hQ.2
    have hkey : (S.card * m * T) ^ 2 + S.card * m * T ^ 2 ≤
        2 * S.card ^ 2 * m * T ^ 2 := by
      have h1 : (S.card * m * T) ^ 2 = S.card ^ 2 * T ^ 2 * m ^ 2 := by ring
      have h2 : S.card ^ 2 * T ^ 2 * m ^ 2 ≤ S.card ^ 2 * T ^ 2 * m :=
        mul_le_mul_of_nonneg_left hM2 (by positivity)
      have h3 : S.card * m * T ^ 2 ≤ S.card ^ 2 * m * T ^ 2 := by
        have := mul_le_mul_of_nonneg_right hNN (mul_nonneg hm0 hT2)
        nlinarith [this]
      nlinarith
    calc
      ‖genericEdgeLogDeriv w S a x θ μ ^ 2 +
          genericEdgeLogDeriv2 w S a x θ μ‖ *
          ‖genericEdgeProduct w c S a x θ μ‖ ≤
        ((S.card * m * T) ^ 2 + S.card * m * T ^ 2) * 1 :=
          mul_le_mul hsum hP (norm_nonneg _) (by positivity)
      _ ≤ 2 * S.card ^ 2 * m * T ^ 2 := by rw [mul_one]; exact hkey
  exact ⟨hP, hderiv, hderiv2⟩

end Bounds

section LocalFunctionals

variable {w : ℂ → ℂ} {W : ℝ} {c M : ℝ → ℝ} [DecidableEq ι]

theorem hasDerivAt_genericLocalF₁_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) (μ₀ : ℝ) :
    HasDerivAt (genericLocalF₁ w c S a x θ)
      (I * (deriv (genericEdgeProduct w c S a x θ) μ₀ -
        deriv (genericEdgeProduct w c S (-a) x θ) μ₀) / 2) μ₀ := by
  have hp := hasDerivAt_genericEdgeProduct_loc hw hnzero a x θ ha μ₀
  have hm := hasDerivAt_genericEdgeProduct_loc hw hnzero (-a) x θ
    (fun e he => by rw [Pi.neg_apply, abs_neg]; exact ha e he) μ₀
  unfold genericLocalF₁
  rw [hp.deriv, hm.deriv]
  exact ((hp.sub hm).const_mul I).div_const 2

theorem hasDerivAt_genericLocalF₂_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) (μ₀ : ℝ) :
    HasDerivAt (genericLocalF₂ w c S a x θ)
      ((deriv (genericEdgeProduct w c S a x θ) μ₀ +
        deriv (genericEdgeProduct w c S (-a) x θ) μ₀) / 2) μ₀ := by
  have hp := hasDerivAt_genericEdgeProduct_loc hw hnzero a x θ ha μ₀
  have hm := hasDerivAt_genericEdgeProduct_loc hw hnzero (-a) x θ
    (fun e he => by rw [Pi.neg_apply, abs_neg]; exact ha e he) μ₀
  unfold genericLocalF₂
  rw [hp.deriv, hm.deriv]
  exact (hp.add hm).div_const 2

theorem deriv_genericLocalF₁_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) :
    deriv (genericLocalF₁ w c S a x θ) = fun μ =>
      I * (deriv (genericEdgeProduct w c S a x θ) μ -
        deriv (genericEdgeProduct w c S (-a) x θ) μ) / 2 := by
  funext μ
  exact (hasDerivAt_genericLocalF₁_loc hw hnzero a x θ ha μ).deriv

theorem deriv_genericLocalF₂_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) :
    deriv (genericLocalF₂ w c S a x θ) = fun μ =>
      (deriv (genericEdgeProduct w c S a x θ) μ +
        deriv (genericEdgeProduct w c S (-a) x θ) μ) / 2 := by
  funext μ
  exact (hasDerivAt_genericLocalF₂_loc hw hnzero a x θ ha μ).deriv

theorem deriv_deriv_genericLocalF₁_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) (μ₀ : ℝ) :
    deriv (deriv (genericLocalF₁ w c S a x θ)) μ₀ =
      I * (deriv (deriv (genericEdgeProduct w c S a x θ)) μ₀ -
        deriv (deriv (genericEdgeProduct w c S (-a) x θ)) μ₀) / 2 := by
  rw [deriv_genericLocalF₁_loc hw hnzero a x θ ha]
  have hp := hasDerivAt_deriv_genericEdgeProduct_loc hw hnzero a x θ ha μ₀
  have hm := hasDerivAt_deriv_genericEdgeProduct_loc hw hnzero (-a) x θ
    (fun e he => by rw [Pi.neg_apply, abs_neg]; exact ha e he) μ₀
  rw [hp.deriv, hm.deriv]
  exact (((hp.sub hm).const_mul I).div_const 2).deriv

theorem deriv_deriv_genericLocalF₂_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) (μ₀ : ℝ) :
    deriv (deriv (genericLocalF₂ w c S a x θ)) μ₀ =
      (deriv (deriv (genericEdgeProduct w c S a x θ)) μ₀ +
        deriv (deriv (genericEdgeProduct w c S (-a) x θ)) μ₀) / 2 := by
  rw [deriv_genericLocalF₂_loc hw hnzero a x θ ha]
  have hp := hasDerivAt_deriv_genericEdgeProduct_loc hw hnzero a x θ ha μ₀
  have hm := hasDerivAt_deriv_genericEdgeProduct_loc hw hnzero (-a) x θ
    (fun e he => by rw [Pi.neg_apply, abs_neg]; exact ha e he) μ₀
  rw [hp.deriv, hm.deriv]
  exact ((hp.add hm).div_const 2).deriv

/-- Generic FS81 T6.1 (3)–(4): the local functionals have norm at most one, first derivative at
most `|S| m T`, and second derivative at most `2 |S|² m T²`. The pointwise log-derivative envelope
`M` is bounded by `m` on all increments of size at most `A`. -/
theorem genericLocalF_bounds_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    (hlog : HasLogDerivBounds w W M)
    {S : Finset ι} (a x θ : ι → ℝ) (A T m μ : ℝ)
    (haA : ∀ e ∈ S, |a e| ≤ A) (hAW : A ≤ W)
    (hθT : ∀ e ∈ S, |θ e| ≤ T) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hM : ∀ u : ℝ, |u| ≤ A → M u ≤ m) :
    (‖genericLocalF₁ w c S a x θ μ‖ ≤ 1 ∧ ‖genericLocalF₂ w c S a x θ μ‖ ≤ 1) ∧
      (‖deriv (genericLocalF₁ w c S a x θ) μ‖ ≤ S.card * m * T ∧
       ‖deriv (genericLocalF₂ w c S a x θ) μ‖ ≤ S.card * m * T) ∧
      (‖deriv (deriv (genericLocalF₁ w c S a x θ)) μ‖ ≤
          2 * S.card ^ 2 * m * T ^ 2 ∧
       ‖deriv (deriv (genericLocalF₂ w c S a x θ)) μ‖ ≤
          2 * S.card ^ 2 * m * T ^ 2) := by
  have hplus := genericEdgeProduct_bounds_loc hw hnzero hlog a x θ A T m μ haA hAW hθT hm0 hm1 hM
  have hminus := genericEdgeProduct_bounds_loc hw hnzero hlog (-a) x θ A T m μ
    (fun e he => by rw [Pi.neg_apply, abs_neg]; exact haA e he) hAW hθT hm0 hm1 hM
  have hlocal0 :
      ‖genericLocalF₁ w c S a x θ μ‖ ≤ 1 ∧
        ‖genericLocalF₂ w c S a x θ μ‖ ≤ 1 := by
    refine ⟨?_, ?_⟩
    · unfold genericLocalF₁
      exact norm_I_mul_sub_div_two_le hplus.1 hminus.1
    · unfold genericLocalF₂
      exact norm_add_div_two_le hplus.1 hminus.1
  have hlocal1 :
      ‖deriv (genericLocalF₁ w c S a x θ) μ‖ ≤ S.card * m * T ∧
        ‖deriv (genericLocalF₂ w c S a x θ) μ‖ ≤ S.card * m * T := by
    refine ⟨?_, ?_⟩
    · rw [deriv_genericLocalF₁_loc hw hnzero a x θ (fun e he => (haA e he).trans hAW)]
      exact norm_I_mul_sub_div_two_le hplus.2.1 hminus.2.1
    · rw [deriv_genericLocalF₂_loc hw hnzero a x θ (fun e he => (haA e he).trans hAW)]
      exact norm_add_div_two_le hplus.2.1 hminus.2.1
  have hlocal2 :
      ‖deriv (deriv (genericLocalF₁ w c S a x θ)) μ‖ ≤
          2 * S.card ^ 2 * m * T ^ 2 ∧
        ‖deriv (deriv (genericLocalF₂ w c S a x θ)) μ‖ ≤
          2 * S.card ^ 2 * m * T ^ 2 := by
    refine ⟨?_, ?_⟩
    · rw [deriv_deriv_genericLocalF₁_loc hw hnzero a x θ
        (fun e he => (haA e he).trans hAW) μ]
      exact norm_I_mul_sub_div_two_le hplus.2.2 hminus.2.2
    · rw [deriv_deriv_genericLocalF₂_loc hw hnzero a x θ
        (fun e he => (haA e he).trans hAW) μ]
      exact norm_add_div_two_le hplus.2.2 hminus.2.2
  exact ⟨hlocal0, hlocal1, hlocal2⟩

end LocalFunctionals


variable {E : Type*} [Fintype E] {w : ℂ → ℂ} {W : ℝ} {c M : ℝ → ℝ}


theorem lineFactor_derivs_loc (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0) (hlog : HasLogDerivBounds w W M)
    (b x y : E → ℝ) (ph s A T m : ℝ) (hbA : ∀ e, |b e| ≤ A) (hAW : A ≤ W)
    (hyT : ∀ e, b e ≠ 0 → |y e| ≤ T) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hM : ∀ u : ℝ, |u| ≤ A → M u ≤ m) :
    ∃ f' f'' : ℝ → ℝ,
      (∀ t, HasDerivAt (lineFactor w c b x y ph s) (f' t) t) ∧
      (∀ t, HasDerivAt f' (f'' t) t) ∧
      (∀ t, |lineFactor w c b x y ph s t| ≤ 1) ∧
      (∀ t, |f' t| ≤ 2 * ((Finset.univ.filter fun e => b e ≠ 0).card * m * T) + 2 * |s|) ∧
      ∀ t, |f'' t| ≤ 4 * ((Finset.univ.filter fun e => b e ≠ 0).card ^ 2 * m * T ^ 2) +
        4 * |s| * ((Finset.univ.filter fun e => b e ≠ 0).card * m * T) + 2 * s ^ 2 := by
  classical
  set S := Finset.univ.filter fun e => b e ≠ 0 with hSdef
  set N : ℝ := (S.card : ℝ) with hN
  have hbW : ∀ e, |b e| ≤ W := fun e => (hbA e).trans hAW
  have haS : ∀ e ∈ S, |b e| ≤ W := fun e _ => hbW e
  have haA : ∀ e ∈ S, |b e| ≤ A := fun e _ => hbA e
  have hθT : ∀ e ∈ S, |y e| ≤ T := fun e he => hyT e (Finset.mem_filter.mp he).2
  set F₁ := genericLocalF₁ w c S b x y with hF₁
  set F₂ := genericLocalF₂ w c S b x y with hF₂
  -- first and second derivatives of the complex local functionals
  have hd₁ : ∀ t, HasDerivAt F₁ (deriv F₁ t) t := fun t =>
    (hasDerivAt_genericLocalF₁_loc hw hnzero b x y haS t).differentiableAt.hasDerivAt
  have hd₂ : ∀ t, HasDerivAt F₂ (deriv F₂ t) t := fun t =>
    (hasDerivAt_genericLocalF₂_loc hw hnzero b x y haS t).differentiableAt.hasDerivAt
  have hbneg : ∀ e ∈ S, |(-b) e| ≤ W := fun e he => by rw [Pi.neg_apply, abs_neg]; exact haS e he
  have hdd₁ : ∀ t, HasDerivAt (deriv F₁) (deriv (deriv F₁) t) t := by
    intro t
    have hp := hasDerivAt_deriv_genericEdgeProduct_loc hw hnzero b x y haS t
    have hm := hasDerivAt_deriv_genericEdgeProduct_loc hw hnzero (-b) x y hbneg t
    have hd : DifferentiableAt ℝ (deriv F₁) t := by
      rw [hF₁, deriv_genericLocalF₁_loc hw hnzero b x y haS]
      exact (((hp.sub hm).const_mul I).div_const 2).differentiableAt
    exact hd.hasDerivAt
  have hdd₂ : ∀ t, HasDerivAt (deriv F₂) (deriv (deriv F₂) t) t := by
    intro t
    have hp := hasDerivAt_deriv_genericEdgeProduct_loc hw hnzero b x y haS t
    have hm := hasDerivAt_deriv_genericEdgeProduct_loc hw hnzero (-b) x y hbneg t
    have hd : DifferentiableAt ℝ (deriv F₂) t := by
      rw [hF₂, deriv_genericLocalF₂_loc hw hnzero b x y haS]
      exact ((hp.add hm).div_const 2).differentiableAt
    exact hd.hasDerivAt
  have hbd := fun t => genericLocalF_bounds_loc hw hnzero hlog b x y A T m t haA hAW hθT hm0 hm1 hM
  -- the real functions
  set f₁ : ℝ → ℝ := fun t => (F₁ t).re
  set f₂ : ℝ → ℝ := fun t => (F₂ t).re
  set d₁ : ℝ → ℝ := fun t => (deriv F₁ t).re
  set d₂ : ℝ → ℝ := fun t => (deriv F₂ t).re
  set e₁ : ℝ → ℝ := fun t => (deriv (deriv F₁) t).re
  set e₂ : ℝ → ℝ := fun t => (deriv (deriv F₂) t).re
  have hf₁ : ∀ t, HasDerivAt f₁ (d₁ t) t := fun t => hasDerivAt_re_of_hasDerivAt (hd₁ t)
  have hf₂ : ∀ t, HasDerivAt f₂ (d₂ t) t := fun t => hasDerivAt_re_of_hasDerivAt (hd₂ t)
  have hg₁ : ∀ t, HasDerivAt d₁ (e₁ t) t := fun t => hasDerivAt_re_of_hasDerivAt (hdd₁ t)
  have hg₂ : ∀ t, HasDerivAt d₂ (e₂ t) t := fun t => hasDerivAt_re_of_hasDerivAt (hdd₂ t)
  have hlin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ph + t * s) s t := fun t => by
    have := ((hasDerivAt_id t).mul_const s).const_add ph
    simpa using this
  have hcos : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.cos (ph + t * s))
      (-Real.sin (ph + t * s) * s) t := fun t => (Real.hasDerivAt_cos _).comp t (hlin t)
  have hsin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.sin (ph + t * s))
      (Real.cos (ph + t * s) * s) t := fun t => (Real.hasDerivAt_sin _).comp t (hlin t)
  -- the line factor through the bridge
  have hline : lineFactor w c b x y ph s = fun t =>
      f₂ t * Real.cos (ph + t * s) + f₁ t * Real.sin (ph + t * s) := by
    funext t
    unfold lineFactor
    rw [localFactor_line_eq hw.cost_zero hw.ofReal_ne_zero b x y t]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, f₁, f₂, F₁, F₂, hSdef]
  set f' : ℝ → ℝ := fun t => d₂ t * Real.cos (ph + t * s) + f₂ t * (-Real.sin (ph + t * s) * s) +
    (d₁ t * Real.sin (ph + t * s) + f₁ t * (Real.cos (ph + t * s) * s)) with hf'
  set f'' : ℝ → ℝ := fun t =>
    e₂ t * Real.cos (ph + t * s) + d₂ t * (-Real.sin (ph + t * s) * s) +
      (d₂ t * (-Real.sin (ph + t * s) * s) + f₂ t * (-(Real.cos (ph + t * s) * s) * s)) +
    (e₁ t * Real.sin (ph + t * s) + d₁ t * (Real.cos (ph + t * s) * s) +
      (d₁ t * (Real.cos (ph + t * s) * s) + f₁ t * (-Real.sin (ph + t * s) * s * s))) with hf''
  refine ⟨f', f'', fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · rw [hline]
    exact ((hf₂ t).mul (hcos t)).add ((hf₁ t).mul (hsin t))
  · have hc' : HasDerivAt (fun t : ℝ => -Real.sin (ph + t * s) * s)
        (-(Real.cos (ph + t * s) * s) * s) t := ((hsin t).neg).mul_const s
    have hs' : HasDerivAt (fun t : ℝ => Real.cos (ph + t * s) * s)
        (-Real.sin (ph + t * s) * s * s) t := (hcos t).mul_const s
    exact (((hg₂ t).mul (hcos t)).add ((hf₂ t).mul hc')).add
      (((hg₁ t).mul (hsin t)).add ((hf₁ t).mul hs'))
  · unfold lineFactor
    exact (Complex.abs_re_le_norm _).trans
      (norm_localFactor_le_one hw.ratio_le b _ hbW _)
  · obtain ⟨⟨hF₁b, hF₂b⟩, ⟨hD₁b, hD₂b⟩, -⟩ := hbd t
    have a1 : |f₁ t| ≤ 1 := (Complex.abs_re_le_norm _).trans hF₁b
    have a2 : |f₂ t| ≤ 1 := (Complex.abs_re_le_norm _).trans hF₂b
    have b1 : |d₁ t| ≤ N * m * T := (Complex.abs_re_le_norm _).trans hD₁b
    have b2 : |d₂ t| ≤ N * m * T := (Complex.abs_re_le_norm _).trans hD₂b
    have cc := Real.abs_cos_le_one (ph + t * s)
    have ss := Real.abs_sin_le_one (ph + t * s)
    have hs0 := abs_nonneg s
    simp only [hf']
    calc |d₂ t * Real.cos (ph + t * s) + f₂ t * (-Real.sin (ph + t * s) * s) +
          (d₁ t * Real.sin (ph + t * s) + f₁ t * (Real.cos (ph + t * s) * s))|
        ≤ |d₂ t| * |Real.cos (ph + t * s)| + |f₂ t| * (|Real.sin (ph + t * s)| * |s|) +
          (|d₁ t| * |Real.sin (ph + t * s)| + |f₁ t| * (|Real.cos (ph + t * s)| * |s|)) := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_)
            ((abs_add_le _ _).trans ?_))
          · rw [abs_mul, abs_mul, abs_mul, abs_neg]
          · rw [abs_mul, abs_mul, abs_mul]
      _ ≤ N * m * T * 1 + 1 * (1 * |s|) + (N * m * T * 1 + 1 * (1 * |s|)) := by
          have hB : 0 ≤ N * m * T := (abs_nonneg _).trans b1
          have j1 := mul_le_mul b2 cc (abs_nonneg _) hB
          have j2 := mul_le_mul a2 (mul_le_mul ss le_rfl hs0 zero_le_one) (by positivity)
            zero_le_one
          have j3 := mul_le_mul b1 ss (abs_nonneg _) hB
          have j4 := mul_le_mul a1 (mul_le_mul cc le_rfl hs0 zero_le_one) (by positivity)
            zero_le_one
          linarith
      _ = 2 * (N * m * T) + 2 * |s| := by ring
  · obtain ⟨⟨hF₁b, hF₂b⟩, ⟨hD₁b, hD₂b⟩, ⟨hE₁b, hE₂b⟩⟩ := hbd t
    have a1 : |f₁ t| ≤ 1 := (Complex.abs_re_le_norm _).trans hF₁b
    have a2 : |f₂ t| ≤ 1 := (Complex.abs_re_le_norm _).trans hF₂b
    have b1 : |d₁ t| ≤ N * m * T := (Complex.abs_re_le_norm _).trans hD₁b
    have b2 : |d₂ t| ≤ N * m * T := (Complex.abs_re_le_norm _).trans hD₂b
    have c1 : |e₁ t| ≤ 2 * N ^ 2 * m * T ^ 2 := (Complex.abs_re_le_norm _).trans hE₁b
    have c2 : |e₂ t| ≤ 2 * N ^ 2 * m * T ^ 2 := (Complex.abs_re_le_norm _).trans hE₂b
    have cc := Real.abs_cos_le_one (ph + t * s)
    have ss := Real.abs_sin_le_one (ph + t * s)
    have hs0 := abs_nonneg s
    have hB : 0 ≤ N * m * T := (abs_nonneg _).trans b1
    simp only [hf'']
    set C := Real.cos (ph + t * s)
    set Sn := Real.sin (ph + t * s)
    have key : |e₂ t * C + d₂ t * (-Sn * s) + (d₂ t * (-Sn * s) + f₂ t * (-(C * s) * s)) +
        (e₁ t * Sn + d₁ t * (C * s) + (d₁ t * (C * s) + f₁ t * (-Sn * s * s)))| ≤
        |e₂ t| * |C| + |d₂ t| * (|Sn| * |s|) + (|d₂ t| * (|Sn| * |s|) + |f₂ t| * (|C| * |s| * |s|)) +
        (|e₁ t| * |Sn| + |d₁ t| * (|C| * |s|) + (|d₁ t| * (|C| * |s|) +
          |f₁ t| * (|Sn| * |s| * |s|))) := by
      have t1 : |e₂ t * C| = |e₂ t| * |C| := abs_mul _ _
      have t2 : |d₂ t * (-Sn * s)| = |d₂ t| * (|Sn| * |s|) := by
        rw [abs_mul, abs_mul, abs_neg]
      have t3 : |f₂ t * (-(C * s) * s)| = |f₂ t| * (|C| * |s| * |s|) := by
        rw [abs_mul, abs_mul, abs_neg, abs_mul]
      have t4 : |e₁ t * Sn| = |e₁ t| * |Sn| := abs_mul _ _
      have t5 : |d₁ t * (C * s)| = |d₁ t| * (|C| * |s|) := by rw [abs_mul, abs_mul]
      have t6 : |f₁ t * (-Sn * s * s)| = |f₁ t| * (|Sn| * |s| * |s|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_neg]
      calc _ ≤ |e₂ t * C + d₂ t * (-Sn * s) + (d₂ t * (-Sn * s) + f₂ t * (-(C * s) * s))| +
            |e₁ t * Sn + d₁ t * (C * s) + (d₁ t * (C * s) + f₁ t * (-Sn * s * s))| :=
            abs_add_le _ _
        _ ≤ (|e₂ t * C| + |d₂ t * (-Sn * s)| + (|d₂ t * (-Sn * s)| +
              |f₂ t * (-(C * s) * s)|)) +
            (|e₁ t * Sn| + |d₁ t * (C * s)| + (|d₁ t * (C * s)| +
              |f₁ t * (-Sn * s * s)|)) := by
            refine add_le_add ?_ ?_
            · refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
            · refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
        _ = _ := by rw [t1, t2, t3, t4, t5, t6]
    refine key.trans ?_
    have hC := abs_nonneg C
    have hSn := abs_nonneg Sn
    have i1 : |e₂ t| * |C| ≤ 2 * N ^ 2 * m * T ^ 2 :=
      (mul_le_mul c2 cc hC ((abs_nonneg _).trans c2)).trans (le_of_eq (mul_one _))
    have i2 : |e₁ t| * |Sn| ≤ 2 * N ^ 2 * m * T ^ 2 :=
      (mul_le_mul c1 ss hSn ((abs_nonneg _).trans c1)).trans (le_of_eq (mul_one _))
    have i3 : |d₂ t| * (|Sn| * |s|) ≤ N * m * T * |s| :=
      mul_le_mul b2 (by nlinarith) (by positivity) hB
    have i4 : |d₁ t| * (|C| * |s|) ≤ N * m * T * |s| :=
      mul_le_mul b1 (by nlinarith) (by positivity) hB
    have i5 : |f₂ t| * (|C| * |s| * |s|) ≤ s ^ 2 := by
      have : |C| * |s| * |s| ≤ s ^ 2 := by
        rw [← sq_abs s]; nlinarith
      calc |f₂ t| * (|C| * |s| * |s|) ≤ 1 * s ^ 2 :=
            mul_le_mul a2 this (by positivity) zero_le_one
        _ = s ^ 2 := one_mul _
    have i6 : |f₁ t| * (|Sn| * |s| * |s|) ≤ s ^ 2 := by
      have : |Sn| * |s| * |s| ≤ s ^ 2 := by
        rw [← sq_abs s]; nlinarith
      calc |f₁ t| * (|Sn| * |s| * |s|) ≤ 1 * s ^ 2 :=
            mul_le_mul a1 this (by positivity) zero_le_one
        _ = s ^ 2 := one_mul _
    nlinarith

/-- **One factor along the real shift** (FS81 (6.35)–(6.37)): for `|z| ≤ 1/8`,
`(1 + z f(0)) exp(z f'(0)/(1 + z f(0)) − 8|z|(s² + (N m T)² + N² m T²)) ≤ 1 + z f(1)`, with
`f = lineFactor` and `N` the number of edges carrying the shift. -/
theorem one_add_mul_lineFactor_ge_loc (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0) (hlog : HasLogDerivBounds w W M)
    (b x y : E → ℝ) (ph s z A T m : ℝ) (hbA : ∀ e, |b e| ≤ A) (hAW : A ≤ W)
    (hyT : ∀ e, b e ≠ 0 → |y e| ≤ T) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hM : ∀ u : ℝ, |u| ≤ A → M u ≤ m) (hz : |z| ≤ 1 / 8) :
    (1 + z * lineFactor w c b x y ph s 0) *
        Real.exp (z * deriv (lineFactor w c b x y ph s) 0 /
            (1 + z * lineFactor w c b x y ph s 0) -
          8 * |z| * (s ^ 2 + ((Finset.univ.filter fun e => b e ≠ 0).card * m * T) ^ 2 +
            (Finset.univ.filter fun e => b e ≠ 0).card ^ 2 * m * T ^ 2)) ≤
      1 + z * lineFactor w c b x y ph s 1 := by
  obtain ⟨f', f'', hf, hf', hf0, hf'b, hf''b⟩ :=
    lineFactor_derivs_loc hw hnzero hlog b x y ph s A T m hbA hAW hyT hm0 hm1 hM
  set f := lineFactor w c b x y ph s with hfdef
  set N : ℝ := ((Finset.univ.filter fun e => b e ≠ 0).card : ℝ)
  set B := N * m * T with hBdef
  set Q := s ^ 2 + B ^ 2 + N ^ 2 * m * T ^ 2 with hQ
  have hQ2 : 0 ≤ N ^ 2 * m * T ^ 2 := by positivity
  have hz0 := abs_nonneg z
  have hD : ∀ t, 7 / 8 ≤ 1 + z * f t := by
    intro t
    have h1 : |z * f t| ≤ 1 / 8 := by
      rw [abs_mul]
      calc |z| * |f t| ≤ 1 / 8 * 1 := mul_le_mul hz (hf0 t) (abs_nonneg _) (by norm_num)
        _ = 1 / 8 := mul_one _
    linarith [neg_abs_le (z * f t)]
  have hDpos : ∀ t, 0 < 1 + z * f t := fun t => by linarith [hD t]
  -- `g = log (1 + z f)` and its derivatives
  set g : ℝ → ℝ := fun t => Real.log (1 + z * f t) with hg
  set g' : ℝ → ℝ := fun t => z * f' t / (1 + z * f t) with hg'
  set g'' : ℝ → ℝ := fun t =>
    (z * f'' t * (1 + z * f t) - z * f' t * (z * f' t)) / (1 + z * f t) ^ 2 with hg''
  have hgd : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    have h := ((hf t).const_mul z).const_add 1
    exact ((Real.hasDerivAt_log (hDpos t).ne').comp t h).congr_deriv (by
      show (1 + z * f t)⁻¹ * (z * f' t) = z * f' t / (1 + z * f t)
      rw [div_eq_inv_mul])
  have hg'd : ∀ t, HasDerivAt g' (g'' t) t := by
    intro t
    have hn := (hf' t).const_mul z
    have hd := ((hf t).const_mul z).const_add 1
    have h := hn.div hd (hDpos t).ne'
    convert h using 1
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g'' t| ≤ 16 * |z| * Q := by
    intro t _
    have hDt := hD t
    have hDp := hDpos t
    have h1 := hf'b t
    have h2 := hf''b t
    have hs := abs_nonneg s
    have hsplit : g'' t = z * f'' t / (1 + z * f t) - (z * f' t) ^ 2 / (1 + z * f t) ^ 2 := by
      simp only [hg'']
      field_simp
    rw [hsplit]
    have a1 : |z * f'' t / (1 + z * f t)| ≤ 8 / 7 * (|z| * |f'' t|) := by
      rw [abs_div, abs_mul, abs_of_pos hDp, div_le_iff₀ hDp]
      nlinarith [mul_nonneg hz0 (abs_nonneg (f'' t))]
    have a2 : |(z * f' t) ^ 2 / (1 + z * f t) ^ 2| ≤ 64 / 49 * (z ^ 2 * f' t ^ 2) := by
      rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos (by positivity),
        div_le_iff₀ (by positivity)]
      have hD2 : (7 / 8 : ℝ) ^ 2 ≤ (1 + z * f t) ^ 2 := by
        exact pow_le_pow_left₀ (by norm_num) hDt 2
      have : 0 ≤ z ^ 2 * f' t ^ 2 := by positivity
      nlinarith
    have hzz : z ^ 2 ≤ |z| / 8 := by
      rw [← sq_abs]
      nlinarith
    have hf'sq : f' t ^ 2 ≤ 8 * B ^ 2 + 8 * s ^ 2 := by
      have : |f' t| ^ 2 ≤ (2 * B + 2 * |s|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs] at this
      nlinarith [sq_abs s, sq_nonneg (B - |s|)]
    have hf''b' : |f'' t| ≤ 4 * (N ^ 2 * m * T ^ 2) + 2 * B ^ 2 + 4 * s ^ 2 := by
      nlinarith [sq_abs s, sq_nonneg (B - |s|)]
    calc |z * f'' t / (1 + z * f t) - (z * f' t) ^ 2 / (1 + z * f t) ^ 2|
        ≤ |z * f'' t / (1 + z * f t)| + |(z * f' t) ^ 2 / (1 + z * f t) ^ 2| :=
          abs_sub _ _
      _ ≤ 8 / 7 * (|z| * |f'' t|) + 64 / 49 * (z ^ 2 * f' t ^ 2) := add_le_add a1 a2
      _ ≤ 8 / 7 * (|z| * (4 * (N ^ 2 * m * T ^ 2) + 2 * B ^ 2 + 4 * s ^ 2)) +
          64 / 49 * (|z| / 8 * (8 * B ^ 2 + 8 * s ^ 2)) := by
          gcongr
      _ ≤ 16 * |z| * Q := by
          simp only [hQ]
          nlinarith [mul_nonneg hz0 hQ2, mul_nonneg hz0 (sq_nonneg B),
            mul_nonneg hz0 (sq_nonneg s)]
  have htay := taylor_lower_bound (fun t _ => hgd t) (fun t _ => hg'd t) hbound
  have hderiv : deriv f 0 = f' 0 := (hf 0).deriv
  rw [hderiv]
  have hexp1 : Real.exp (g 1) = 1 + z * f 1 := Real.exp_log (hDpos 1)
  have hexp0 : Real.exp (g 0) = 1 + z * f 0 := Real.exp_log (hDpos 0)
  calc (1 + z * f 0) * Real.exp (z * f' 0 / (1 + z * f 0) - 8 * |z| * Q)
      = Real.exp (g 0 + g' 0 - 16 * |z| * Q / 2) := by
        show _ = Real.exp (g 0 + z * f' 0 / (1 + z * f 0) - 16 * |z| * Q / 2)
        rw [show g 0 + z * f' 0 / (1 + z * f 0) - 16 * |z| * Q / 2 =
            g 0 + (z * f' 0 / (1 + z * f 0) - 8 * |z| * Q) by ring, Real.exp_add, hexp0]
    _ ≤ Real.exp (g 1) := Real.exp_le_exp.mpr htay
    _ = 1 + z * f 1 := hexp1


end FroehlichSpencer.BKT.Clock.Disorder

end
