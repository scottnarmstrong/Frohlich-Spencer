/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.LocalFactor
public import FroehlichSpencer.BKT.Generic.StripWeight
public import FroehlichSpencer.BKT.Rotator.Contour.Products
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Generic local-factor derivative bounds

Their first two derivatives are
controlled by `HasLogDerivBounds`; the strip-weight ratio estimate supplies the norm bound.

The
Bessel bridge identifies these definitions with the existing rotator factors and converts the
rotator logarithmic-derivative estimate to the generic interface.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open Complex
open scoped Real

variable {ι : Type*}

/-- One normalized edge factor, with the cost normalization from `Generic.LocalFactor`. -/
def normalizedEdgeFactor (w : ℂ → ℂ) (c : ℝ → ℝ) (a : ℝ) (x : ℝ) : ℂ :=
  w ((x : ℂ) + (a : ℂ) * I) / w x * Complex.exp (-((c a : ℝ) : ℂ))

/-- The logarithmic-derivative difference for a translated edge factor. -/
def factorLogDeriv (w : ℂ → ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  logDeriv w (z + (a : ℂ) * I) - logDeriv w z

/-- The derivative of `factorLogDeriv`, again written without choosing a branch of `log w`. -/
def factorLogDeriv2 (w : ℂ → ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  deriv (logDeriv w) (z + (a : ℂ) * I) - deriv (logDeriv w) z

/-- The normalized product along a real line of edge variables. -/
def genericEdgeProduct (w : ℂ → ℂ) (c : ℝ → ℝ) (S : Finset ι)
    (a x θ : ι → ℝ) (μ : ℝ) : ℂ :=
  ∏ e ∈ S, normalizedEdgeFactor w c (a e) (x e + μ * θ e)

/-- The logarithmic derivative of a finite edge product along its line. -/
def genericEdgeLogDeriv (w : ℂ → ℂ) (S : Finset ι)
    (a x θ : ι → ℝ) (μ : ℝ) : ℂ :=
  ∑ e ∈ S, (θ e : ℂ) *
    factorLogDeriv w (a e) ((x e : ℂ) + (μ : ℂ) * θ e)

/-- The derivative of `genericEdgeLogDeriv` along its line. -/
def genericEdgeLogDeriv2 (w : ℂ → ℂ) (S : Finset ι)
    (a x θ : ι → ℝ) (μ : ℝ) : ℂ :=
  ∑ e ∈ S, (θ e : ℂ) ^ 2 *
    factorLogDeriv2 w (a e) ((x e : ℂ) + (μ : ℂ) * θ e)

/-- The odd local functional in FS81 (6.18). -/
def genericLocalF₁ (w : ℂ → ℂ) (c : ℝ → ℝ) (S : Finset ι)
    (a x θ : ι → ℝ) (μ : ℝ) : ℂ :=
  I * (genericEdgeProduct w c S a x θ μ - genericEdgeProduct w c S (-a) x θ μ) / 2

/-- The even local functional in FS81 (6.18). -/
def genericLocalF₂ (w : ℂ → ℂ) (c : ℝ → ℝ) (S : Finset ι)
    (a x θ : ι → ℝ) (μ : ℝ) : ℂ :=
  (genericEdgeProduct w c S a x θ μ + genericEdgeProduct w c S (-a) x θ μ) / 2

section Calculus

variable {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

lemma complex_real_line (x θ μ : ℝ) :
    ((x + μ * θ : ℝ) : ℂ) = (x : ℂ) + (μ : ℂ) * θ := by
  push_cast
  ring

/-- A real-line parameterization has derivative `θ`, in the convention used by the contour files. -/
lemma hasDerivAt_realLine {f : ℂ → ℂ} {f' : ℂ} {x θ μ₀ : ℝ}
    (hf : HasDerivAt f f' ((x : ℂ) + (μ₀ : ℂ) * θ)) :
    HasDerivAt (fun μ : ℝ => f ((x : ℂ) + (μ : ℂ) * θ)) ((θ : ℂ) * f') μ₀ := by
  have hline : HasDerivAt (fun z : ℂ => (x : ℂ) + z * θ) (θ : ℂ) (μ₀ : ℂ) := by
    have h := ((hasDerivAt_id' (μ₀ : ℂ)).mul_const (θ : ℂ)).const_add (x : ℂ)
    simpa using h
  have h := (hf.comp (μ₀ : ℂ) hline).comp_ofReal
  rw [mul_comm] at h
  exact h

/-- Analyticity and nonvanishing make `logDeriv w = w'/w` analytic at points in the strip. -/
lemma analyticAt_logDeriv_of_strip
    (hanalytic : ∀ z : ℂ, |z.im| ≤ W → AnalyticAt ℂ w z)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {z : ℂ} (hz : |z.im| ≤ W) : AnalyticAt ℂ (logDeriv w) z := by
  change AnalyticAt ℂ (deriv w / w) z
  exact (hanalytic z hz).deriv.div (hanalytic z hz) (hnzero z hz)

/-- The line derivative of the first logarithmic-derivative difference. -/
theorem hasDerivAt_factorLogDeriv_line
    (hanalytic : ∀ z : ℂ, |z.im| ≤ W → AnalyticAt ℂ w z)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {a x θ μ₀ : ℝ} (ha : |a| ≤ W) (hw : 0 ≤ W) :
    HasDerivAt (fun μ : ℝ => factorLogDeriv w a ((x : ℂ) + (μ : ℂ) * θ))
      ((θ : ℂ) * factorLogDeriv2 w a ((x : ℂ) + (μ₀ : ℂ) * θ)) μ₀ := by
  let z₀ : ℂ := (x : ℂ) + (μ₀ : ℂ) * θ
  have hz₀ : |z₀.im| ≤ W := by
    rw [show z₀.im = 0 by simp [z₀], abs_zero]
    exact hw
  have hza : |(z₀ + (a : ℂ) * I).im| ≤ W := by
    calc |(z₀ + (a : ℂ) * I).im| = |a| := by simp [z₀]
      _ ≤ W := ha
  have hbase := analyticAt_logDeriv_of_strip hanalytic hnzero hz₀
  have hshift := analyticAt_logDeriv_of_strip hanalytic hnzero hza
  have hbase' := hbase.differentiableAt.hasDerivAt
  have hshift' := HasDerivAt.comp_add_const z₀ ((a : ℂ) * I)
    hshift.differentiableAt.hasDerivAt
  have hdiff := hshift'.sub hbase'
  have hline := hasDerivAt_realLine hdiff
  convert hline using 1 <;> simp [factorLogDeriv, factorLogDeriv2, z₀]

/-- The line derivative of a normalized edge factor. -/
theorem hasDerivAt_normalizedEdgeFactor_line
    (hw : IsStripWeight w W c)
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
/-- The first log-derivative difference is controlled by `HasLogDerivBounds`. -/
theorem norm_factorLogDeriv_le_of_hasLogDerivBounds
    (hM : HasLogDerivBounds w W M) {a x : ℝ} (ha : |a| ≤ W) :
    ‖factorLogDeriv w a (x : ℂ)‖ ≤ M a := by
  simpa [factorLogDeriv] using hM.logDeriv_sub_le x a ha

omit [DecidableEq ι] in
/-- The second log-derivative difference is controlled by `HasLogDerivBounds`. -/
theorem norm_factorLogDeriv2_le_of_hasLogDerivBounds
    (hM : HasLogDerivBounds w W M) {a x : ℝ} (ha : |a| ≤ W) :
    ‖factorLogDeriv2 w a (x : ℂ)‖ ≤ M a := by
  simpa [factorLogDeriv2] using hM.deriv_logDeriv_sub_le x a ha

omit [DecidableEq ι] in
/-- The normalized edge factor has norm at most one by the strip ratio bound. -/
theorem norm_normalizedEdgeFactor_le_one
    (hw : IsStripWeight w W c) {a x : ℝ} (ha : |a| ≤ W) :
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
theorem norm_genericEdgeProduct_le_one
    (hw : IsStripWeight w W c) {S : Finset ι} (a x θ : ι → ℝ) (μ : ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) :
    ‖genericEdgeProduct w c S a x θ μ‖ ≤ 1 := by
  unfold genericEdgeProduct
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun e he => norm_nonneg _)
    (fun e he => norm_normalizedEdgeFactor_le_one hw (ha e he))

/-- A finite product rule using the logarithmic derivative of each normalized edge factor. -/
theorem hasDerivAt_product_of_logDeriv
    {S : Finset ι} (f q : ι → ℝ → ℂ) (μ₀ : ℝ)
    (hq : ∀ e ∈ S, HasDerivAt (f e) (q e μ₀ * f e μ₀) μ₀) :
    HasDerivAt (fun μ => ∏ e ∈ S, f e μ)
      ((∑ e ∈ S, q e μ₀) * ∏ e ∈ S, f e μ₀) μ₀ := by
  classical
  revert hq
  induction S using Finset.induction_on with
  | empty =>
      intro hq
      simpa using (hasDerivAt_const μ₀ (1 : ℂ))
  | @insert e S he ih =>
      intro hq
      have he' := hq e (by simp)
      have hrest := ih (fun j hj => hq j (by simp [hj]))
      have hmul := he'.mul hrest
      convert hmul using 1
      · funext μ
        simp [Finset.prod_insert, he]
      · simp [Finset.sum_insert, Finset.prod_insert, he]
        ring

/-- A finite product rule using the logarithmic derivative of each normalized edge factor. -/
theorem hasDerivAt_genericEdgeProduct
    (hw : IsStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) (μ₀ : ℝ) :
    HasDerivAt (genericEdgeProduct w c S a x θ)
      (genericEdgeLogDeriv w S a x θ μ₀ * genericEdgeProduct w c S a x θ μ₀) μ₀ := by
  have hprod := hasDerivAt_product_of_logDeriv
    (f := fun e μ => normalizedEdgeFactor w c (a e) (x e + μ * θ e))
    (q := fun e μ => (θ e : ℂ) *
      factorLogDeriv w (a e) ((x e : ℂ) + (μ : ℂ) * θ e)) μ₀
    (fun e he => hasDerivAt_normalizedEdgeFactor_line hw hnzero
      (a := a e) (x := x e) (θ := θ e) (μ₀ := μ₀) (ha e he))
  change HasDerivAt
    (fun μ => ∏ e ∈ S, normalizedEdgeFactor w c (a e) (x e + μ * θ e))
    ((∑ e ∈ S, (θ e : ℂ) * factorLogDeriv w (a e)
      ((x e : ℂ) + (μ₀ : ℂ) * θ e)) *
        ∏ e ∈ S, normalizedEdgeFactor w c (a e) (x e + μ₀ * θ e)) μ₀
  exact hprod

/-- The derivative of the finite product is its log-derivative sum times the product. -/
theorem deriv_genericEdgeProduct
    (hw : IsStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) :
    deriv (genericEdgeProduct w c S a x θ) =
      fun μ => genericEdgeLogDeriv w S a x θ μ * genericEdgeProduct w c S a x θ μ := by
  funext μ
  exact (hasDerivAt_genericEdgeProduct hw hnzero a x θ ha μ).deriv

omit [DecidableEq ι] in
/-- The product log-derivative varies with derivative `genericEdgeLogDeriv2`. -/
theorem hasDerivAt_genericEdgeLogDeriv
    (hw : IsStripWeight w W c)
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
theorem hasDerivAt_deriv_genericEdgeProduct
    (hw : IsStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) (μ₀ : ℝ) :
    HasDerivAt (deriv (genericEdgeProduct w c S a x θ))
      ((genericEdgeLogDeriv w S a x θ μ₀ ^ 2 +
        genericEdgeLogDeriv2 w S a x θ μ₀) *
          genericEdgeProduct w c S a x θ μ₀) μ₀ := by
  rw [deriv_genericEdgeProduct hw hnzero a x θ ha]
  have h := (hasDerivAt_genericEdgeLogDeriv hw hnzero a x θ ha μ₀).mul
    (hasDerivAt_genericEdgeProduct hw hnzero a x θ ha μ₀)
  convert h using 1
  ring

omit [DecidableEq ι] in
/-- The first two logarithmic sums are bounded by the number of factors times their uniform
per-edge bound. -/
theorem norm_genericEdgeLogDeriv_bounds
    (hM : HasLogDerivBounds w W M)
    {S : Finset ι} (a x θ : ι → ℝ) (A T m μ : ℝ)
    (haA : ∀ e ∈ S, |a e| ≤ A) (hAW : A ≤ W)
    (hθT : ∀ e ∈ S, |θ e| ≤ T)
    (hMbound : ∀ u : ℝ, |u| ≤ A → M u ≤ m) :
    ‖genericEdgeLogDeriv w S a x θ μ‖ ≤ S.card * m * T ∧
      ‖genericEdgeLogDeriv2 w S a x θ μ‖ ≤ S.card * m * T ^ 2 := by
  have haW : ∀ e ∈ S, |a e| ≤ W := fun e he => (haA e he).trans hAW
  have hfirst :
      ‖genericEdgeLogDeriv w S a x θ μ‖ ≤ S.card * m * T := by
    unfold genericEdgeLogDeriv
    refine (norm_sum_le _ _).trans ?_
    calc ∑ e ∈ S, ‖(θ e : ℂ) *
          factorLogDeriv w (a e) ((x e : ℂ) + (μ : ℂ) * θ e)‖
        ≤ ∑ _e ∈ S, m * T := Finset.sum_le_sum fun e he => by
          have hL := norm_factorLogDeriv_le_of_hasLogDerivBounds hM
            (a := a e) (x := x e + μ * θ e) (haW e he)
          have hL' : ‖factorLogDeriv w (a e)
              ((x e : ℂ) + (μ : ℂ) * θ e)‖ ≤ m := by
            have hM' := hMbound (a e) (haA e he)
            simpa only [complex_real_line] using hL.trans hM'
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
          exact mul_le_mul hL' (hθT e he) (abs_nonneg _)
            ((norm_nonneg _).trans hL')
      _ = S.card * m * T := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hsecond :
      ‖genericEdgeLogDeriv2 w S a x θ μ‖ ≤ S.card * m * T ^ 2 := by
    unfold genericEdgeLogDeriv2
    refine (norm_sum_le _ _).trans ?_
    calc ∑ e ∈ S, ‖(θ e : ℂ) ^ 2 *
          factorLogDeriv2 w (a e) ((x e : ℂ) + (μ : ℂ) * θ e)‖
        ≤ ∑ _e ∈ S, m * T ^ 2 := Finset.sum_le_sum fun e he => by
          have hL := norm_factorLogDeriv2_le_of_hasLogDerivBounds hM
            (a := a e) (x := x e + μ * θ e) (haW e he)
          have hL' : ‖factorLogDeriv2 w (a e)
              ((x e : ℂ) + (μ : ℂ) * θ e)‖ ≤ m := by
            have hM' := hMbound (a e) (haA e he)
            simpa only [complex_real_line] using hL.trans hM'
          have hT : θ e ^ 2 ≤ T ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hθT e he) 2
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_comm]
          exact mul_le_mul hL' hT (sq_nonneg _)
            ((norm_nonneg _).trans hL')
      _ = S.card * m * T ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  exact ⟨hfirst, hsecond⟩

/-- One generic finite product and its first two line derivatives. -/
theorem genericEdgeProduct_bounds
    (hw : IsStripWeight w W c)
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
  have hP := norm_genericEdgeProduct_le_one hw a x θ μ haW
  have hQ := norm_genericEdgeLogDeriv_bounds hlog a x θ A T m μ haA hAW hθT hM
  have hderiv : ‖deriv (genericEdgeProduct w c S a x θ) μ‖ ≤ S.card * m * T := by
    rw [deriv_genericEdgeProduct hw hnzero a x θ haW, norm_mul]
    calc ‖genericEdgeLogDeriv w S a x θ μ‖ *
          ‖genericEdgeProduct w c S a x θ μ‖ ≤ (S.card * m * T) * 1 :=
        mul_le_mul hQ.1 hP (norm_nonneg _) ((norm_nonneg _).trans hQ.1)
      _ = S.card * m * T := mul_one _
  have hderiv2 :
      ‖deriv (deriv (genericEdgeProduct w c S a x θ)) μ‖ ≤
        2 * S.card ^ 2 * m * T ^ 2 := by
    rw [(hasDerivAt_deriv_genericEdgeProduct hw hnzero a x θ haW μ).deriv, norm_mul]
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

theorem hasDerivAt_genericLocalF₁
    (hw : IsStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) (μ₀ : ℝ) :
    HasDerivAt (genericLocalF₁ w c S a x θ)
      (I * (deriv (genericEdgeProduct w c S a x θ) μ₀ -
        deriv (genericEdgeProduct w c S (-a) x θ) μ₀) / 2) μ₀ := by
  have hp := hasDerivAt_genericEdgeProduct hw hnzero a x θ ha μ₀
  have hm := hasDerivAt_genericEdgeProduct hw hnzero (-a) x θ
    (fun e he => by rw [Pi.neg_apply, abs_neg]; exact ha e he) μ₀
  unfold genericLocalF₁
  rw [hp.deriv, hm.deriv]
  exact ((hp.sub hm).const_mul I).div_const 2

theorem hasDerivAt_genericLocalF₂
    (hw : IsStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) (μ₀ : ℝ) :
    HasDerivAt (genericLocalF₂ w c S a x θ)
      ((deriv (genericEdgeProduct w c S a x θ) μ₀ +
        deriv (genericEdgeProduct w c S (-a) x θ) μ₀) / 2) μ₀ := by
  have hp := hasDerivAt_genericEdgeProduct hw hnzero a x θ ha μ₀
  have hm := hasDerivAt_genericEdgeProduct hw hnzero (-a) x θ
    (fun e he => by rw [Pi.neg_apply, abs_neg]; exact ha e he) μ₀
  unfold genericLocalF₂
  rw [hp.deriv, hm.deriv]
  exact (hp.add hm).div_const 2

theorem deriv_genericLocalF₁
    (hw : IsStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) :
    deriv (genericLocalF₁ w c S a x θ) = fun μ =>
      I * (deriv (genericEdgeProduct w c S a x θ) μ -
        deriv (genericEdgeProduct w c S (-a) x θ) μ) / 2 := by
  funext μ
  exact (hasDerivAt_genericLocalF₁ hw hnzero a x θ ha μ).deriv

theorem deriv_genericLocalF₂
    (hw : IsStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) :
    deriv (genericLocalF₂ w c S a x θ) = fun μ =>
      (deriv (genericEdgeProduct w c S a x θ) μ +
        deriv (genericEdgeProduct w c S (-a) x θ) μ) / 2 := by
  funext μ
  exact (hasDerivAt_genericLocalF₂ hw hnzero a x θ ha μ).deriv

theorem deriv_deriv_genericLocalF₁
    (hw : IsStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) (μ₀ : ℝ) :
    deriv (deriv (genericLocalF₁ w c S a x θ)) μ₀ =
      I * (deriv (deriv (genericEdgeProduct w c S a x θ)) μ₀ -
        deriv (deriv (genericEdgeProduct w c S (-a) x θ)) μ₀) / 2 := by
  rw [deriv_genericLocalF₁ hw hnzero a x θ ha]
  have hp := hasDerivAt_deriv_genericEdgeProduct hw hnzero a x θ ha μ₀
  have hm := hasDerivAt_deriv_genericEdgeProduct hw hnzero (-a) x θ
    (fun e he => by rw [Pi.neg_apply, abs_neg]; exact ha e he) μ₀
  rw [hp.deriv, hm.deriv]
  exact (((hp.sub hm).const_mul I).div_const 2).deriv

theorem deriv_deriv_genericLocalF₂
    (hw : IsStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) (μ₀ : ℝ) :
    deriv (deriv (genericLocalF₂ w c S a x θ)) μ₀ =
      (deriv (deriv (genericEdgeProduct w c S a x θ)) μ₀ +
        deriv (deriv (genericEdgeProduct w c S (-a) x θ)) μ₀) / 2 := by
  rw [deriv_genericLocalF₂ hw hnzero a x θ ha]
  have hp := hasDerivAt_deriv_genericEdgeProduct hw hnzero a x θ ha μ₀
  have hm := hasDerivAt_deriv_genericEdgeProduct hw hnzero (-a) x θ
    (fun e he => by rw [Pi.neg_apply, abs_neg]; exact ha e he) μ₀
  rw [hp.deriv, hm.deriv]
  exact ((hp.add hm).div_const 2).deriv

lemma norm_I_mul_sub_div_two_le {B : ℝ} {u v : ℂ} (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B) :
    ‖I * (u - v) / 2‖ ≤ B := by
  rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_two]
  have h := norm_sub_le u v
  linarith

lemma norm_add_div_two_le {B : ℝ} {u v : ℂ} (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B) :
    ‖(u + v) / 2‖ ≤ B := by
  rw [norm_div, Complex.norm_two]
  have h := norm_add_le u v
  linarith

/-- Generic FS81 T6.1 (3)–(4): the local functionals have norm at most one, first derivative at
most `|S| m T`, and second derivative at most `2 |S|² m T²`. The pointwise log-derivative envelope
`M` is bounded by `m` on all increments of size at most `A`. -/
theorem genericLocalF_bounds
    (hw : IsStripWeight w W c)
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
  have hplus := genericEdgeProduct_bounds hw hnzero hlog a x θ A T m μ haA hAW hθT hm0 hm1 hM
  have hminus := genericEdgeProduct_bounds hw hnzero hlog (-a) x θ A T m μ
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
    · rw [deriv_genericLocalF₁ hw hnzero a x θ (fun e he => (haA e he).trans hAW)]
      exact norm_I_mul_sub_div_two_le hplus.2.1 hminus.2.1
    · rw [deriv_genericLocalF₂ hw hnzero a x θ (fun e he => (haA e he).trans hAW)]
      exact norm_add_div_two_le hplus.2.1 hminus.2.1
  have hlocal2 :
      ‖deriv (deriv (genericLocalF₁ w c S a x θ)) μ‖ ≤
          2 * S.card ^ 2 * m * T ^ 2 ∧
        ‖deriv (deriv (genericLocalF₂ w c S a x θ)) μ‖ ≤
          2 * S.card ^ 2 * m * T ^ 2 := by
    refine ⟨?_, ?_⟩
    · rw [deriv_deriv_genericLocalF₁ hw hnzero a x θ
        (fun e he => (haA e he).trans hAW) μ]
      exact norm_I_mul_sub_div_two_le hplus.2.2 hminus.2.2
    · rw [deriv_deriv_genericLocalF₂ hw hnzero a x θ
        (fun e he => (haA e he).trans hAW) μ]
      exact norm_add_div_two_le hplus.2.2 hminus.2.2
  exact ⟨hlocal0, hlocal1, hlocal2⟩

end LocalFunctionals

section BesselBridge

open FroehlichSpencer.BKT.Rotator.BesselInterp
open FroehlichSpencer.BKT.Rotator.Contour

/-- The rotator logarithmic-derivative estimate supplies the generic strip predicate. -/
theorem exists_hasLogDerivBounds_besselInterp :
    ∃ β₀ C_d : ℝ, 0 < β₀ ∧ 0 ≤ C_d ∧ ∀ β : ℝ, β₀ ≤ β →
      HasLogDerivBounds (besselInterp β) (β / 2)
        (fun u => C_d / β * Real.exp (2 * π * |u|)) := by
  obtain ⟨β₀, C_d, hβ₀, hC_d, h⟩ := logDeriv_besselInterp_translate_sub_le
  refine ⟨β₀, C_d, hβ₀, hC_d, fun β hβ => ?_⟩
  constructor
  · intro t u hu
    simpa using (h β hβ t u hu).1
  · intro t u hu
    simpa using (h β hβ t u hu).2

/-- The generic normalized edge factor specializes to the Bessel factor (6.19). -/
theorem normalizedEdgeFactor_besselBridge (β C a x : ℝ) :
    normalizedEdgeFactor (besselInterp β) (fun u => cEnvelope C u / β) a x =
      normalizedFactor β C a (x : ℂ) := rfl

/-- The generic finite product specializes to the Bessel edge product. -/
theorem genericEdgeProduct_besselBridge {ι : Type*} (S : Finset ι)
    (β C : ℝ) (a x θ : ι → ℝ) (μ : ℝ) :
    genericEdgeProduct (besselInterp β) (fun u => cEnvelope C u / β) S a x θ μ =
      FroehlichSpencer.BKT.Rotator.Contour.edgeProduct β C S a x θ μ := by
  unfold genericEdgeProduct FroehlichSpencer.BKT.Rotator.Contour.edgeProduct
  apply Finset.prod_congr rfl
  intro e he
  simpa only [complex_real_line] using
    normalizedEdgeFactor_besselBridge β C (a e) (x e + μ * θ e)

/-- The generic odd local functional specializes to the rotator's `F₁`. -/
theorem genericLocalF₁_besselBridge {ι : Type*} (S : Finset ι)
    (β C : ℝ) (a x θ : ι → ℝ) (μ : ℝ) :
    genericLocalF₁ (besselInterp β) (fun u => cEnvelope C u / β) S a x θ μ =
      FroehlichSpencer.BKT.Rotator.Contour.localF₁ β C S a x θ μ := by
  unfold genericLocalF₁ FroehlichSpencer.BKT.Rotator.Contour.localF₁
  rw [genericEdgeProduct_besselBridge, genericEdgeProduct_besselBridge]

/-- The generic even local functional specializes to the rotator's `F₂`. -/
theorem genericLocalF₂_besselBridge {ι : Type*} (S : Finset ι)
    (β C : ℝ) (a x θ : ι → ℝ) (μ : ℝ) :
    genericLocalF₂ (besselInterp β) (fun u => cEnvelope C u / β) S a x θ μ =
      FroehlichSpencer.BKT.Rotator.Contour.localF₂ β C S a x θ μ := by
  unfold genericLocalF₂ FroehlichSpencer.BKT.Rotator.Contour.localF₂
  rw [genericEdgeProduct_besselBridge, genericEdgeProduct_besselBridge]

/-- The generic bound theorem specializes to the Bessel `F₁`, `F₂` and their line derivatives. -/
theorem genericLocalF_bounds_besselBridge
    {ι : Type*} [DecidableEq ι] (β C : ℝ)
    (hw : IsStripWeight (besselInterp β) (β / 2)
      (fun u => cEnvelope C u / β))
    (hnzero : ∀ z : ℂ, |z.im| ≤ β / 2 → besselInterp β z ≠ 0)
    {M : ℝ → ℝ} (hlog : HasLogDerivBounds (besselInterp β) (β / 2) M)
    (S : Finset ι) (a x θ : ι → ℝ) (A T m μ : ℝ)
    (haA : ∀ e ∈ S, |a e| ≤ A) (hAW : A ≤ β / 2)
    (hθT : ∀ e ∈ S, |θ e| ≤ T) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hM : ∀ u : ℝ, |u| ≤ A → M u ≤ m) :
    (‖FroehlichSpencer.BKT.Rotator.Contour.localF₁ β C S a x θ μ‖ ≤ 1 ∧
      ‖FroehlichSpencer.BKT.Rotator.Contour.localF₂ β C S a x θ μ‖ ≤ 1) ∧
      (‖deriv (FroehlichSpencer.BKT.Rotator.Contour.localF₁ β C S a x θ) μ‖ ≤ S.card * m * T ∧
       ‖deriv (FroehlichSpencer.BKT.Rotator.Contour.localF₂ β C S a x θ) μ‖ ≤ S.card * m * T) ∧
      (‖deriv (deriv (FroehlichSpencer.BKT.Rotator.Contour.localF₁ β C S a x θ)) μ‖ ≤
          2 * S.card ^ 2 * m * T ^ 2 ∧
       ‖deriv (deriv (FroehlichSpencer.BKT.Rotator.Contour.localF₂ β C S a x θ)) μ‖ ≤
          2 * S.card ^ 2 * m * T ^ 2) := by
  have h := genericLocalF_bounds hw hnzero hlog a x θ A T m μ haA hAW hθT hm0 hm1 hM
  have h₁ : genericLocalF₁ (besselInterp β) (fun u => cEnvelope C u / β) S a x θ =
      FroehlichSpencer.BKT.Rotator.Contour.localF₁ β C S a x θ := by
    funext μ
    exact genericLocalF₁_besselBridge S β C a x θ μ
  have h₂ : genericLocalF₂ (besselInterp β) (fun u => cEnvelope C u / β) S a x θ =
      FroehlichSpencer.BKT.Rotator.Contour.localF₂ β C S a x θ := by
    funext μ
    exact genericLocalF₂_besselBridge S β C a x θ μ
  rw [h₁, h₂] at h
  exact h

end BesselBridge

end FroehlichSpencer.BKT.Generic

end
