/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Elementary lemmas for the SOS endpoint repair

The fixed endpoint prefactor of FS81 (7.32)–(7.40) comes from comparing
`1 + z F_{β,ε}` with `1 + z F_β` by the crude ratio `(1 − z)/(1 + z)`. The endpoint factors are
real, `F = ‖P‖ cos(θ + arg P)`, and the observable only shifts the phase `θ`. The
Kharash–Peled comparison (arXiv:1711.04720, Claim 3.1) bounds the shifted factor below by the
unshifted one times `exp(odd linear term − D|z|y²)`. Jensen's inequality against the
negation-invariant ensemble measure removes the odd term. The surviving loss is quadratic in
the shift and vanishes as `ε → 0`. This file proves the elementary ingredients:

* `one_add_mul_cos_add_ge`: KP Claim 3.1 with `D = 2`;
* `exp_mul_add_conj_div_two`: realness of the endpoint factors;
* `integral_exp_ge_exp_integral_even`: Jensen against an even probability measure;
* `add_neg_sub_two_mul_ge`: the symmetric second-difference bound;
* `two_mul_le_of_exp_le`: a prefactor-one lower bound `M(ε) ≥ e^{aε²}` gives `M''(0) ≥ 2a`,
  which is the step (7.17) ⇒ (7.18).
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Repair

open MeasureTheory Set Filter Topology

/-- Kharash–Peled Claim 3.1, real form with `D = 2`: for `|z| ≤ 1/8`,
`1 + z cos(x + y) ≥ exp(−z sin x sin y/(1 + z cos x) − 2|z|y²)·(1 + z cos x)`. -/
theorem one_add_mul_cos_add_ge {z x y : ℝ} (hz : |z| ≤ 1 / 8) :
    Real.exp (-(z * Real.sin x * Real.sin y) / (1 + z * Real.cos x) - 2 * |z| * y ^ 2) *
      (1 + z * Real.cos x) ≤ 1 + z * Real.cos (x + y) := by
  set p := 1 + z * Real.cos x with hp
  have hcx := Real.abs_cos_le_one x
  have hz0 := abs_nonneg z
  have hzc : |z * Real.cos x| ≤ 1 / 8 := by
    rw [abs_mul]
    calc |z| * |Real.cos x| ≤ |z| * 1 := mul_le_mul_of_nonneg_left hcx hz0
      _ ≤ 1 / 8 := by linarith
  have hp1 : 7 / 8 ≤ p := by have := neg_abs_le (z * Real.cos x); linarith
  have hppos : 0 < p := by linarith
  set u := Real.cos x * (Real.cos y - 1) - Real.sin x * Real.sin y with hu
  have hcosadd : Real.cos (x + y) = Real.cos x + u := by rw [Real.cos_add, hu]; ring
  set t := z * u / p with ht
  have h1t : 1 + z * Real.cos (x + y) = p * (1 + t) := by
    have hpm : p * (1 + z * u / p) = p + z * u := by
      rw [mul_add, mul_one, mul_div_cancel₀ _ hppos.ne']
    rw [hcosadd, ht, hpm, hp]; ring
  -- bounds on `1 - cos y` and on `u`
  have hcy1 : 0 ≤ 1 - Real.cos y := by linarith [Real.cos_le_one y]
  have hcy2 : 1 - Real.cos y ≤ y ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := y)]
  have hid : u ^ 2 + (Real.sin x * (Real.cos y - 1) + Real.cos x * Real.sin y) ^ 2 =
      2 * (1 - Real.cos y) := by
    have hx := Real.sin_sq_add_cos_sq x
    have hy := Real.sin_sq_add_cos_sq y
    rw [hu]
    linear_combination ((Real.cos y - 1) ^ 2 + Real.sin y ^ 2) * hx + hy
  have hu2 : u ^ 2 ≤ y ^ 2 := by
    nlinarith [sq_nonneg (Real.sin x * (Real.cos y - 1) + Real.cos x * Real.sin y)]
  have hu_abs : |u| ≤ 2 := by
    have : u = Real.cos (x + y) - Real.cos x := by rw [hcosadd]; ring
    rw [this]
    calc |Real.cos (x + y) - Real.cos x| ≤ |Real.cos (x + y)| + |Real.cos x| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one _) hcx
      _ = 2 := by norm_num
  have ht_abs : |t| ≤ 1 / 2 := by
    rw [ht, abs_div, abs_mul, abs_of_pos hppos, div_le_iff₀ hppos]
    calc |z| * |u| ≤ (1 / 8) * 2 := mul_le_mul hz hu_abs (abs_nonneg u) (by norm_num)
      _ ≤ 1 / 2 * p := by linarith
  have h1tpos : 0 < 1 + t := by linarith [(abs_le.mp ht_abs).1]
  -- `log (1 + t) ≥ t − 2t²` for `|t| ≤ 1/2`
  have hlog : t - 2 * t ^ 2 ≤ Real.log (1 + t) := by
    have h1 := Real.one_sub_inv_le_log_of_pos h1tpos
    have h2 : t - 2 * t ^ 2 ≤ 1 - (1 + t)⁻¹ := by
      rw [← sub_nonneg]
      have heq : 1 - (1 + t)⁻¹ - (t - 2 * t ^ 2) = t ^ 2 * (1 + 2 * t) / (1 + t) := by
        field_simp; ring
      rw [heq]
      apply div_nonneg _ h1tpos.le
      have : 0 ≤ 1 + 2 * t := by linarith [(abs_le.mp ht_abs).1]
      positivity
    linarith
  -- the exponent comparison
  have hw : -(4 / 7) * |z| * y ^ 2 ≤ z * Real.cos x * (Real.cos y - 1) / p := by
    rw [le_div_iff₀ hppos]
    have hb : |z * Real.cos x * (Real.cos y - 1)| ≤ |z| * (y ^ 2 / 2) := by
      rw [abs_mul, abs_mul, abs_of_nonpos (by linarith : Real.cos y - 1 ≤ 0)]
      calc |z| * |Real.cos x| * -(Real.cos y - 1) ≤ |z| * 1 * (y ^ 2 / 2) := by
            gcongr <;> linarith
        _ = |z| * (y ^ 2 / 2) := by ring
    have hneg := neg_abs_le (z * Real.cos x * (Real.cos y - 1))
    have hzy : 0 ≤ |z| * y ^ 2 := by positivity
    nlinarith
  have ht2 : 2 * t ^ 2 ≤ 16 / 49 * |z| * y ^ 2 := by
    have hz2 : z ^ 2 ≤ |z| / 8 := by
      rw [← sq_abs]; nlinarith
    have hnum : (z * u) ^ 2 ≤ |z| / 8 * y ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul hz2 hu2 (sq_nonneg u) (by positivity)
    have hp2 : 49 / 64 ≤ p ^ 2 := by nlinarith
    have htsq : t ^ 2 = (z * u) ^ 2 / p ^ 2 := by rw [ht, div_pow]
    rw [htsq]
    have : (z * u) ^ 2 / p ^ 2 ≤ (|z| / 8 * y ^ 2) / (49 / 64) :=
      div_le_div₀ (by positivity) hnum (by norm_num) hp2
    have hzy : 0 ≤ |z| * y ^ 2 := by positivity
    nlinarith
  have htsplit : t = z * Real.cos x * (Real.cos y - 1) / p + -(z * Real.sin x * Real.sin y) / p := by
    rw [ht, hu]; field_simp; ring
  have hA : -(z * Real.sin x * Real.sin y) / p - 2 * |z| * y ^ 2 ≤ t - 2 * t ^ 2 := by
    have hzy : 0 ≤ |z| * y ^ 2 := by positivity
    rw [htsplit] at ht2 ⊢
    nlinarith
  calc Real.exp (-(z * Real.sin x * Real.sin y) / p - 2 * |z| * y ^ 2) * p
      ≤ Real.exp (Real.log (1 + t)) * p :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hA.trans hlog)) hppos.le
    _ = 1 + z * Real.cos (x + y) := by rw [Real.exp_log h1tpos, h1t]; ring

/-- The endpoint factors of FS81 (7.29) are real:
`(e^{iθ}P + e^{−iθ} conj P)/2 = ‖P‖ cos(θ + arg P)`. -/
theorem exp_mul_add_conj_div_two (θ : ℝ) (P : ℂ) :
    (Complex.exp (θ * Complex.I) * P + Complex.exp (-(θ * Complex.I)) * (starRingEnd ℂ) P) / 2 =
      ((‖P‖ * Real.cos (θ + Complex.arg P) : ℝ) : ℂ) := by
  have key : ∀ r a : ℝ,
      (Complex.exp (θ * Complex.I) * ((r : ℂ) * Complex.exp (a * Complex.I)) +
          Complex.exp (-(θ * Complex.I)) * (starRingEnd ℂ) ((r : ℂ) * Complex.exp (a * Complex.I))) /
        2 = ((r * Real.cos (θ + a) : ℝ) : ℂ) := by
    intro r a
    have hconj : (starRingEnd ℂ) ((r : ℂ) * Complex.exp (a * Complex.I)) =
        (r : ℂ) * Complex.exp (-(a * Complex.I)) := by
      rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
        Complex.conj_I, mul_neg]
    rw [hconj]
    have h2 : 2 * Complex.cos ((θ : ℂ) + a) =
        Complex.exp (((θ : ℂ) + a) * Complex.I) + Complex.exp (-((θ : ℂ) + a) * Complex.I) :=
      Complex.two_cos _
    have hexp1 : Complex.exp (θ * Complex.I) * Complex.exp (a * Complex.I) =
        Complex.exp (((θ : ℂ) + a) * Complex.I) := by rw [← Complex.exp_add]; ring_nf
    have hexp2 : Complex.exp (-(θ * Complex.I)) * Complex.exp (-(a * Complex.I)) =
        Complex.exp (-((θ : ℂ) + a) * Complex.I) := by rw [← Complex.exp_add]; ring_nf
    push_cast
    calc (Complex.exp (θ * Complex.I) * ((r : ℂ) * Complex.exp (a * Complex.I)) +
          Complex.exp (-(θ * Complex.I)) * ((r : ℂ) * Complex.exp (-(a * Complex.I)))) / 2
        = (r : ℂ) * ((Complex.exp (θ * Complex.I) * Complex.exp (a * Complex.I) +
            Complex.exp (-(θ * Complex.I)) * Complex.exp (-(a * Complex.I))) / 2) := by ring
      _ = (r : ℂ) * Complex.cos ((θ : ℂ) + a) := by
          rw [hexp1, hexp2, ← h2]; ring
  have := key ‖P‖ (Complex.arg P)
  rwa [Complex.norm_mul_exp_arg_mul_I] at this

/-- Jensen against a negation-invariant probability measure: only the even part of the exponent
counts. -/
theorem integral_exp_ge_exp_integral_even {V : Type*} [Fintype V]
    {μ : MeasureTheory.Measure (V → ℝ)} [MeasureTheory.IsProbabilityMeasure μ]
    (hμ : MeasureTheory.Measure.map (fun φ => -φ) μ = μ)
    {W : (V → ℝ) → ℝ} (hW : MeasureTheory.Integrable W μ)
    (hexp : MeasureTheory.Integrable (fun φ => Real.exp (W φ)) μ) :
    Real.exp (∫ φ, (W φ + W (-φ)) / 2 ∂μ) ≤ ∫ φ, Real.exp (W φ) ∂μ := by
  have hneg_meas : AEMeasurable (fun φ : V → ℝ => -φ) μ := measurable_neg.aemeasurable
  have hWmap : Integrable W (μ.map (fun φ => -φ)) := by rw [hμ]; exact hW
  have hWneg : Integrable (fun φ => W (-φ)) μ := hWmap.comp_aemeasurable hneg_meas
  have hint_neg : ∫ φ, W (-φ) ∂μ = ∫ φ, W φ ∂μ := by
    rw [← integral_map hneg_meas (by rw [hμ]; exact hW.aestronglyMeasurable), hμ]
  have heven : ∫ φ, (W φ + W (-φ)) / 2 ∂μ = ∫ φ, W φ ∂μ := by
    rw [integral_div, integral_add hW hWneg, hint_neg]; ring
  rw [heven]
  exact (convexOn_exp).map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall fun _ => mem_univ _) hW hexp

/-- Symmetric second difference: `g(t) + g(−t) − 2g(0) ≥ −B t²` when `|g''| ≤ B` on
`[−|t|, |t|]`. -/
theorem add_neg_sub_two_mul_ge {g g' g'' : ℝ → ℝ} {t B : ℝ}
    (hg : ∀ s, |s| ≤ |t| → HasDerivAt g (g' s) s) (hg' : ∀ s, |s| ≤ |t| → HasDerivAt g' (g'' s) s)
    (hB : ∀ s, |s| ≤ |t| → |g'' s| ≤ B) : -(B * t ^ 2) ≤ g t + g (-t) - 2 * g 0 := by
  set T := |t| with hTdef
  have hsym : g t + g (-t) = g T + g (-T) := by
    rcases le_or_gt 0 t with h | h
    · rw [hTdef, abs_of_nonneg h]
    · rw [hTdef, abs_of_neg h, neg_neg, add_comm]
  have htT : t ^ 2 = T ^ 2 := (sq_abs t).symm
  rw [hsym, htT]
  rcases (abs_nonneg t).eq_or_lt with hT0 | hTpos
  · rw [← hTdef] at hT0
    rw [← hT0]
    simp only [neg_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    linarith
  rw [← hTdef] at hTpos
  -- `g'(s) − g'(−s) ≥ −2Bs` for `0 < s ≤ T`
  have hstep : ∀ s, 0 < s → s ≤ T → -(2 * B * s) ≤ g' s - g' (-s) := by
    intro s hs hsT
    have hcont : ContinuousOn g' (Icc (-s) s) := fun u hu =>
      (hg' u (by rw [abs_le]; constructor <;> linarith [hu.1, hu.2])).continuousAt.continuousWithinAt
    obtain ⟨η, hη, hηeq⟩ := exists_hasDerivAt_eq_slope g' g'' (by linarith : -s < s) hcont
      (fun u hu => hg' u (by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]))
    have hηB : |g'' η| ≤ B := hB η (by rw [abs_le]; constructor <;> linarith [hη.1, hη.2])
    have hdiff : g' s - g' (-s) = g'' η * (2 * s) := by
      rw [hηeq]; field_simp; ring
    rw [hdiff]
    have := neg_abs_le (g'' η)
    nlinarith
  -- `k(s) = g(s) + g(−s) + B s²` is nondecreasing on `[0, T]`
  set k : ℝ → ℝ := fun s => g s + g (-s) + B * s ^ 2 with hk
  have hkder : ∀ s, |s| ≤ T → HasDerivAt k (g' s - g' (-s) + 2 * B * s) s := by
    intro s hs
    have h1 := hg s hs
    have h2 : HasDerivAt (fun u => g (-u)) (g' (-s) * (-1)) s := by
      exact (hg (-s) (by rwa [abs_neg])).comp s (hasDerivAt_neg s)
    have h3 : HasDerivAt (fun u => B * u ^ 2) (B * (2 * s)) s := by
      have := (hasDerivAt_pow 2 s).const_mul B
      simpa using this
    have := (h1.add h2).add h3
    convert this using 1; ring
  have hkcont : ContinuousOn k (Icc 0 T) := fun u hu =>
    (hkder u (by rw [abs_le]; constructor <;> linarith [hu.1, hu.2])).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope k (fun s => g' s - g' (-s) + 2 * B * s)
    hTpos hkcont (fun u hu => hkder u (by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]))
  have hk' : 0 ≤ g' ξ - g' (-ξ) + 2 * B * ξ := by
    have := hstep ξ hξ.1 hξ.2.le; linarith
  have hkT : k 0 ≤ k T := by
    have hslope : 0 ≤ (k T - k 0) / (T - 0) := by rw [← hξeq]; exact hk'
    rw [sub_zero] at hslope
    have := (div_nonneg_iff.mp hslope)
    rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith
    · linarith
  simp only [hk, neg_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    add_zero] at hkT
  linarith

/-- (7.17) ⇒ (7.18) needs prefactor one: a moment function with `M(0) = 1`, `M'(0) = 0` and
`M(ε) ≥ exp(aε²)` near `0` has second derivative at least `2a` at `0`. -/
theorem two_mul_le_of_exp_le {M M' : ℝ → ℝ} {m₂ a δ : ℝ} (hδ : 0 < δ) (hM0 : M 0 = 1)
    (hM : ∀ ε, |ε| < δ → Real.exp (a * ε ^ 2) ≤ M ε)
    (hM1 : ∀ ε, |ε| < δ → HasDerivAt M (M' ε) ε) (hM'0 : M' 0 = 0) (hM2 : HasDerivAt M' m₂ 0) :
    2 * a ≤ m₂ := by
  by_contra hlt
  push Not at hlt
  set κ := (m₂ + 2 * a) / 2 with hκ
  have hη : 0 < κ - m₂ := by rw [hκ]; linarith
  -- `M'(s) ≤ κ s` for small `s ≥ 0`
  have hlo := hM2.isLittleO.def hη
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hlo
  set s₀ := min ε δ / 2 with hs₀
  have hs₀pos : 0 < s₀ := by rw [hs₀]; exact half_pos (lt_min hε hδ)
  have hs₀ε : s₀ < ε := by rw [hs₀]; linarith [min_le_left ε δ, lt_min hε hδ]
  have hs₀δ : s₀ < δ := by rw [hs₀]; linarith [min_le_right ε δ, lt_min hε hδ]
  have hM'le : ∀ u, 0 ≤ u → u ≤ s₀ → M' u ≤ κ * u := by
    intro u hu0 hus
    have hdist : dist u 0 < ε := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hu0]; linarith
    have h := hball hdist
    rw [hM'0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hu0,
      smul_eq_mul] at h
    have := le_abs_self (M' u - u * m₂)
    nlinarith
  -- `k(u) = M(u) − κu²/2` is nonincreasing on `[0, s₀]`
  set k : ℝ → ℝ := fun u => M u - κ * u ^ 2 / 2 with hk
  have hkder : ∀ u, |u| < δ → HasDerivAt k (M' u - κ * u) u := by
    intro u hu
    have h1 := hM1 u hu
    have h2 : HasDerivAt (fun v => κ * v ^ 2 / 2) (κ * u) u := by
      have := ((hasDerivAt_pow 2 u).const_mul κ).div_const 2
      convert this using 1; ring
    exact h1.sub h2
  have hkcont : ContinuousOn k (Icc 0 s₀) := fun u hu =>
    (hkder u (by rw [abs_lt]; constructor <;> linarith [hu.1, hu.2])).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope k (fun u => M' u - κ * u) hs₀pos hkcont
    (fun u hu => hkder u (by rw [abs_lt]; constructor <;> linarith [hu.1, hu.2]))
  have hk' : M' ξ - κ * ξ ≤ 0 := by have := hM'le ξ hξ.1.le hξ.2.le; linarith
  have hks : k s₀ ≤ k 0 := by
    have hslope : (k s₀ - k 0) / (s₀ - 0) ≤ 0 := by rw [← hξeq]; exact hk'
    rw [sub_zero, div_nonpos_iff] at hslope
    rcases hslope with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith
    · linarith
  simp only [hk, hM0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_div, sub_zero] at hks
  have hlow := hM s₀ (by rw [abs_of_pos hs₀pos]; exact hs₀δ)
  have hexp := Real.add_one_le_exp (a * s₀ ^ 2)
  have hs2 : 0 < s₀ ^ 2 := by positivity
  nlinarith

end FroehlichSpencer.BKT.SOS.Repair
