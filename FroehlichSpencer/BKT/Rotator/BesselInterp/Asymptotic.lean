/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.BesselInterp.Defs
import FroehlichSpencer.BKT.Rotator.BesselInterp.Coeff
import FroehlichSpencer.BKT.Rotator.BesselInterp.Debye
import FroehlichSpencer.BKT.Rotator.BesselInterp.Contour
import FroehlichSpencer.BKT.Rotator.BesselInterp.Elementary
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The uniform Debye bound (B.12′)

For every `β > 0` and every integer `n`, with `s = √(β² + n²)`,

`|I_β(n) / L_β(n) - 1| ≤ debyeConst / s`,

an absolute constant over `s`. This is a complete replacement for the steepest-descent argument
(B.4)–(B.12) of FS81 Appendix B (J pp.597–599). After the contour shift (`Contour`),
`I_β(n)/L_β(n) = √(s/2π) ∫_{-π}^{π} e^{s(cos θ - 1)} cos(n(θ - sin θ)) dθ`, which is compared with
`√(s/2π) ∫_ℝ e^{-sθ²/2} dθ = 1` using `1 - cos θ ≥ 2θ²/π²` on `[-π, π]`, the Taylor bounds of
`Elementary`, and the even Gaussian moments.

Consequences: `|ln I_β(n) - ln L_β(n)| ≤ 2 debyeConst / s` once `s ≥ 2 debyeConst`, hence
`≤ 2 debyeConst / β` for all `n` when `β ≥ 2 debyeConst`, and the coefficients of (B.14) are bounded
for every `β > 0`.
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.BesselInterp

open MeasureTheory Set
open scoped Real

/-- The absolute constant of the uniform Debye bound (B.12′). -/
def debyeConst : ℝ :=
  Real.Gamma (3 + 1 / 2) / (72 * (Real.sqrt (2 * π) * Real.sqrt (2 / π ^ 2) * (2 / π ^ 2) ^ 3)) +
    Real.Gamma (2 + 1 / 2) / (24 * (Real.sqrt (2 * π) * Real.sqrt (2 / π ^ 2) * (2 / π ^ 2) ^ 2)) +
      Real.Gamma (1 + 1 / 2) / (π ^ 2 * (Real.sqrt (2 * π) * Real.sqrt (1 / 2) * (1 / 2) ^ 1))

theorem debyeConst_pos : 0 < debyeConst := by
  unfold debyeConst
  have h3 : 0 < Real.Gamma (3 + 1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  have h2 : 0 < Real.Gamma (2 + 1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  have h1 : 0 < Real.Gamma (1 + 1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  have hπ := Real.pi_pos
  have hs1 : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : 0 < Real.sqrt (2 / π ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs3 : 0 < Real.sqrt (1 / 2) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- `√(s/2π)` times the `k`th even Gaussian moment at `c s`. -/
lemma sqrt_div_mul_moment {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (k : ℕ) :
    Real.sqrt (s / (2 * π)) * (Real.Gamma (k + 1 / 2) / ((c * s) ^ k * Real.sqrt (c * s))) =
      Real.Gamma (k + 1 / 2) / (Real.sqrt (2 * π) * Real.sqrt c * c ^ k) / s ^ k := by
  have hπ : 0 < 2 * π := by positivity
  have h1 : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h2 : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have h3 : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr hπ
  rw [Real.sqrt_div hs.le, Real.sqrt_mul hc.le, mul_pow]
  field_simp

/-- The pointwise comparison on `[-π, π]`. -/
lemma abs_core_sub_gauss_le {s : ℝ} (hs : 0 ≤ s) (n x : ℝ) (hx : |x| ≤ π) :
    |Real.exp (s * (Real.cos x - 1)) * Real.cos (n * (x - Real.sin x)) -
        Real.exp (-(1 / 2 * s) * x ^ 2)| ≤
      n ^ 2 / 72 * (x ^ (2 * 3) * Real.exp (-(2 / π ^ 2 * s) * x ^ 2)) +
        s / 24 * (x ^ (2 * 2) * Real.exp (-(2 / π ^ 2 * s) * x ^ 2)) := by
  set X := s * (Real.cos x - 1) with hX
  set Y := -(1 / 2 * s) * x ^ 2 with hY
  set E := Real.exp (-(2 / π ^ 2 * s) * x ^ 2) with hE
  set u := n * (x - Real.sin x) with hu
  have hYX : Y ≤ X := by
    have h := mul_le_mul_of_nonneg_left
      (show -(x ^ 2 / 2) ≤ Real.cos x - 1 by linarith [Real.one_sub_sq_div_two_le_cos (x := x)]) hs
    have e : Y = s * -(x ^ 2 / 2) := by rw [hY]; ring
    rw [e]; exact h
  have hXa : X ≤ -(2 / π ^ 2 * s) * x ^ 2 := by
    have h := mul_le_mul_of_nonneg_left
      (show Real.cos x - 1 ≤ -(2 / π ^ 2 * x ^ 2) by linarith [Real.cos_le_one_sub_mul_cos_sq hx]) hs
    have e : -(2 / π ^ 2 * s) * x ^ 2 = s * -(2 / π ^ 2 * x ^ 2) := by ring
    rw [e]; exact h
  have hXY : X - Y ≤ s * x ^ 4 / 24 := by
    have h := mul_le_mul_of_nonneg_left
      (show Real.cos x - 1 + x ^ 2 / 2 ≤ x ^ 4 / 24 by linarith [cos_le_quartic x]) hs
    have e1 : X - Y = s * (Real.cos x - 1 + x ^ 2 / 2) := by rw [hX, hY]; ring
    have e2 : s * x ^ 4 / 24 = s * (x ^ 4 / 24) := by ring
    rw [e1, e2]; exact h
  have hexpX : Real.exp X ≤ E := Real.exp_le_exp.mpr hXa
  have hsin : (x - Real.sin x) ^ 2 ≤ x ^ 6 / 36 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) (abs_sub_sin_le x) 2
    rw [sq_abs] at h
    have e : (|x| ^ 3 / 6) ^ 2 = x ^ 6 / 36 := by
      have : (|x| ^ 3) ^ 2 = x ^ 6 := by
        rw [← pow_mul, show 3 * 2 = 2 * 3 by rfl, pow_mul, sq_abs]; ring
      rw [div_pow, this]; norm_num
    rw [e] at h; exact h
  have hc : |Real.cos u - 1| ≤ n ^ 2 * x ^ 6 / 72 := by
    have h1 : 1 - u ^ 2 / 2 ≤ Real.cos u := Real.one_sub_sq_div_two_le_cos
    have h2 : Real.cos u ≤ 1 := Real.cos_le_one u
    have hu2 : u ^ 2 ≤ n ^ 2 * (x ^ 6 / 36) := by
      rw [hu, mul_pow]; exact mul_le_mul_of_nonneg_left hsin (sq_nonneg n)
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hsplit : Real.exp X * Real.cos u - Real.exp Y =
      Real.exp X * (Real.cos u - 1) + (Real.exp X - Real.exp Y) := by ring
  have hXYn : 0 ≤ Real.exp X - Real.exp Y := sub_nonneg.mpr (Real.exp_le_exp.mpr hYX)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hA : |Real.exp X * (Real.cos u - 1)| ≤ E * (n ^ 2 * x ^ 6 / 72) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos X)]
    exact mul_le_mul hexpX hc (abs_nonneg _) hE0
  have hB : Real.exp X - Real.exp Y ≤ s * x ^ 4 / 24 * E := by
    refine (exp_sub_exp_le X Y).trans ?_
    exact mul_le_mul hXY hexpX (Real.exp_pos _).le (by positivity)
  calc |Real.exp X * Real.cos u - Real.exp Y|
      = |Real.exp X * (Real.cos u - 1) + (Real.exp X - Real.exp Y)| := by rw [hsplit]
    _ ≤ |Real.exp X * (Real.cos u - 1)| + |Real.exp X - Real.exp Y| := abs_add_le _ _
    _ ≤ E * (n ^ 2 * x ^ 6 / 72) + s * x ^ 4 / 24 * E := by
        rw [abs_of_nonneg hXYn]; exact add_le_add hA hB
    _ = n ^ 2 / 72 * (x ^ (2 * 3) * E) + s / 24 * (x ^ (2 * 2) * E) := by ring

/-- The core estimate: `|√(s/2π) ∫_{-π}^{π} e^{s(cos θ-1)} cos(n(θ - sin θ)) dθ - 1| ≤ C/s`
whenever `n² ≤ s²`. -/
theorem abs_sqrt_mul_integral_sub_one_le {s : ℝ} (hs : 0 < s) {n : ℝ} (hn : n ^ 2 ≤ s ^ 2) :
    |Real.sqrt (s / (2 * π)) *
        (∫ x in (-π)..π, Real.exp (s * (Real.cos x - 1)) * Real.cos (n * (x - Real.sin x))) - 1| ≤
      debyeConst / s := by
  have hπ := Real.pi_pos
  set a := 2 / π ^ 2 * s with ha
  set b := 1 / 2 * s with hb
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  set w : ℝ → ℝ := fun x => Real.exp (s * (Real.cos x - 1)) * Real.cos (n * (x - Real.sin x))
    with hw
  set g : ℝ → ℝ := fun x => Real.exp (-b * x ^ 2) with hg
  set H₁ : ℝ → ℝ := fun x => n ^ 2 / 72 * (x ^ (2 * 3) * Real.exp (-a * x ^ 2)) +
    s / 24 * (x ^ (2 * 2) * Real.exp (-a * x ^ 2)) with hH₁
  set H₂ : ℝ → ℝ := fun x => 1 / π ^ 2 * (x ^ (2 * 1) * Real.exp (-b * x ^ 2)) with hH₂
  have hwc : Continuous w := by simp only [hw]; fun_prop
  have hgi : Integrable g := integrable_exp_neg_mul_sq hb0
  have hH₁i : Integrable H₁ :=
    ((integrable_pow_two_mul_mul_exp_neg_mul_sq 3 ha0).const_mul _).add
      ((integrable_pow_two_mul_mul_exp_neg_mul_sq 2 ha0).const_mul _)
  have hH₂i : Integrable H₂ := (integrable_pow_two_mul_mul_exp_neg_mul_sq 1 hb0).const_mul _
  have hH₁0 : ∀ x, 0 ≤ H₁ x := fun x => by
    simp only [hH₁, pow_mul]; positivity
  have hH₂0 : ∀ x, 0 ≤ H₂ x := fun x => by
    simp only [hH₂, pow_mul]; positivity
  have hpt1 : ∀ x ∈ Ioc (-π) π, |w x - g x| ≤ H₁ x := fun x hx => by
    have hxπ : |x| ≤ π := abs_le.mpr ⟨hx.1.le, hx.2⟩
    have h := abs_core_sub_gauss_le hs.le n x hxπ
    simp only [hw, hg, hH₁, ha, hb]
    exact h
  have hpt2 : ∀ x ∈ (Ioc (-π) π)ᶜ, g x ≤ H₂ x := fun x hx => by
    have hx2 : π ^ 2 ≤ x ^ 2 := by
      simp only [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hx
      rcases hx with h | h
      · nlinarith
      · nlinarith
    simp only [hg, hH₂]
    have he := (Real.exp_pos (-b * x ^ 2)).le
    have h1 : 1 ≤ x ^ (2 * 1) / π ^ 2 := by
      rw [le_div_iff₀ (by positivity), one_mul, mul_one]; exact hx2
    calc Real.exp (-b * x ^ 2) = 1 * Real.exp (-b * x ^ 2) := (one_mul _).symm
      _ ≤ x ^ (2 * 1) / π ^ 2 * Real.exp (-b * x ^ 2) := mul_le_mul_of_nonneg_right h1 he
      _ = 1 / π ^ 2 * (x ^ (2 * 1) * Real.exp (-b * x ^ 2)) := by ring
  have hJ : ∫ x in (-π)..π, w x = ∫ x in Ioc (-π) π, w x :=
    intervalIntegral.integral_of_le (by linarith)
  have hG : ∫ x, g x = Real.sqrt (π / b) := integral_gaussian b
  have hq : Real.sqrt (s / (2 * π)) * Real.sqrt (π / b) = 1 := by
    rw [← Real.sqrt_mul (by positivity)]
    have : s / (2 * π) * (π / b) = 1 := by rw [hb]; field_simp
    rw [this, Real.sqrt_one]
  have hsplit := integral_add_compl (measurableSet_Ioc : MeasurableSet (Ioc (-π) π)) hgi
  have hwI : IntegrableOn w (Ioc (-π) π) := (hwc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hgI : IntegrableOn g (Ioc (-π) π) := hgi.integrableOn
  have hkey : |(∫ x in Ioc (-π) π, w x) - ∫ x, g x| ≤ (∫ x, H₁ x) + ∫ x, H₂ x := by
    rw [← hsplit, ← sub_sub, ← integral_sub hwI hgI]
    have e1 : |∫ x in Ioc (-π) π, (w x - g x)| ≤ ∫ x, H₁ x :=
      calc |∫ x in Ioc (-π) π, (w x - g x)| ≤ ∫ x in Ioc (-π) π, |w x - g x| :=
            abs_integral_le_integral_abs
        _ ≤ ∫ x in Ioc (-π) π, H₁ x :=
            setIntegral_mono_on (hwI.sub hgI).abs hH₁i.integrableOn measurableSet_Ioc hpt1
        _ ≤ ∫ x, H₁ x := setIntegral_le_integral hH₁i (Filter.Eventually.of_forall hH₁0)
    have e2 : 0 ≤ ∫ x in (Ioc (-π) π)ᶜ, g x :=
      setIntegral_nonneg measurableSet_Ioc.compl fun x _ => (Real.exp_pos _).le
    have e3 : ∫ x in (Ioc (-π) π)ᶜ, g x ≤ ∫ x, H₂ x :=
      (setIntegral_mono_on hgi.integrableOn hH₂i.integrableOn measurableSet_Ioc.compl hpt2).trans
        (setIntegral_le_integral hH₂i (Filter.Eventually.of_forall hH₂0))
    calc |(∫ x in Ioc (-π) π, (w x - g x)) - ∫ x in (Ioc (-π) π)ᶜ, g x|
        ≤ |∫ x in Ioc (-π) π, (w x - g x)| + |∫ x in (Ioc (-π) π)ᶜ, g x| := abs_sub _ _
      _ ≤ (∫ x, H₁ x) + ∫ x, H₂ x := by rw [abs_of_nonneg e2]; linarith
  have hI1 : ∫ x, H₁ x = n ^ 2 / 72 * (Real.Gamma ((3 : ℕ) + 1 / 2) / (a ^ 3 * Real.sqrt a)) +
      s / 24 * (Real.Gamma ((2 : ℕ) + 1 / 2) / (a ^ 2 * Real.sqrt a)) := by
    simp only [hH₁]
    rw [integral_add ((integrable_pow_two_mul_mul_exp_neg_mul_sq 3 ha0).const_mul _)
        ((integrable_pow_two_mul_mul_exp_neg_mul_sq 2 ha0).const_mul _),
      integral_const_mul, integral_const_mul, integral_pow_two_mul_mul_exp_neg_mul_sq 3 ha0,
      integral_pow_two_mul_mul_exp_neg_mul_sq 2 ha0]
  have hI2 : ∫ x, H₂ x = 1 / π ^ 2 * (Real.Gamma ((1 : ℕ) + 1 / 2) / (b ^ 1 * Real.sqrt b)) := by
    simp only [hH₂]
    rw [integral_const_mul, integral_pow_two_mul_mul_exp_neg_mul_sq 1 hb0]
  have hm3 := sqrt_div_mul_moment hs (show 0 < 2 / π ^ 2 by positivity) 3
  have hm2 := sqrt_div_mul_moment hs (show 0 < 2 / π ^ 2 by positivity) 2
  have hm1 := sqrt_div_mul_moment hs (show (0 : ℝ) < 1 / 2 by norm_num) 1
  rw [← ha] at hm3 hm2
  rw [← hb] at hm1
  set q := Real.sqrt (s / (2 * π)) with hqdef
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hone : q * ∫ x, g x = 1 := by rw [hG, hq]
  have hrw : q * (∫ x in (-π)..π, w x) - 1 = q * ((∫ x in Ioc (-π) π, w x) - ∫ x, g x) := by
    rw [mul_sub, hone, hJ]
  rw [hrw, abs_mul, abs_of_nonneg hq0]
  refine (mul_le_mul_of_nonneg_left hkey hq0).trans ?_
  rw [hI1, hI2, mul_add, mul_add]
  set T3 := Real.Gamma ((3 : ℕ) + 1 / 2) /
    (Real.sqrt (2 * π) * Real.sqrt (2 / π ^ 2) * (2 / π ^ 2) ^ 3) with hT3
  set T2 := Real.Gamma ((2 : ℕ) + 1 / 2) /
    (Real.sqrt (2 * π) * Real.sqrt (2 / π ^ 2) * (2 / π ^ 2) ^ 2) with hT2
  set T1 := Real.Gamma ((1 : ℕ) + 1 / 2) /
    (Real.sqrt (2 * π) * Real.sqrt (1 / 2) * (1 / 2) ^ 1) with hT1
  have e3 : q * (n ^ 2 / 72 * (Real.Gamma ((3 : ℕ) + 1 / 2) / (a ^ 3 * Real.sqrt a))) =
      n ^ 2 / 72 * (T3 / s ^ 3) := by rw [← hm3]; ring
  have e2 : q * (s / 24 * (Real.Gamma ((2 : ℕ) + 1 / 2) / (a ^ 2 * Real.sqrt a))) =
      s / 24 * (T2 / s ^ 2) := by rw [← hm2]; ring
  have e1 : q * (1 / π ^ 2 * (Real.Gamma ((1 : ℕ) + 1 / 2) / (b ^ 1 * Real.sqrt b))) =
      1 / π ^ 2 * (T1 / s ^ 1) := by rw [← hm1]; ring
  rw [e3, e2, e1]
  have hD : debyeConst = T3 / 72 + T2 / 24 + T1 / π ^ 2 := by
    simp only [debyeConst, hT3, hT2, hT1, Nat.cast_ofNat, Nat.cast_one]
    field_simp
  have hT3n : 0 ≤ T3 := by
    have : 0 < Real.Gamma ((3 : ℕ) + 1 / 2) := Real.Gamma_pos_of_pos (by positivity)
    simp only [hT3]; positivity
  have hs3 : n ^ 2 / 72 * (T3 / s ^ 3) ≤ T3 / 72 / s := by
    have : n ^ 2 / 72 * (T3 / s ^ 3) ≤ s ^ 2 / 72 * (T3 / s ^ 3) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    refine this.trans (le_of_eq ?_)
    field_simp
  have hs2 : s / 24 * (T2 / s ^ 2) = T2 / 24 / s := by field_simp
  have hs1 : 1 / π ^ 2 * (T1 / s ^ 1) = T1 / π ^ 2 / s := by field_simp
  rw [hs2, hs1, hD]
  have : (T3 / 72 + T2 / 24 + T1 / π ^ 2) / s = T3 / 72 / s + T2 / 24 / s + T1 / π ^ 2 / s := by
    ring
  rw [this]
  linarith

/-- `L_β(n)` on the integers: `(2π)^{-1/2} s^{-1/2} e^{-nr + s}` with `s = √(β² + n²)`,
`r = sinh⁻¹(n/β)`. -/
lemma debyeRe_eq {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    debyeRe β x = (Real.sqrt (2 * π))⁻¹ * (Real.sqrt (Real.sqrt (β ^ 2 + x ^ 2)))⁻¹ *
      Real.exp (-(x * Real.arsinh (x / β)) + Real.sqrt (β ^ 2 + x ^ 2)) := by
  have hs : β * Real.sqrt (1 + x ^ 2 / β ^ 2) = Real.sqrt (β ^ 2 + x ^ 2) := by
    rw [show β * Real.sqrt (1 + x ^ 2 / β ^ 2) = Real.sqrt (β ^ 2 * (1 + x ^ 2 / β ^ 2)) by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hβ.le]]
    congr 1
    field_simp
  unfold debyeRe
  rw [hs, Real.rpow_neg (Real.sqrt_nonneg _), ← Real.sqrt_eq_rpow, neg_mul]

/-- The ratio `I_β(n)/L_β(n)` as a normalized integral. -/
theorem besselCoeffRe_div_debyeRe {β : ℝ} (hβ : 0 < β) (n : ℤ) :
    besselCoeffRe β n / debyeRe β n =
      Real.sqrt (Real.sqrt (β ^ 2 + (n : ℝ) ^ 2) / (2 * π)) *
        ∫ x in (-π)..π, Real.exp (Real.sqrt (β ^ 2 + (n : ℝ) ^ 2) * (Real.cos x - 1)) *
          Real.cos (n * (x - Real.sin x)) := by
  set s := Real.sqrt (β ^ 2 + (n : ℝ) ^ 2) with hsdef
  set r := Real.arsinh (n / β) with hr
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hπ : 0 < 2 * π := by positivity
  set J := ∫ x in (-π)..π, Real.exp (s * (Real.cos x - 1)) * Real.cos (n * (x - Real.sin x))
    with hJ
  have h2π := two_pi_mul_besselCoeffRe hβ n
  have hint : (∫ x in (-π)..π, Real.exp (-(n * r)) * Real.exp (s * Real.cos x) *
      Real.cos (n * (x - Real.sin x))) = Real.exp (-(n * r)) * Real.exp s * J := by
    rw [hJ, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    have : Real.exp (s * Real.cos x) = Real.exp s * Real.exp (s * (Real.cos x - 1)) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  rw [hint] at h2π
  have hI : besselCoeffRe β n = Real.exp (-(n * r)) * Real.exp s * J / (2 * π) := by
    rw [← h2π]; field_simp
  rw [hI, debyeRe_eq hβ, ← hsdef, ← hr, Real.exp_add, Real.sqrt_div hs.le]
  have h1 : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h2 : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr hπ
  have he1 := Real.exp_pos (-(n * r))
  have he2 := Real.exp_pos s
  set c := Real.sqrt (2 * π) with hc
  have h3 : 2 * π = c ^ 2 := (Real.sq_sqrt hπ.le).symm
  rw [h3]
  field_simp

/-- **(B.12′)**, the uniform Debye bound: `|I_β(n)/L_β(n) - 1| ≤ debyeConst / √(β² + n²)` for
every `β > 0` and every integer `n`. -/
theorem abs_besselCoeffRe_div_debyeRe_sub_one_le {β : ℝ} (hβ : 0 < β) (n : ℤ) :
    |besselCoeffRe β n / debyeRe β n - 1| ≤ debyeConst / Real.sqrt (β ^ 2 + (n : ℝ) ^ 2) := by
  rw [besselCoeffRe_div_debyeRe hβ n]
  have hs : 0 < Real.sqrt (β ^ 2 + (n : ℝ) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  refine abs_sqrt_mul_integral_sub_one_le hs ?_
  rw [Real.sq_sqrt (by positivity)]
  linarith [sq_nonneg β]

/-- `|ln x| ≤ 2 |x - 1|` when `|x - 1| ≤ 1/2`. -/
lemma abs_log_le_two_mul_abs_sub_one {x : ℝ} (hx : |x - 1| ≤ 1 / 2) :
    |Real.log x| ≤ 2 * |x - 1| := by
  have hx1 := abs_le.mp hx
  have hpos : 0 < x := by linarith [hx1.1]
  have hup := Real.log_le_sub_one_of_pos hpos
  have hlow := Real.one_sub_inv_le_log_of_pos hpos
  set t := x⁻¹ with ht
  have hxt : x * t = 1 := mul_inv_cancel₀ hpos.ne'
  have ht0 : 0 < t := inv_pos.mpr hpos
  have ht2 : t ≤ 2 := by
    rw [ht, inv_le_comm₀ hpos (by norm_num)]; linarith [hx1.1]
  have e : 1 - t = (x - 1) * t := by linear_combination -hxt
  have hab1 := neg_abs_le (x - 1)
  have hab2 := le_abs_self (x - 1)
  have habs0 := abs_nonneg (x - 1)
  rw [abs_le]
  constructor
  · have h1 : -|x - 1| * t ≤ (x - 1) * t := mul_le_mul_of_nonneg_right hab1 ht0.le
    have h2 : |x - 1| * t ≤ |x - 1| * 2 := mul_le_mul_of_nonneg_left ht2 habs0
    linarith
  · linarith

/-- The coefficients of (B.14): `|ln I_β(n) - ln L_β(n)| ≤ 2 debyeConst / √(β² + n²)` once
`√(β² + n²) ≥ 2 debyeConst`. -/
theorem abs_logDefect_le {β : ℝ} (hβ : 0 < β) (n : ℤ)
    (h : 2 * debyeConst ≤ Real.sqrt (β ^ 2 + (n : ℝ) ^ 2)) :
    |logDefect β n| ≤ 2 * debyeConst / Real.sqrt (β ^ 2 + (n : ℝ) ^ 2) := by
  set s := Real.sqrt (β ^ 2 + (n : ℝ) ^ 2) with hsdef
  have hD := debyeConst_pos
  have hs : 0 < s := by linarith
  have hρ := abs_besselCoeffRe_div_debyeRe_sub_one_le hβ n
  rw [← hsdef] at hρ
  have hhalf : debyeConst / s ≤ 1 / 2 := by
    rw [div_le_iff₀ hs]; linarith
  have hI := besselCoeffRe_pos hβ n
  have hL := debyeRe_pos hβ (n : ℝ)
  have hlog : logDefect β n = Real.log (besselCoeffRe β n / debyeRe β n) := by
    unfold logDefect
    rw [Real.log_div hI.ne' hL.ne']
  rw [hlog]
  calc |Real.log (besselCoeffRe β n / debyeRe β n)|
      ≤ 2 * |besselCoeffRe β n / debyeRe β n - 1| :=
        abs_log_le_two_mul_abs_sub_one (hρ.trans hhalf)
    _ ≤ 2 * (debyeConst / s) := by linarith
    _ = 2 * debyeConst / s := by ring

/-- For `β ≥ 2 debyeConst`, every coefficient of (B.14) is at most `2 debyeConst / β`. -/
theorem abs_logDefect_le_of_le {β : ℝ} (hβ : 2 * debyeConst ≤ β) (n : ℤ) :
    |logDefect β n| ≤ 2 * debyeConst / β := by
  have hD := debyeConst_pos
  have hβ0 : 0 < β := by linarith
  have hsβ : β ≤ Real.sqrt (β ^ 2 + (n : ℝ) ^ 2) := by
    calc β = Real.sqrt (β ^ 2) := (Real.sqrt_sq hβ0.le).symm
      _ ≤ Real.sqrt (β ^ 2 + (n : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  refine (abs_logDefect_le hβ0 n (hβ.trans hsβ)).trans ?_
  exact div_le_div_of_nonneg_left (by linarith) hβ0 hsβ

/-- The coefficients of (B.14) are bounded for every `β > 0`. -/
theorem exists_abs_logDefect_le {β : ℝ} (hβ : 0 < β) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ, |logDefect β n| ≤ M := by
  have hD := debyeConst_pos
  set N : ℤ := ⌈2 * debyeConst⌉ with hN
  refine ⟨1 + ∑ k ∈ Finset.Icc (-N) N, |logDefect β k|,
    add_nonneg zero_le_one (Finset.sum_nonneg fun k _ => abs_nonneg _), fun n => ?_⟩
  have hsum0 : 0 ≤ ∑ k ∈ Finset.Icc (-N) N, |logDefect β k| :=
    Finset.sum_nonneg fun k _ => abs_nonneg _
  by_cases hn : 2 * debyeConst ≤ |(n : ℝ)|
  · have hsn : |(n : ℝ)| ≤ Real.sqrt (β ^ 2 + (n : ℝ) ^ 2) :=
      Real.abs_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))
    have hs := hn.trans hsn
    have hspos : 0 < Real.sqrt (β ^ 2 + (n : ℝ) ^ 2) := by linarith
    have h1 : 2 * debyeConst / Real.sqrt (β ^ 2 + (n : ℝ) ^ 2) ≤ 1 := by
      rw [div_le_one hspos]; exact hs
    linarith [abs_logDefect_le hβ n hs]
  · push Not at hn
    have hceil : 2 * debyeConst ≤ (N : ℝ) := Int.le_ceil _
    have hmem : n ∈ Finset.Icc (-N) N := by
      have h1 := neg_abs_le (n : ℝ)
      have h2 := le_abs_self (n : ℝ)
      have hlo : ((-N : ℤ) : ℝ) < n := by push_cast; linarith
      have hhi : (n : ℝ) < (N : ℝ) := by linarith
      rw [Finset.mem_Icc]
      exact ⟨(Int.cast_lt.mp hlo).le, (Int.cast_lt.mp hhi).le⟩
    have := Finset.single_le_sum (f := fun k => |logDefect β k|) (fun k _ => abs_nonneg _) hmem
    linarith

end FroehlichSpencer.BKT.Rotator.BesselInterp
