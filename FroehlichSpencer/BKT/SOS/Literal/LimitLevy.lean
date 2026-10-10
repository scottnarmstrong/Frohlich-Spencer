/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.LimitDomination

/-!
# `L_β` is a Gaussian scale mixture (the comb-inserted SOS construction)

The Cauchy–Schlömilch substitution `s = ax − b/x` and the involution `x ↦ κ/x` give, for
`P, Q > 0` (`lintegral_levy`),

`∫₀^∞ x^{−2} e^{−P/x² − Qx²} dx = √π/(2√P) · e^{−2√(PQ)}`.

With `q₀ = β^{−2/3}`, `L_β(t) = e^{−β√(q₀+t²)}` (`Lw_eq`), so for the mixing weight
`w(x) = (β/√π) x^{−2} e^{−β²/(4x²) − q₀x²}` on `x > 0` (`mixW`) and `0 ≤ λ < β²/2`,

`∫₀^∞ w(x) e^{λ/(2x²)} e^{−x²t²} dx = (β/β_λ) e^{−β_λ√(q₀+t²)}`, `β_λ = √(β² − 2λ)`
(`lintegral_mixW`); at `λ = 0` this is `L_β(t)`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

/-- `∫ e^{−s²} ds = √π`. -/
theorem lintegral_exp_neg_sq :
    ∫⁻ s : ℝ, ENNReal.ofReal (Real.exp (-s ^ 2)) = ENNReal.ofReal (Real.sqrt π) := by
  have h := integral_gaussian 1
  have hi := integrable_exp_neg_mul_sq (b := 1) one_pos
  simp only [neg_mul, one_mul, div_one] at h hi
  rw [← h, ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun s => (Real.exp_pos _).le)]

/-- The substitution `s = ax − b/x`. -/
theorem lintegral_cauchy_schlomilch {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (a + b / x ^ 2) *
      ENNReal.ofReal (Real.exp (-(a * x - b / x) ^ 2)) = ENNReal.ofReal (Real.sqrt π) := by
  set f : ℝ → ℝ := fun x => a * x - b / x with hf
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt f (a + b / x ^ 2) (Ioi 0) x := by
    intro x hx
    have hx0 : x ≠ 0 := (mem_Ioi.mp hx).ne'
    have h1 : HasDerivAt (fun y : ℝ => a * y) a x := by
      simpa using (hasDerivAt_id x).const_mul a
    have h2 : HasDerivAt (fun y : ℝ => b * y⁻¹) (b * -(x ^ 2)⁻¹) x :=
      (hasDerivAt_inv hx0).const_mul b
    have h3 := h1.sub h2
    refine (h3.congr_deriv ?_).hasDerivWithinAt.congr_of_mem (fun y _ => ?_) hx
    · field_simp; ring
    · simp only [hf, div_eq_mul_inv, Pi.sub_apply]
  have hinj : InjOn f (Ioi 0) := by
    intro x hx y hy hxy
    have hx0 := mem_Ioi.mp hx
    have hy0 := mem_Ioi.mp hy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : f x < f y := by
        simp only [hf]
        have : b / y < b / x := div_lt_div_of_pos_left hb hx0 h
        nlinarith
      exact absurd hxy this.ne
    · have : f y < f x := by
        simp only [hf]
        have : b / x < b / y := div_lt_div_of_pos_left hb hy0 h
        nlinarith
      exact absurd hxy this.ne'
  have himg : f '' Ioi 0 = univ := by
    refine eq_univ_of_forall fun s => ?_
    set D := Real.sqrt (s ^ 2 + 4 * a * b) with hD
    have hD2 : D ^ 2 = s ^ 2 + 4 * a * b := Real.sq_sqrt (by positivity)
    have hDs : |s| < D := by
      rw [hD, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_lt_sqrt (sq_nonneg s) (by nlinarith)
    have hpos : 0 < (s + D) / (2 * a) := by
      apply div_pos _ (by positivity)
      linarith [neg_abs_le s]
    refine ⟨(s + D) / (2 * a), hpos, ?_⟩
    simp only [hf]
    have hsD : s + D ≠ 0 := by linarith [neg_abs_le s]
    field_simp
    nlinarith
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj
    (fun s => ENNReal.ofReal (Real.exp (-s ^ 2)))
  rw [himg, Measure.restrict_univ, lintegral_exp_neg_sq] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [abs_of_pos (by have := mem_Ioi.mp hx; positivity)]

/-- The involution `x ↦ κ/x` of `(0, ∞)`. -/
theorem lintegral_inv_subst {κ : ℝ} (hκ : 0 < κ) (G : ℝ → ℝ≥0∞) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (κ / x ^ 2) * G (κ / x) = ∫⁻ y in Ioi (0 : ℝ), G y := by
  set f : ℝ → ℝ := fun x => κ / x with hf
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt f (-(κ / x ^ 2)) (Ioi 0) x := by
    intro x hx
    have hx0 : x ≠ 0 := (mem_Ioi.mp hx).ne'
    have h2 : HasDerivAt (fun y : ℝ => κ * y⁻¹) (κ * -(x ^ 2)⁻¹) x :=
      (hasDerivAt_inv hx0).const_mul κ
    refine (h2.congr_deriv ?_).hasDerivWithinAt.congr_of_mem (fun y _ => ?_) hx
    · field_simp
    · simp only [hf, div_eq_mul_inv]
  have hinj : InjOn f (Ioi 0) := by
    intro x hx y hy hxy
    simp only [hf] at hxy
    have hx0 := (mem_Ioi.mp hx).ne'
    have hy0 := (mem_Ioi.mp hy).ne'
    field_simp at hxy
    nlinarith [hxy]
  have himg : f '' Ioi 0 = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact div_pos hκ (mem_Ioi.mp hx)
    · intro hy
      refine ⟨κ / y, div_pos hκ (mem_Ioi.mp hy), ?_⟩
      simp only [hf]
      field_simp [(mem_Ioi.mp hy).ne']
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj G
  rw [himg] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [abs_neg, abs_of_pos (by have := mem_Ioi.mp hx; positivity)]

/-- **The Lévy integral** `∫₀^∞ x^{−2} e^{−P/x² − Qx²} dx = √π/(2√P) e^{−2√(PQ)}`. -/
theorem lintegral_levy {P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(P / x ^ 2) - Q * x ^ 2) / x ^ 2) =
      ENNReal.ofReal (Real.sqrt π / (2 * Real.sqrt P) * Real.exp (-(2 * Real.sqrt (P * Q)))) := by
  set a := Real.sqrt Q with ha
  set b := Real.sqrt P with hb
  have ha0 : 0 < a := Real.sqrt_pos.mpr hQ
  have hb0 : 0 < b := Real.sqrt_pos.mpr hP
  have ha2 : a ^ 2 = Q := Real.sq_sqrt hQ.le
  have hb2 : b ^ 2 = P := Real.sq_sqrt hP.le
  have hPQ : Real.sqrt (P * Q) = b * a := by rw [Real.sqrt_mul hP.le]
  set g : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-(a * x - b / x) ^ 2)) with hg
  have hgm : Measurable g := ENNReal.measurable_ofReal.comp (by fun_prop)
  -- the two substitutions
  have h1 := lintegral_cauchy_schlomilch ha0 hb0
  have h2 : ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (b / x ^ 2) * g x =
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal a * g x := by
    have hκ : 0 < b / a := div_pos hb0 ha0
    rw [← lintegral_inv_subst hκ (fun y => ENNReal.ofReal a * g y)]
    refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : x ≠ 0 := (mem_Ioi.mp hx).ne'
    have hgx : g (b / a / x) = g x := by
      simp only [hg]
      congr 3
      field_simp
      ring
    conv_rhs => rw [hgx, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      show b / a / x ^ 2 * a = b / x ^ 2 by field_simp]
  have hsplit : ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (a + b / x ^ 2) * g x =
      (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal a * g x) +
        ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (b / x ^ 2) * g x := by
    calc ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (a + b / x ^ 2) * g x
        = ∫⁻ x in Ioi (0 : ℝ), (ENNReal.ofReal a * g x + ENNReal.ofReal (b / x ^ 2) * g x) :=
          setLIntegral_congr_fun measurableSet_Ioi fun x hx => by
            rw [ENNReal.ofReal_add ha0.le (by positivity), add_mul]
      _ = _ := lintegral_add_left (f := fun x => ENNReal.ofReal a * g x)
          (measurable_const.mul hgm) _
  rw [h1, h2] at hsplit
  have hI : ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal a * g x = ENNReal.ofReal (Real.sqrt π / 2) := by
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat,
      ENNReal.eq_div_iff two_ne_zero ENNReal.ofNat_ne_top, two_mul]
    exact hsplit.symm
  have hI2 : ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (b / x ^ 2) * g x =
      ENNReal.ofReal (Real.sqrt π / 2) := by rw [h2, hI]
  -- assemble
  have hpt : ∀ x ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(P / x ^ 2) - Q * x ^ 2) / x ^ 2) =
        ENNReal.ofReal (Real.exp (-(2 * Real.sqrt (P * Q))) / b) *
          (ENNReal.ofReal (b / x ^ 2) * g x) := by
    intro x hx
    have hx0 : x ≠ 0 := (mem_Ioi.mp hx).ne'
    simp only [hg]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have he : Real.exp (-(P / x ^ 2) - Q * x ^ 2) =
        Real.exp (-(2 * Real.sqrt (P * Q))) * Real.exp (-(a * x - b / x) ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      rw [hPQ, ← ha2, ← hb2]
      field_simp
      ring
    rw [he]
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_const_mul _ (by fun_prop), hI2,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-! ## The mixture for `L_β` -/

/-- `q₀ = β^{−2/3}`. -/
def mixQ0 (β : ℝ) : ℝ := (β ^ (2 / 3 : ℝ))⁻¹

theorem mixQ0_pos {β : ℝ} (hβ : 0 < β) : 0 < mixQ0 β :=
  inv_pos.mpr (Real.rpow_pos_of_pos hβ _)

/-- `L_β(t) = e^{−β√(q₀+t²)}`. -/
theorem Lw_eq {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    Lw β t = Real.exp (-(β * Real.sqrt (mixQ0 β + t ^ 2))) := by
  unfold Lw mixQ0
  set b := β ^ (2 / 3 : ℝ) with hbdef
  have hb : 0 < b := Real.rpow_pos_of_pos hβ _
  have hβb := rpow_two_thirds_mul_sqrt hβ
  rw [← hbdef] at hβb
  have hsq : Real.sqrt (b⁻¹ + t ^ 2) = Real.sqrt (1 + b * t ^ 2) / Real.sqrt b := by
    rw [← Real.sqrt_div' _ hb.le]
    congr 1
    field_simp
  rw [hsq]
  congr 1
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  rw [← hβb]
  field_simp

/-- The mixing weight `w(x) = (β/√π) x^{−2} e^{−β²/(4x²) − q₀x²}`. -/
def mixW (β x : ℝ) : ℝ :=
  β / Real.sqrt π * (Real.exp (-((β ^ 2 / 4) / x ^ 2) - mixQ0 β * x ^ 2) / x ^ 2)

theorem mixW_nonneg {β : ℝ} (hβ : 0 ≤ β) (x : ℝ) : 0 ≤ mixW β x := by
  unfold mixW; positivity

/-- **The tilted mixture**: for `λ < β²/2`,
`∫₀^∞ w(x) e^{λ/(2x²)} e^{−x²t²} dx = (β/β_λ) e^{−β_λ√(q₀+t²)}`, `β_λ = √(β² − 2λ)`. -/
theorem lintegral_mixW {β : ℝ} (hβ : 0 < β) {lam : ℝ} (hl : 2 * lam < β ^ 2)
    (t : ℝ) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (mixW β x * Real.exp (lam / (2 * x ^ 2)) *
        Real.exp (-(x ^ 2 * t ^ 2))) =
      ENNReal.ofReal (β / Real.sqrt (β ^ 2 - 2 * lam) *
        Real.exp (-(Real.sqrt (β ^ 2 - 2 * lam) * Real.sqrt (mixQ0 β + t ^ 2)))) := by
  have hP : 0 < (β ^ 2 - 2 * lam) / 4 := by linarith
  have hQ : 0 < mixQ0 β + t ^ 2 := by have := mixQ0_pos hβ; positivity
  have hpt : ∀ x ∈ Ioi (0 : ℝ), ENNReal.ofReal (mixW β x * Real.exp (lam / (2 * x ^ 2)) *
      Real.exp (-(x ^ 2 * t ^ 2))) = ENNReal.ofReal (β / Real.sqrt π) *
        ENNReal.ofReal (Real.exp (-(((β ^ 2 - 2 * lam) / 4) / x ^ 2) -
          (mixQ0 β + t ^ 2) * x ^ 2) / x ^ 2) := by
    intro x hx
    have hx0 : x ≠ 0 := (mem_Ioi.mp hx).ne'
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold mixW
    have he : Real.exp (-((β ^ 2 / 4) / x ^ 2) - mixQ0 β * x ^ 2) *
        Real.exp (lam / (2 * x ^ 2)) * Real.exp (-(x ^ 2 * t ^ 2)) =
        Real.exp (-(((β ^ 2 - 2 * lam) / 4) / x ^ 2) - (mixQ0 β + t ^ 2) * x ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      field_simp
      ring
    rw [← he]
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_const_mul _ (by fun_prop),
    lintegral_levy hP hQ, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have h4 : Real.sqrt ((β ^ 2 - 2 * lam) / 4) = Real.sqrt (β ^ 2 - 2 * lam) / 2 := by
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have h5 : Real.sqrt ((β ^ 2 - 2 * lam) / 4 * (mixQ0 β + t ^ 2)) =
      Real.sqrt (β ^ 2 - 2 * lam) / 2 * Real.sqrt (mixQ0 β + t ^ 2) := by
    rw [Real.sqrt_mul hP.le, h4]
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hs : 0 < Real.sqrt (β ^ 2 - 2 * lam) := Real.sqrt_pos.mpr (by linarith)
  rw [h4, h5]
  field_simp

/-- At `λ = 0` the mixture is `L_β`. -/
theorem lintegral_mixW_zero {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (mixW β x * Real.exp (-(x ^ 2 * t ^ 2))) =
      ENNReal.ofReal (Lw β t) := by
  have h := lintegral_mixW hβ (lam := 0) (by rw [mul_zero]; positivity) t
  simp only [mul_zero, sub_zero, zero_div, Real.exp_zero, mul_one,
    Real.sqrt_sq hβ.le, div_self hβ.ne', one_mul] at h
  rw [h, Lw_eq hβ]

/-- The tilted mixture is at most `K₀ e^{δ|t|} L_β(t)`, `K₀ = (β/β_λ)e^{δ√q₀}`, `δ = β − β_λ`. -/
theorem mixTilt_le {β : ℝ} (hβ : 0 < β) {lam : ℝ} (hl0 : 0 ≤ lam) (hl : 2 * lam < β ^ 2)
    (t : ℝ) :
    β / Real.sqrt (β ^ 2 - 2 * lam) *
        Real.exp (-(Real.sqrt (β ^ 2 - 2 * lam) * Real.sqrt (mixQ0 β + t ^ 2))) ≤
      β / Real.sqrt (β ^ 2 - 2 * lam) *
        Real.exp ((β - Real.sqrt (β ^ 2 - 2 * lam)) * Real.sqrt (mixQ0 β)) *
        Real.exp ((β - Real.sqrt (β ^ 2 - 2 * lam)) * |t|) * Lw β t := by
  rw [Lw_eq hβ]
  set s := Real.sqrt (β ^ 2 - 2 * lam) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsβ : s ≤ β := by
    rw [hs, Real.sqrt_le_left]
    · linarith
    · exact hβ.le
  have hq := mixQ0_pos hβ
  have hroot : Real.sqrt (mixQ0 β + t ^ 2) ≤ Real.sqrt (mixQ0 β) + |t| := by
    rw [Real.sqrt_le_left (by positivity)]
    have h1 := Real.sq_sqrt hq.le
    nlinarith [Real.sqrt_nonneg (mixQ0 β), abs_nonneg t, sq_abs t]
  rw [mul_assoc (β / s * _), ← Real.exp_add, mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have hd : 0 ≤ β - s := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hroot hd]

end FroehlichSpencer.BKT.SOS.Literal

end
