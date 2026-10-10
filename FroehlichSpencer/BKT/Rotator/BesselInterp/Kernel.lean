/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.BesselInterp.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# The kernel `sin²(πz)/(π²z²)` and shifted-kernel series

The kernel `sincSq` of FS81 (B.14) is entire, equals `δ_{k0}` at integers, is real and even on the
real axis, and satisfies `‖sincSq ζ‖ ≤ 2 e^{2π|Im ζ|}/(1 + (Re ζ)²)`. Cauchy estimates on circles of
radius one transfer bounds of this shape to derivatives. For bounded coefficients `c`, the series
`Σₙ c n · k (z - n)` of any entire `k` with such a bound is entire, can be differentiated termwise,
and is bounded by `‖c‖_∞ · A · e^{2π|Im z|} · 3 Σ_k (1+k²)⁻¹`, uniformly in `Re z`.
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.BesselInterp

open Complex Metric
open scoped Real

/-! ### Values on the integers and on the real axis -/

lemma sincSq_intCast (k : ℤ) : sincSq k = if k = 0 then 1 else 0 := by
  unfold sincSq
  by_cases hk : k = 0
  · simp [hk]
  · have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have : Complex.sin (π * k) = 0 := by rw [mul_comm]; exact Complex.sin_int_mul_pi k
    simp [hk, hk', this]

lemma sincSq_ofReal (y : ℝ) : sincSq y = ((Real.sinc (π * y)) ^ 2 : ℝ) := by
  unfold sincSq
  by_cases hy : y = 0
  · simp [hy, Real.sinc_zero]
  · have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
    have hpy : π * y ≠ 0 := mul_ne_zero Real.pi_ne_zero hy
    rw [ite_eq_right hy', Real.sinc_of_ne_zero hpy]
    push_cast
    ring

lemma sincSq_neg (z : ℂ) : sincSq (-z) = sincSq z := by
  unfold sincSq
  by_cases hz : z = 0
  · simp [hz]
  · simp [hz, mul_neg, Complex.sin_neg]

lemma sincSq_zero : sincSq 0 = 1 := by simp [sincSq]


/-! ### Norm bounds and holomorphy -/

lemma norm_cexp_mul_I_le (w : ℂ) : ‖Complex.exp (w * I)‖ ≤ Real.exp |w.im| := by
  rw [Complex.norm_exp]; simp only [mul_re, I_re, mul_zero, I_im, mul_one, zero_sub]
  exact Real.exp_le_exp.mpr (neg_le_abs _)

lemma norm_cexp_neg_mul_I_le (w : ℂ) : ‖Complex.exp (-w * I)‖ ≤ Real.exp |w.im| := by
  rw [Complex.norm_exp]; simp only [mul_re, neg_re, I_re, mul_zero, neg_im, I_im, mul_one,
    zero_sub, neg_neg]
  exact Real.exp_le_exp.mpr (le_abs_self _)

lemma norm_sin_le_exp (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  have h : Complex.sin w = (Complex.exp (-w * I) - Complex.exp (w * I)) * I / 2 := by
    rw [← two_sin]; ring
  rw [h, norm_div, norm_mul, norm_I, mul_one, Complex.norm_two]
  have := norm_sub_le (Complex.exp (-w * I)) (Complex.exp (w * I))
  linarith [norm_cexp_mul_I_le w, norm_cexp_neg_mul_I_le w]

lemma norm_cos_le_exp (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  have h : Complex.cos w = (Complex.exp (w * I) + Complex.exp (-w * I)) / 2 := by
    rw [← two_cos]; ring
  rw [h, norm_div, Complex.norm_two]
  have := norm_add_le (Complex.exp (w * I)) (Complex.exp (-w * I))
  linarith [norm_cexp_mul_I_le w, norm_cexp_neg_mul_I_le w]

/-- `sin w / w = ∫₀¹ cos (w t) dt`. -/
lemma integral_cos_mul_eq (w : ℂ) (hw : w ≠ 0) :
    ∫ t in (0 : ℝ)..1, Complex.cos (w * t) = Complex.sin w / w := by
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => Complex.sin (w * t) / w) (Complex.cos (w * t)) t := by
    intro t _
    have h1 : HasDerivAt (fun u : ℂ => Complex.sin (w * u) / w) (Complex.cos (w * t) * w / w) t :=
      ((Complex.hasDerivAt_sin _).comp _ ((hasDerivAt_id _).const_mul w |>.congr_deriv
        (by simp))).div_const w
    rw [mul_div_cancel_right₀ _ hw] at h1
    exact h1.comp_ofReal
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ => Complex.cos (w * t)).intervalIntegrable _ _)]
  simp

lemma norm_sin_div_le (w : ℂ) (hw : w ≠ 0) : ‖Complex.sin w / w‖ ≤ Real.exp |w.im| := by
  rw [← integral_cos_mul_eq w hw]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun t : ℝ => Complex.cos (w * t)) (C := Real.exp |w.im|) (fun t ht => by
      rw [Set.uIoc_of_le zero_le_one] at ht
      refine (norm_cos_le_exp _).trans (Real.exp_le_exp.mpr ?_)
      rw [mul_im, ofReal_im, ofReal_re, mul_zero, zero_add, abs_mul, abs_of_pos ht.1]
      exact mul_le_of_le_one_right (abs_nonneg _) ht.2)
  simpa using this

lemma sincSq_of_ne {z : ℂ} (hz : z ≠ 0) : sincSq z = (Complex.sin (π * z) / (π * z)) ^ 2 := by
  rw [sincSq, ite_eq_right hz, div_pow, mul_pow]

lemma norm_sincSq_le (z : ℂ) : ‖sincSq z‖ ≤ Real.exp (2 * π * |z.im|) := by
  by_cases hz : z = 0
  · simp [sincSq, hz]
  · have hpz : (π : ℂ) * z ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) hz
    rw [sincSq_of_ne hz, norm_pow]
    have h := norm_sin_div_le _ hpz
    have hi : |((π : ℂ) * z).im| = π * |z.im| := by
      rw [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, abs_mul, abs_of_pos Real.pi_pos]
    rw [hi] at h
    calc ‖Complex.sin (π * z) / (π * z)‖ ^ 2 ≤ Real.exp (π * |z.im|) ^ 2 := by gcongr
      _ = Real.exp (2 * π * |z.im|) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf

lemma norm_sincSq_le_div {z : ℂ} (hz : z ≠ 0) :
    ‖sincSq z‖ ≤ Real.exp (2 * π * |z.im|) / (π ^ 2 * ‖z‖ ^ 2) := by
  rw [sincSq, ite_eq_right hz]
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  have hz' : 0 < π ^ 2 * ‖z‖ ^ 2 := by positivity
  gcongr
  have h := norm_sin_le_exp ((π : ℂ) * z)
  rw [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, abs_mul, abs_of_pos Real.pi_pos] at h
  calc ‖Complex.sin (π * z)‖ ^ 2 ≤ Real.exp (π * |z.im|) ^ 2 := by gcongr
    _ = Real.exp (2 * π * |z.im|) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf

/-- The kernel is entire (removable singularity via `dslope`). -/
lemma differentiable_sincSq : Differentiable ℂ sincSq := by
  set f : ℂ → ℂ := fun z => Complex.sin (π * z)
  have hf : Differentiable ℂ f := by fun_prop
  have hd : Differentiable ℂ (dslope f 0) := by
    rw [← differentiableOn_univ, differentiableOn_dslope Filter.univ_mem]
    exact hf.differentiableOn
  have heq : sincSq = fun z => (dslope f 0 z / π) ^ 2 := by
    funext z
    by_cases hz : z = 0
    · subst hz
      have hderiv : deriv f 0 = π := by
        have := ((Complex.hasDerivAt_sin _).comp (0 : ℂ)
          ((hasDerivAt_id (0 : ℂ)).const_mul (π : ℂ))).deriv
        simp only [Function.comp_def, id, mul_zero, Complex.cos_zero, one_mul, mul_one] at this
        exact this
      rw [dslope_same, hderiv, div_self (by exact_mod_cast Real.pi_ne_zero)]
      simp [sincSq]
    · rw [dslope_of_ne _ hz, slope_def_field, sincSq_of_ne hz]
      simp only [f, mul_zero, Complex.sin_zero, sub_zero]
      field_simp
  rw [heq]
  exact (hd.div_const _).pow 2

/-! ### Summable majorants -/

lemma summable_shift_inv_sq' (x₀ : ℝ) : Summable fun n : ℤ => 5 / (1 + (x₀ - n) ^ 2) := by
  have hs : Summable fun n : ℤ => 20 * (1 + x₀ ^ 2) * (1 / |(n : ℝ) + 1 / 2| ^ (2 : ℝ)) :=
    ((Real.summable_one_div_int_add_rpow (1 / 2) 2).mpr one_lt_two).mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  have hpos : 0 < |(n : ℝ) + 1 / 2| := by
    rw [abs_pos]; intro h
    have : (2 * n + 1 : ℝ) = 0 := by linarith
    have : (2 * n + 1 : ℤ) = 0 := by exact_mod_cast this
    omega
  rw [Real.rpow_two, sq_abs]
  have hsq : ((n : ℝ) + 1 / 2) ^ 2 ≤ 4 * (1 + x₀ ^ 2) * (1 + (x₀ - n) ^ 2) := by
    nlinarith [sq_nonneg (x₀ * (x₀ - n) + 1), sq_nonneg (x₀ + (x₀ - n)), sq_nonneg (x₀ - n),
      sq_nonneg ((n : ℝ) - 1 / 2)]
  have h1 : 0 < ((n : ℝ) + 1 / 2) ^ 2 := by rw [← sq_abs]; positivity
  have h2 : 0 < 1 + (x₀ - n) ^ 2 := by positivity
  rw [mul_one_div, div_le_div_iff₀ h2 h1]
  nlinarith


lemma summable_inv_one_add_sq_shift (x : ℝ) : Summable fun n : ℤ => 1 / (1 + (x - n) ^ 2) := by
  refine ((summable_shift_inv_sq' x).div_const 5).congr fun n => ?_
  field_simp

/-- `Σ_{k ∈ ℤ} (1 + k²)⁻¹`. -/
def latticeSum : ℝ := ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)

lemma latticeSum_nonneg : 0 ≤ latticeSum := tsum_nonneg fun k => by positivity

lemma one_add_sq_le_three_mul {u v : ℝ} (h : |u - v| ≤ 1) : 1 + v ^ 2 ≤ 3 * (1 + u ^ 2) := by
  have h2 : (u - v) ^ 2 ≤ 1 := by nlinarith [sq_abs (u - v), abs_nonneg (u - v)]
  nlinarith [sq_nonneg (u + (u - v))]

/-- The lattice sum is bounded uniformly in the shift. -/
lemma tsum_inv_one_add_sq_shift_le (x : ℝ) :
    ∑' n : ℤ, 1 / (1 + (x - n) ^ 2) ≤ 3 * latticeSum := by
  set m : ℤ := ⌊x⌋
  have hm : |x - m| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [Int.floor_le x, Int.sub_one_lt_floor x]
  have hg : Summable fun n : ℤ => 3 * (1 / (1 + ((m : ℝ) - n) ^ 2)) :=
    (summable_inv_one_add_sq_shift m).mul_left 3
  have hle : ∀ n : ℤ, 1 / (1 + (x - n) ^ 2) ≤ 3 * (1 / (1 + ((m : ℝ) - n) ^ 2)) := by
    intro n
    have h1 : |(x - n) - ((m : ℝ) - n)| ≤ 1 := by rw [show (x - n) - ((m : ℝ) - n) = x - m by ring]; exact hm
    have := one_add_sq_le_three_mul h1
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  calc ∑' n : ℤ, 1 / (1 + (x - n) ^ 2)
      ≤ ∑' n : ℤ, 3 * (1 / (1 + ((m : ℝ) - n) ^ 2)) :=
        (summable_inv_one_add_sq_shift x).tsum_le_tsum hle hg
    _ = 3 * latticeSum := by
        rw [tsum_mul_left, latticeSum]
        congr 1
        rw [← (Equiv.subLeft m).tsum_eq]
        refine tsum_congr fun n => ?_
        simp only [Equiv.subLeft_apply, Int.cast_sub, sub_sub_cancel]

/-! ### Majorants of the shape `A e^{2π|Im ζ|}/(1 + (Re ζ)²)` -/

/-- The kernel's majorant. -/
theorem norm_sincSq_le_majorant (ζ : ℂ) :
    ‖sincSq ζ‖ ≤ 2 * Real.exp (2 * π * |ζ.im|) / (1 + ζ.re ^ 2) := by
  have hE := Real.exp_pos (2 * π * |ζ.im|)
  by_cases hx : |ζ.re| ≤ 1
  · have h1 : ζ.re ^ 2 ≤ 1 := by nlinarith [sq_abs ζ.re, abs_nonneg ζ.re]
    refine (norm_sincSq_le ζ).trans ?_
    rw [le_div_iff₀ (by positivity)]
    generalize Real.exp (2 * π * |ζ.im|) = E at hE ⊢
    nlinarith
  · push Not at hx
    have hne : ζ ≠ 0 := by
      intro h; rw [h, zero_re, abs_zero] at hx; linarith
    have h1 : ζ.re ^ 2 ≤ ‖ζ‖ ^ 2 := by nlinarith [sq_abs ζ.re, abs_re_le_norm ζ, abs_nonneg ζ.re]
    have hx2 : 1 ≤ ζ.re ^ 2 := by nlinarith [sq_abs ζ.re]
    have hpi : 1 ≤ π ^ 2 := by nlinarith [Real.two_le_pi]
    refine (norm_sincSq_le_div hne).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    generalize Real.exp (2 * π * |ζ.im|) = E at hE ⊢
    have h3 : 1 + ζ.re ^ 2 ≤ 2 * (π ^ 2 * ‖ζ‖ ^ 2) := by nlinarith
    calc E * (1 + ζ.re ^ 2) ≤ E * (2 * (π ^ 2 * ‖ζ‖ ^ 2)) := by gcongr
      _ = 2 * E * (π ^ 2 * ‖ζ‖ ^ 2) := by ring

lemma nonneg_of_majorant {k : ℂ → ℂ} {A : ℝ}
    (hA : ∀ ζ, ‖k ζ‖ ≤ A * Real.exp (2 * π * |ζ.im|) / (1 + ζ.re ^ 2)) : 0 ≤ A := by
  have h := (norm_nonneg _).trans (hA 0)
  simp only [zero_im, abs_zero, mul_zero, Real.exp_zero, mul_one, zero_re] at h
  norm_num at h
  exact h

/-- Moving the base point by at most one costs a factor `3 e^{2π}`. -/
lemma majorant_le_of_norm_sub_le {A : ℝ} (hA : 0 ≤ A) {w v : ℂ} (h : ‖w - v‖ ≤ 1) :
    A * Real.exp (2 * π * |w.im|) / (1 + w.re ^ 2) ≤
      (3 * Real.exp (2 * π) * A) * Real.exp (2 * π * |v.im|) / (1 + v.re ^ 2) := by
  have hre : |w.re - v.re| ≤ 1 := by
    have := abs_re_le_norm (w - v); rw [sub_re] at this; linarith
  have him : |w.im| ≤ |v.im| + 1 := by
    have := abs_im_le_norm (w - v); rw [sub_im] at this
    have := abs_sub_abs_le_abs_sub w.im v.im; linarith
  have hexp : Real.exp (2 * π * |w.im|) ≤ Real.exp (2 * π) * Real.exp (2 * π * |v.im|) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hden := one_add_sq_le_three_mul hre
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hEw := Real.exp_pos (2 * π * |w.im|)
  have hE0 := Real.exp_pos (2 * π)
  have hEv := Real.exp_pos (2 * π * |v.im|)
  generalize Real.exp (2 * π * |w.im|) = Ew at hexp hEw ⊢
  generalize Real.exp (2 * π) = E0 at hexp hE0 ⊢
  generalize Real.exp (2 * π * |v.im|) = Ev at hexp hEv ⊢
  calc A * Ew * (1 + v.re ^ 2) ≤ A * (E0 * Ev) * (3 * (1 + w.re ^ 2)) := by gcongr
    _ = 3 * E0 * A * Ev * (1 + w.re ^ 2) := by ring

/-- Cauchy estimates on circles of radius one transfer a majorant to the derivative. -/
theorem norm_deriv_le_majorant {k : ℂ → ℂ} (hk : Differentiable ℂ k) {A : ℝ}
    (hA : ∀ ζ, ‖k ζ‖ ≤ A * Real.exp (2 * π * |ζ.im|) / (1 + ζ.re ^ 2)) (ζ : ℂ) :
    ‖deriv k ζ‖ ≤ (3 * Real.exp (2 * π) * A) * Real.exp (2 * π * |ζ.im|) / (1 + ζ.re ^ 2) := by
  have hA0 := nonneg_of_majorant hA
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := ζ) (R := 1) (f := k) one_pos
    hk.diffContOnCl (fun w hw => (hA w).trans
      (majorant_le_of_norm_sub_le hA0 (mem_sphere_iff_norm.mp hw).le))
  simpa using this

/-! ### Series of shifted kernels -/

section Series

variable {k : ℂ → ℂ} {A : ℝ} {c : ℤ → ℂ} {M : ℝ}

lemma norm_shift_term_le (hA : ∀ ζ, ‖k ζ‖ ≤ A * Real.exp (2 * π * |ζ.im|) / (1 + ζ.re ^ 2))
    (hc : ∀ n, ‖c n‖ ≤ M) (z : ℂ) (n : ℤ) :
    ‖c n * k (z - n)‖ ≤ M * A * Real.exp (2 * π * |z.im|) * (1 / (1 + (z.re - n) ^ 2)) := by
  have hA0 := nonneg_of_majorant hA
  rw [norm_mul]
  have h := hA (z - n)
  simp only [sub_im, intCast_im, sub_zero, sub_re, intCast_re] at h
  calc ‖c n‖ * ‖k (z - n)‖ ≤ M * (A * Real.exp (2 * π * |z.im|) / (1 + (z.re - n) ^ 2)) :=
        mul_le_mul (hc n) h (norm_nonneg _) ((norm_nonneg _).trans (hc n))
    _ = M * A * Real.exp (2 * π * |z.im|) * (1 / (1 + (z.re - n) ^ 2)) := by ring

lemma summable_shift (hA : ∀ ζ, ‖k ζ‖ ≤ A * Real.exp (2 * π * |ζ.im|) / (1 + ζ.re ^ 2))
    (hc : ∀ n, ‖c n‖ ≤ M) (z : ℂ) : Summable fun n : ℤ => c n * k (z - n) :=
  Summable.of_norm_bounded ((summable_inv_one_add_sq_shift z.re).mul_left _)
    (norm_shift_term_le hA hc z)

/-- The series is bounded by `M · A · e^{2π|Im z|} · 3 Σ_k (1+k²)⁻¹`, uniformly in `Re z`. -/
theorem norm_tsum_shift_le (hA : ∀ ζ, ‖k ζ‖ ≤ A * Real.exp (2 * π * |ζ.im|) / (1 + ζ.re ^ 2))
    (hc : ∀ n, ‖c n‖ ≤ M) (z : ℂ) :
    ‖∑' n : ℤ, c n * k (z - n)‖ ≤ M * A * Real.exp (2 * π * |z.im|) * (3 * latticeSum) := by
  have hA0 := nonneg_of_majorant hA
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hc 0)
  have hmaj := (summable_inv_one_add_sq_shift z.re).mul_left (M * A * Real.exp (2 * π * |z.im|))
  calc ‖∑' n : ℤ, c n * k (z - n)‖
      ≤ ∑' n : ℤ, M * A * Real.exp (2 * π * |z.im|) * (1 / (1 + (z.re - n) ^ 2)) :=
        tsum_of_norm_bounded hmaj.hasSum (norm_shift_term_le hA hc z)
    _ = M * A * Real.exp (2 * π * |z.im|) * ∑' n : ℤ, 1 / (1 + (z.re - n) ^ 2) := tsum_mul_left
    _ ≤ M * A * Real.exp (2 * π * |z.im|) * (3 * latticeSum) := by
        gcongr
        exact tsum_inv_one_add_sq_shift_le z.re

lemma norm_shift_term_le_ball (hA : ∀ ζ, ‖k ζ‖ ≤ A * Real.exp (2 * π * |ζ.im|) / (1 + ζ.re ^ 2))
    (hc : ∀ n, ‖c n‖ ≤ M) {z₀ w : ℂ} (hw : w ∈ ball z₀ 1) (n : ℤ) :
    ‖c n * k (w - n)‖ ≤
      M * ((3 * Real.exp (2 * π) * A) * Real.exp (2 * π * |z₀.im|) * (1 / (1 + (z₀.re - n) ^ 2))) := by
  have hA0 := nonneg_of_majorant hA
  rw [norm_mul]
  have hd : ‖(w - n) - (z₀ - n)‖ ≤ 1 := by
    rw [sub_sub_sub_cancel_right]; exact (mem_ball_iff_norm.mp hw).le
  have h := (hA (w - n)).trans (majorant_le_of_norm_sub_le hA0 hd)
  simp only [sub_im, intCast_im, sub_zero, sub_re, intCast_re] at h
  refine mul_le_mul (hc n) (h.trans_eq ?_) (norm_nonneg _) ((norm_nonneg _).trans (hc n))
  ring

/-- A series of shifted entire kernels with a majorant and bounded coefficients is entire. -/
theorem differentiable_tsum_shift (hk : Differentiable ℂ k)
    (hA : ∀ ζ, ‖k ζ‖ ≤ A * Real.exp (2 * π * |ζ.im|) / (1 + ζ.re ^ 2))
    (hc : ∀ n, ‖c n‖ ≤ M) : Differentiable ℂ fun z : ℂ => ∑' n : ℤ, c n * k (z - n) := by
  intro z₀
  have hF : ∀ n : ℤ, DifferentiableOn ℂ (fun y : ℂ => c n * k (y - n)) (ball z₀ 1) :=
    fun n y _ => (((hk (y - n)).comp y (differentiableAt_id.sub_const (n : ℂ))).const_mul
      (c n)).differentiableWithinAt
  refine (Complex.differentiableOn_tsum_of_summable_norm
    (F := fun (n : ℤ) (y : ℂ) => c n * k (y - n))
    ((summable_inv_one_add_sq_shift z₀.re).mul_left _ |>.mul_left M) hF
    isOpen_ball (fun n w hw => norm_shift_term_le_ball hA hc hw n)).differentiableAt
    (ball_mem_nhds z₀ one_pos)

/-- Termwise differentiation of the series. -/
theorem hasSum_deriv_tsum_shift (hk : Differentiable ℂ k)
    (hA : ∀ ζ, ‖k ζ‖ ≤ A * Real.exp (2 * π * |ζ.im|) / (1 + ζ.re ^ 2))
    (hc : ∀ n, ‖c n‖ ≤ M) (z : ℂ) :
    HasSum (fun n : ℤ => c n * deriv k (z - n))
      (deriv (fun z : ℂ => ∑' n : ℤ, c n * k (z - n)) z) := by
  have hF : ∀ n : ℤ, DifferentiableOn ℂ (fun y : ℂ => c n * k (y - n)) (ball z 1) :=
    fun n y _ => (((hk (y - n)).comp y (differentiableAt_id.sub_const (n : ℂ))).const_mul
      (c n)).differentiableWithinAt
  have h := Complex.hasSum_deriv_of_summable_norm (F := fun (n : ℤ) (y : ℂ) => c n * k (y - n))
    ((summable_inv_one_add_sq_shift z.re).mul_left _ |>.mul_left M) hF
    isOpen_ball (fun n w hw => norm_shift_term_le_ball hA hc hw n) (mem_ball_self one_pos)
  refine h.congr_fun fun n => ?_
  have hd : DifferentiableAt ℂ (fun y : ℂ => k (y - n)) z :=
    (hk (z - n)).comp z (differentiableAt_id.sub_const (n : ℂ))
  rw [deriv_const_mul _ hd, deriv_comp_sub_const]

theorem deriv_tsum_shift (hk : Differentiable ℂ k)
    (hA : ∀ ζ, ‖k ζ‖ ≤ A * Real.exp (2 * π * |ζ.im|) / (1 + ζ.re ^ 2))
    (hc : ∀ n, ‖c n‖ ≤ M) :
    deriv (fun z : ℂ => ∑' n : ℤ, c n * k (z - n)) =
      fun z : ℂ => ∑' n : ℤ, c n * deriv k (z - n) :=
  funext fun z => (hasSum_deriv_tsum_shift hk hA hc z).tsum_eq.symm

end Series

end FroehlichSpencer.BKT.Rotator.BesselInterp
