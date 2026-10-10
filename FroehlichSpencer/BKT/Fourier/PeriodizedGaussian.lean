/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The periodized Gaussian edge weight

The Villain weight is the periodization of a Gaussian with period `2π`. Its Fourier expansion is
the one-edge identity used in Kharash–Peled, arXiv:1711.04720v1, §6.1, p. 33.
-/

@[expose] public section

open Real
open Filter
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT

/-- The one-edge Villain weight, KP §1.4, p. 4. -/
def villainWeight (β x : ℝ) : ℝ :=
  ∑' m : ℤ, Real.exp (-(β / 2) * (x + 2 * π * m) ^ 2)

namespace VillainWeight

variable {β : ℝ}

private theorem summable_shift_nat (hβ : 0 < β) (x : ℝ) :
    Summable (fun n : ℕ => Real.exp (-(β / 2) * (x + 2 * π * (n : ℝ)) ^ 2)) := by
  let a : ℝ := -(β / 2) * (2 * π) ^ 2
  let b : ℝ := -(β / 2) * (2 * x * (2 * π))
  let c : ℝ := -(β / 2) * x ^ 2
  have ha : a < 0 := by
    have hβ2 : 0 < β / 2 := by positivity
    have hπ : 0 < (2 * π) ^ 2 := sq_pos_of_pos (by positivity)
    calc
      a = -((β / 2) * (2 * π) ^ 2) := by simp [a, neg_mul]
      _ < 0 := neg_lt_zero.mpr (mul_pos hβ2 hπ)
  have hquad := rexp_neg_quadratic_isLittleO_rpow_atTop ha b (-2)
  have hcast := hquad.isBigO.comp_tendsto
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hbound :
      (fun n : ℕ => Real.exp (-(β / 2) * (x + 2 * π * (n : ℝ)) ^ 2)) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) := by
    convert hcast.const_mul_left (Real.exp c) using 1 <;> ext n
    · change Real.exp (-(β / 2) * (x + 2 * π * (n : ℝ)) ^ 2) =
        Real.exp c * Real.exp (a * (n : ℝ) ^ 2 + b * (n : ℝ))
      rw [← Real.exp_add]
      congr 1
      dsimp [a, b, c]
      ring
    · rfl
  exact summable_of_isBigO_nat
    (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)) hbound

private theorem summable_shifted_gaussian (hβ : 0 < β) (x : ℝ) :
    Summable (fun m : ℤ => Real.exp (-(β / 2) * (x + 2 * π * m) ^ 2)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa using summable_shift_nat hβ x
  · convert summable_shift_nat hβ (-x) using 1
    ext n
    congr 2
    push_cast
    ring

/-- The defining Gaussian series of the Villain weight is summable. -/
theorem villainWeight_summable (hβ : 0 < β) (x : ℝ) :
    Summable (fun m : ℤ => Real.exp (-(β / 2) * (x + 2 * π * m) ^ 2)) :=
  summable_shifted_gaussian hβ x

@[simp] theorem villainWeight_apply (x : ℝ) :
    villainWeight β x = ∑' m : ℤ, Real.exp (-(β / 2) * (x + 2 * π * m) ^ 2) := rfl

theorem villainWeight_pos (hβ : 0 < β) (x : ℝ) : 0 < villainWeight β x := by
  rw [villainWeight]
  exact (summable_shifted_gaussian hβ x).tsum_pos (fun _ => by positivity) 0 (by positivity)

private theorem summable_gaussian_coeff (hβ : 0 < β) :
    Summable (fun q : ℤ => Real.exp (-((q : ℝ) ^ 2) / (2 * β))) := by
  have hc : -(1 / (2 * β)) < 0 := neg_lt_zero.mpr (by positivity)
  have hn : ∀ n : ℕ, (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    intro n
    exact_mod_cast (show n ≤ n ^ 2 by simpa [pow_two] using Nat.le_mul_self n)
  have hnat : Summable (fun n : ℕ => Real.exp (-(1 / (2 * β)) * (n : ℝ) ^ 2)) :=
    Real.summable_exp_nat_mul_of_ge hc hn
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · convert hnat using 1
    ext n
    simp only [Int.cast_natCast]
    congr 1
    field_simp [ne_of_gt hβ]
  · convert hnat using 1
    ext n
    simp only [Int.cast_neg, Int.cast_natCast, neg_sq]
    congr 1
    field_simp [ne_of_gt hβ]

/-- The integer Fourier coefficients of the periodized Gaussian are summable. -/
theorem villainWeight_fourier_coeff_summable (hβ : 0 < β) :
    Summable (fun q : ℤ => Real.exp (-((q : ℝ) ^ 2) / (2 * β))) :=
  summable_gaussian_coeff hβ

/-- The complex Fourier series on the right side of the Poisson identity is summable. -/
theorem villainWeight_fourier_series_summable (hβ : 0 < β) (x : ℝ) :
    Summable (fun q : ℤ =>
      (Real.exp (-((q : ℝ) ^ 2) / (2 * β)) : ℂ) *
        Complex.exp (Complex.I * (q : ℂ) * (x : ℂ))) := by
  apply Summable.of_norm
  convert (villainWeight_fourier_coeff_summable hβ).norm using 1
  ext q
  rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_exp]
  simp [Complex.mul_re]

/-- Complex Fourier expansion of the periodized Gaussian, by the Gaussian Poisson formula.
This is the one-edge Villain identity used in KP §6.1, p. 33. -/
theorem villainWeight_fourier_complex (hβ : 0 < β) (x : ℝ) :
    (villainWeight β x : ℂ) =
      (1 / ((2 * π * β : ℝ) : ℂ) ^ (1 / 2 : ℂ)) *
        ∑' q : ℤ,
          (Real.exp (-((q : ℝ) ^ 2) / (2 * β)) : ℂ) *
            Complex.exp (Complex.I * (q : ℂ) * (x : ℂ)) := by
  let a : ℂ := ((2 * π * β : ℝ) : ℂ)
  let b : ℂ := (-(β * x) : ℝ)
  have ha : 0 < a.re := by
    simp [a]
    positivity
  have hcast :
      (villainWeight β x : ℂ) =
        ∑' m : ℤ, Complex.exp (-(β / 2 : ℝ) * (x + 2 * π * m) ^ 2) := by
    rw [villainWeight, Complex.ofReal_tsum]
    apply tsum_congr
    intro m
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
  calc
    (villainWeight β x : ℂ) =
        ∑' m : ℤ, Complex.exp (-(β / 2 : ℝ) * (x + 2 * π * m) ^ 2) := hcast
    _ = Complex.exp (-(β / 2 : ℝ) * x ^ 2) *
          ∑' m : ℤ, Complex.exp (-π * a * (m : ℂ) ^ 2 + 2 * π * b * m) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      rw [← Complex.exp_add]
      congr 1
      simp [a, b]
      ring_nf
    _ = Complex.exp (-(β / 2 : ℝ) * x ^ 2) *
          ((1 / a ^ (1 / 2 : ℂ)) *
            ∑' q : ℤ, Complex.exp (-π / a * ((q : ℂ) + Complex.I * b) ^ 2)) := by
      rw [Complex.tsum_exp_neg_quadratic ha b]
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          ∑' q : ℤ,
            (Real.exp (-((q : ℝ) ^ 2) / (2 * β)) : ℂ) *
              Complex.exp (Complex.I * (q : ℂ) * (x : ℂ)) := by
      calc
        _ = (1 / a ^ (1 / 2 : ℂ)) *
              (Complex.exp (-(β / 2 : ℝ) * x ^ 2) *
                ∑' q : ℤ, Complex.exp (-π / a * ((q : ℂ) + Complex.I * b) ^ 2)) := by ring
        _ = (1 / a ^ (1 / 2 : ℂ)) *
              ∑' q : ℤ,
                Complex.exp (-(β / 2 : ℝ) * x ^ 2) *
                  Complex.exp (-π / a * ((q : ℂ) + Complex.I * b) ^ 2) := by
          rw [← tsum_mul_left]
        _ = (1 / a ^ (1 / 2 : ℂ)) *
              ∑' q : ℤ,
                (Real.exp (-((q : ℝ) ^ 2) / (2 * β)) : ℂ) *
                  Complex.exp (Complex.I * (q : ℂ) * (x : ℂ)) := by
          apply congrArg (fun z : ℂ => (1 / a ^ (1 / 2 : ℂ)) * z)
          apply tsum_congr
          intro q
          rw [Complex.ofReal_exp]
          conv_lhs => rw [← Complex.exp_add]
          conv_rhs => rw [← Complex.exp_add]
          congr 1
          simp only [a, b, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
            Complex.ofReal_div]
          push_cast
          field_simp [Complex.ofReal_ne_zero.mpr hβ.ne',
            Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
          ring_nf
          simp only [Complex.I_sq]
          ring

private theorem complex_prefactor_eq_real {A : ℝ} (hA : 0 < A) :
    (1 / (A : ℂ) ^ (1 / 2 : ℂ)) = (↑(A ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hhalf, ← Complex.ofReal_cpow hA.le (1 / 2 : ℝ), one_div, ← Complex.ofReal_inv]
  apply congrArg Complex.ofReal
  rw [Real.rpow_neg hA.le]

/-- Complex exponential form with the real Poisson normalization made explicit, KP §6.1, p. 33.
-/
theorem villainWeight_fourier_complex_normalized (hβ : 0 < β) (x : ℝ) :
    (villainWeight β x : ℂ) =
      (((2 * π * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑' q : ℤ,
          (Real.exp (-((q : ℝ) ^ 2) / (2 * β)) : ℂ) *
            Complex.exp (Complex.I * (q : ℂ) * (x : ℂ)) := by
  let A : ℝ := 2 * π * β
  have hA : 0 < A := by positivity
  calc
    (villainWeight β x : ℂ) =
        (1 / (A : ℂ) ^ (1 / 2 : ℂ)) *
          ∑' q : ℤ,
            (Real.exp (-((q : ℝ) ^ 2) / (2 * β)) : ℂ) *
              Complex.exp (Complex.I * (q : ℂ) * (x : ℂ)) := by
      simpa [A] using villainWeight_fourier_complex hβ x
    _ = (((A ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
          ∑' q : ℤ,
            (Real.exp (-((q : ℝ) ^ 2) / (2 * β)) : ℂ) *
              Complex.exp (Complex.I * (q : ℂ) * (x : ℂ)) := by
      rw [complex_prefactor_eq_real hA]
    _ = (((2 * π * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑' q : ℤ,
            (Real.exp (-((q : ℝ) ^ 2) / (2 * β)) : ℂ) *
              Complex.exp (Complex.I * (q : ℂ) * (x : ℂ)) := by rfl

/-- Real cosine form of the Villain Fourier expansion, KP §6.1, p. 33. -/
theorem villainWeight_fourier_real (hβ : 0 < β) (x : ℝ) :
    villainWeight β x =
      (2 * π * β) ^ (-(1 / 2 : ℝ)) *
        ∑' q : ℤ,
          Real.exp (-((q : ℝ) ^ 2) / (2 * β)) * Real.cos ((q : ℝ) * x) := by
  let A : ℝ := 2 * π * β
  have hA : 0 < A := by positivity
  have hc := complex_prefactor_eq_real hA
  have hseries := villainWeight_fourier_series_summable hβ x
  have hterm (q : ℤ) :
      ((Real.exp (-((q : ℝ) ^ 2) / (2 * β)) : ℂ) *
        Complex.exp (Complex.I * (q : ℂ) * (x : ℂ))).re =
          Real.exp (-((q : ℝ) ^ 2) / (2 * β)) * Real.cos ((q : ℝ) * x) := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have hphase :
        Complex.I * (q : ℂ) * (x : ℂ) = (((q : ℝ) * x : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hphase, Complex.exp_ofReal_mul_I]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  calc
    villainWeight β x = (villainWeight β x : ℂ).re := by simp
    _ = ((1 / ((2 * π * β : ℝ) : ℂ) ^ (1 / 2 : ℂ)) *
          ∑' q : ℤ,
            (Real.exp (-((q : ℝ) ^ 2) / (2 * β)) : ℂ) *
              Complex.exp (Complex.I * (q : ℂ) * (x : ℂ))).re := by
      rw [villainWeight_fourier_complex hβ x]
    _ = A ^ (-(1 / 2 : ℝ)) *
          (∑' q : ℤ,
            (Real.exp (-((q : ℝ) ^ 2) / (2 * β)) : ℂ) *
              Complex.exp (Complex.I * (q : ℂ) * (x : ℂ))).re := by
      rw [hc]
      rw [Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    _ = A ^ (-(1 / 2 : ℝ)) *
          ∑' q : ℤ,
            Real.exp (-((q : ℝ) ^ 2) / (2 * β)) * Real.cos ((q : ℝ) * x) := by
      rw [Complex.re_tsum hseries]
      congr 1
      apply tsum_congr
      exact hterm


/-- The Villain weight is periodic with period `2π`, KP §1.4, p. 4. -/
theorem villainWeight_add_two_pi (β x : ℝ) :
    villainWeight β (x + 2 * π) = villainWeight β x := by
  rw [villainWeight, villainWeight]
  calc
    (∑' m : ℤ, Real.exp (-(β / 2) * (x + 2 * π + 2 * π * m) ^ 2)) =
        ∑' m : ℤ, Real.exp (-(β / 2) * (x + 2 * π * (m + 1)) ^ 2) := by
      apply tsum_congr
      intro m
      congr 1
      congr 2
      ring_nf
    _ = ∑' m : ℤ, Real.exp (-(β / 2) * (x + 2 * π * m) ^ 2) := by
      simpa only [Equiv.coe_addRight, Int.cast_add, Int.cast_one] using
        (Equiv.tsum_eq (Equiv.addRight (1 : ℤ))
          (fun m : ℤ => Real.exp (-(β / 2) * (x + 2 * π * m) ^ 2)))

/-- The Villain weight is even, KP §1.4, p. 4. -/
theorem villainWeight_neg (β x : ℝ) : villainWeight β (-x) = villainWeight β x := by
  rw [villainWeight, villainWeight]
  calc
    (∑' m : ℤ, Real.exp (-(β / 2) * (-x + 2 * π * m) ^ 2)) =
        ∑' m : ℤ, Real.exp (-(β / 2) * (x + 2 * π * (-m)) ^ 2) := by
      apply tsum_congr
      intro m
      rw [show (-x + 2 * π * m) ^ 2 = (x + 2 * π * (-m)) ^ 2 by
        ring_nf]
    _ = ∑' m : ℤ, Real.exp (-(β / 2) * (x + 2 * π * m) ^ 2) := by
      simpa only [Equiv.neg_apply, Int.cast_neg] using
        (Equiv.tsum_eq (Equiv.neg ℤ)
          (fun m : ℤ => Real.exp (-(β / 2) * (x + 2 * π * m) ^ 2)))

/-- Reindexed complex Fourier expansion with a negative phase. This convention makes the current
constraint from `exp (I * θ j)` have positive divergence at `j`, as in KP §6.1, p. 33. -/
theorem villainWeight_fourier_complex_normalized_neg (hβ : 0 < β) (x : ℝ) :
    (villainWeight β x : ℂ) =
      (((2 * π * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑' q : ℤ,
          (Real.exp (-((q : ℝ) ^ 2) / (2 * β)) : ℂ) *
            Complex.exp (-Complex.I * (q : ℂ) * (x : ℂ)) := by
  have hphase (q : ℤ) :
      Complex.I * (q : ℂ) * ((-x : ℝ) : ℂ) =
        -Complex.I * (q : ℂ) * (x : ℂ) := by
    rw [Complex.ofReal_neg]
    ring
  calc
    (villainWeight β x : ℂ) = (villainWeight β (-x) : ℂ) := by
      rw [villainWeight_neg]
    _ = (((2 * π * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑' q : ℤ,
            (Real.exp (-((q : ℝ) ^ 2) / (2 * β)) : ℂ) *
              Complex.exp (Complex.I * (q : ℂ) * (-x : ℝ)) :=
      villainWeight_fourier_complex_normalized hβ (-x)
    _ = (((2 * π * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑' q : ℤ,
            (Real.exp (-((q : ℝ) ^ 2) / (2 * β)) : ℂ) *
              Complex.exp (-Complex.I * (q : ℂ) * (x : ℂ)) := by
      congr 1
      apply tsum_congr
      intro q
      rw [hphase]

end VillainWeight

end FroehlichSpencer.BKT

end
