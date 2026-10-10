/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# Cancellation over the finite clock group

The nontrivial character of a finite cyclic clock has zero sum. Its real part
is the corresponding cancellation for the cosine observable.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Clock.HighTemp

/-- Sum of all `N` equally spaced clock roots of unity. -/
theorem clockRootSum_zero (N : ℕ) (hN : 2 ≤ N) :
    ∑ k ∈ Finset.range N,
      Complex.exp ((k : ℂ) * ((2 * Real.pi * Complex.I) / (N : ℂ))) = 0 := by
  have hN0 : N ≠ 0 := by omega
  let z : ℂ := Complex.exp ((2 * Real.pi * Complex.I) / (N : ℂ))
  have hzN : z ^ N = 1 := by
    dsimp [z]
    rw [← Complex.exp_nat_mul]
    have harg : (N : ℂ) * ((2 * Real.pi * Complex.I) / (N : ℂ)) =
        2 * Real.pi * Complex.I := by field_simp
    rw [harg, Complex.exp_two_pi_mul_I]
  have hzne : z ≠ 1 := by
    intro hz
    have hdvd : N ∣ 1 := by
      apply (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := 1) hN0).mp
      simpa [z, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hz
    have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hdvd
    omega
  have hroot : ∑ k ∈ Finset.range N, z ^ k = 0 := by
    have hg := geom_sum_mul z N
    rw [hzN, sub_self] at hg
    rcases mul_eq_zero.mp hg with hs | hs
    · exact hs
    · exact (hzne (sub_eq_zero.mp hs)).elim
  calc
    ∑ k ∈ Finset.range N,
        Complex.exp ((k : ℂ) * ((2 * Real.pi * Complex.I) / (N : ℂ)))
      = ∑ k ∈ Finset.range N, z ^ k := by
          apply Finset.sum_congr rfl
          intro k hk
          dsimp [z]
          rw [Complex.exp_nat_mul]
    _ = 0 := hroot

/-- The average of a cosine over all clock rotations is zero. -/
theorem clockRotation_cos_sum_zero (N : ℕ) (hN : 2 ≤ N) (x : ℝ) :
    ∑ k ∈ Finset.range N,
      Real.cos (x + (k : ℝ) * (2 * Real.pi / N)) = 0 := by
  have hN0 : N ≠ 0 := by omega
  have hN0c : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  let z : ℂ := Complex.exp ((2 * Real.pi * Complex.I) / (N : ℂ))
  have hzsum : ∑ k ∈ Finset.range N, z ^ k = 0 := by
    calc
      ∑ k ∈ Finset.range N, z ^ k =
          ∑ k ∈ Finset.range N,
            Complex.exp ((k : ℂ) * ((2 * Real.pi * Complex.I) / (N : ℂ))) := by
              apply Finset.sum_congr rfl
              intro k hk
              dsimp [z]
              rw [Complex.exp_nat_mul]
      _ = 0 := clockRootSum_zero N hN
  have hexpsum :
      ∑ k ∈ Finset.range N,
        Complex.exp (((x + (k : ℝ) * (2 * Real.pi / N) : ℝ) : ℂ) * Complex.I) = 0 := by
    calc
      ∑ k ∈ Finset.range N,
          Complex.exp (((x + (k : ℝ) * (2 * Real.pi / N) : ℝ) : ℂ) * Complex.I)
        = ∑ k ∈ Finset.range N, Complex.exp (x * Complex.I) * z ^ k := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [show (((x + (k : ℝ) * (2 * Real.pi / N) : ℝ) : ℂ) * Complex.I) =
                x * Complex.I + (k : ℂ) * ((2 * Real.pi * Complex.I) / (N : ℂ)) by
                  push_cast
                  field_simp [hN0c]]
            rw [Complex.exp_add, Complex.exp_nat_mul]
      _ = Complex.exp (x * Complex.I) * ∑ k ∈ Finset.range N, z ^ k := by
            rw [Finset.mul_sum]
      _ = 0 := by rw [hzsum, mul_zero]
  calc
    ∑ k ∈ Finset.range N,
        Real.cos (x + (k : ℝ) * (2 * Real.pi / N))
      = Complex.re (∑ k ∈ Finset.range N,
          Complex.exp (((x + (k : ℝ) * (2 * Real.pi / N) : ℝ) : ℂ) * Complex.I)) := by
            rw [Complex.re_sum]
            simp only [Complex.exp_ofReal_mul_I_re]
    _ = 0 := by rw [hexpsum]; simp

/-- The Fin-indexed form of `clockRotation_cos_sum_zero`. -/
theorem fin_clockRotation_cos_sum_zero (N : ℕ) (hN : 2 ≤ N) (x : ℝ) :
    ∑ k : Fin N, Real.cos (x + (k.val : ℝ) * (2 * Real.pi / N)) = 0 := by
  calc
    ∑ k : Fin N, Real.cos (x + (k.val : ℝ) * (2 * Real.pi / N)) =
        ∑ k ∈ Finset.range N, Real.cos (x + (k : ℝ) * (2 * Real.pi / N)) := by
          exact Fin.sum_univ_eq_sum_range
            (fun k : ℕ => Real.cos (x + (k : ℝ) * (2 * Real.pi / N))) N
    _ = 0 := clockRotation_cos_sum_zero N hN x

end FroehlichSpencer.BKT.Clock.HighTemp

end
