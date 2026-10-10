/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.BesselInterp.Coeff
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Factorial bound and nonnegativity of the Bessel Fourier coefficients

From the exponential series, `I_β(n) = (2π)⁻¹ Σ_k β^k/k! ∫₀^{2π} cos^k θ cos (nθ) dθ`, where the
moments vanish for `k < |n|` and are at most `2π`. Hence `|I_β(n)| ≤ |β|^{|n|} e^{|β|} / |n|!` and
`I_β(n) ≥ 0` for `β ≥ 0`.
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.BesselInterp

open scoped Real

lemma besselCoeffRe_natAbs (β : ℝ) (n : ℤ) : besselCoeffRe β n = besselCoeffRe β (n.natAbs : ℤ) := by
  rcases Int.natAbs_eq n with h | h
  · conv_lhs => rw [h]
  · conv_lhs => rw [h, besselCoeffRe_neg]

/-- For `β ≥ 0` the coefficients are nonnegative. -/
theorem besselCoeffRe_nonneg {β : ℝ} (hβ : 0 ≤ β) (n : ℤ) : 0 ≤ besselCoeffRe β n := by
  unfold besselCoeffRe
  refine mul_nonneg (by positivity) ?_
  exact (hasSum_besselIntegral β n).nonneg fun k =>
    mul_nonneg (by positivity) (cosMoment_nonneg k n)

lemma cosMoment_eq_zero_of_lt (k : ℕ) : ∀ m : ℤ, (k : ℤ) < |m| → cosMoment k m = 0 := by
  induction k with
  | zero =>
    intro m hm
    rw [cosMoment_zero, ite_eq_right]
    intro h; rw [h, abs_zero] at hm; exact absurd hm (lt_irrefl _)
  | succ k ih =>
    intro m hm
    rw [cosMoment_succ, ih (m + 1), ih (m - 1)]
    · norm_num
    · rw [lt_abs] at hm ⊢; push_cast at hm; omega
    · rw [lt_abs] at hm ⊢; push_cast at hm; omega

lemma cosMoment_le (k : ℕ) : ∀ m : ℤ, cosMoment k m ≤ 2 * π := by
  induction k with
  | zero => intro m; rw [cosMoment_zero]; split_ifs <;> linarith [Real.pi_pos]
  | succ k ih => intro m; rw [cosMoment_succ]; linarith [ih (m + 1), ih (m - 1)]

lemma pow_div_factorial_add_le (x : ℝ) (hx : 0 ≤ x) (N j : ℕ) :
    x ^ (j + N) / (Nat.factorial (j + N)) ≤
      x ^ N / (Nat.factorial N) * (x ^ j / (Nat.factorial j)) := by
  have hfac : (Nat.factorial N : ℝ) * (Nat.factorial j) ≤ Nat.factorial (j + N) := by
    have := Nat.factorial_mul_factorial_dvd_factorial_add N j
    rw [add_comm j N]
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) this
  rw [div_mul_div_comm, ← pow_add, add_comm N j]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hfac

/-- The explicit factorial bound `|I_β(n)| ≤ |β|^{|n|} e^{|β|} / |n|!`. -/
theorem abs_besselCoeffRe_le (β : ℝ) (n : ℤ) :
    |besselCoeffRe β n| ≤
      |β| ^ n.natAbs / (Nat.factorial n.natAbs) * Real.exp |β| := by
  rw [besselCoeffRe_natAbs]
  set N := n.natAbs
  unfold besselCoeffRe
  have hs := hasSum_besselIntegral β (N : ℤ)
  have habs : Summable fun k : ℕ => |β| ^ k / (Nat.factorial k) * cosMoment k N :=
    ((NormedSpace.expSeries_div_summable (𝔸 := ℝ) |β|).mul_right (2 * π)).of_nonneg_of_le
      (fun k => mul_nonneg (by positivity) (cosMoment_nonneg k _))
      (fun k => mul_le_mul_of_nonneg_left (cosMoment_le k _) (by positivity))
  have hterm : ∀ k : ℕ, ‖β ^ k / (Nat.factorial k) * cosMoment k N‖ =
      |β| ^ k / (Nat.factorial k) * cosMoment k N := fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast,
      abs_of_nonneg (cosMoment_nonneg k _)]
  have hle : |∑' k : ℕ, β ^ k / (Nat.factorial k) * cosMoment k N| ≤
      ∑' k : ℕ, |β| ^ k / (Nat.factorial k) * cosMoment k N := by
    rw [← Real.norm_eq_abs, ← tsum_congr hterm]
    exact norm_tsum_le_tsum_norm (habs.congr fun k => (hterm k).symm)
  have hshift : ∑' k : ℕ, |β| ^ k / (Nat.factorial k) * cosMoment k N =
      ∑' j : ℕ, |β| ^ (j + N) / (Nat.factorial (j + N)) * cosMoment (j + N) N := by
    rw [← habs.sum_add_tsum_nat_add N]
    have : ∑ i ∈ Finset.range N, |β| ^ i / (Nat.factorial i) * cosMoment i N = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [cosMoment_eq_zero_of_lt i N (by
        rw [Finset.mem_range] at hi
        rw [Nat.abs_cast]; exact_mod_cast hi), mul_zero]
    rw [this, zero_add]
  have hbound : ∑' j : ℕ, |β| ^ (j + N) / (Nat.factorial (j + N)) * cosMoment (j + N) N ≤
      ∑' j : ℕ, |β| ^ N / (Nat.factorial N) * (|β| ^ j / (Nat.factorial j)) * (2 * π) := by
    refine Summable.tsum_le_tsum (fun j => ?_) ((summable_nat_add_iff N).mpr habs)
      (((NormedSpace.expSeries_div_summable (𝔸 := ℝ) |β|).mul_left _).mul_right _)
    exact mul_le_mul (pow_div_factorial_add_le |β| (abs_nonneg β) N j) (cosMoment_le _ _)
      (cosMoment_nonneg _ _) (by positivity)
  have hexp : ∑' j : ℕ, |β| ^ N / (Nat.factorial N) * (|β| ^ j / (Nat.factorial j)) * (2 * π) =
      |β| ^ N / (Nat.factorial N) * Real.exp |β| * (2 * π) := by
    rw [tsum_mul_right, tsum_mul_left, Real.exp_eq_exp_ℝ,
      (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) |β|).tsum_eq]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹), ← hs.tsum_eq]
  calc (2 * π)⁻¹ * |∑' k : ℕ, β ^ k / (Nat.factorial k) * cosMoment k N|
      ≤ (2 * π)⁻¹ * (|β| ^ N / (Nat.factorial N) * Real.exp |β| * (2 * π)) := by
        gcongr
        exact hle.trans (hshift ▸ hbound.trans hexp.le)
    _ = |β| ^ N / (Nat.factorial N) * Real.exp |β| := by
        field_simp

end FroehlichSpencer.BKT.Rotator.BesselInterp
