/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.ZN.RenormIdentity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# the Jensen step (3.42)–(3.49)

The source expands `1 + z F(ρ; dθ + ε)` to second order in `ε`, notes that the first-order term is
odd in `θ`, and applies Jensen's inequality to the even positive measure
`∏ [1 + z F(ρ; dθ)] dμ_β` (FS82 (3.42)–(3.49)).

Here the same bound is obtained from a pointwise
two-point inequality and the symmetry `θ ↦ −θ`:

* `two_point_lower_bound`: if `u_± = u₀ e^{Δ_±}` with `|u| ≤ 1`, `|Δ_±| ≤ k₁`, `|Δ_+ + Δ_-| ≤ k₂` and
  `0 ≤ z ≤ 1/2`, then `(1 + z Re u_+)(1 + z Re u_-) ≥ (1 + z Re u₀)² e^{−6z(2k₂ + 12k₁²)}`.
* `renormU_eq_mul_exp`: `U(θ; ε, δ) = U(θ; 0, 0) e^{Δ(ε, δ)}`, with `shiftDelta` and its bounds
  `shiftK1` (first order) and `shiftK2` (second order, for `Δ(ε,δ) + Δ(−ε,−δ)`).
* `integral_renorm_jensen`: FS82 (3.49),
  `∫ ∏ (1 + z_i F_i^{ε,δ}) W_ε ≥ e^{−Σ 3 z_i (2k₂ + 12k₁²) − (β/2) Σ (2πε_p)²} ∫ ∏ (1 + z_i F_i^{0,0}) W_0`.
-/

open MeasureTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.ZN.Torus

noncomputable section


/-! ### The two-point inequality -/

/-- `(1 − z)² ≥ (1 + z)² e^{−6z}` for `0 ≤ z ≤ 1/2`. -/
theorem one_sub_sq_ge_one_add_sq_mul_exp {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 1 / 2) :
    (1 + z) ^ 2 * Real.exp (-(6 * z)) ≤ (1 - z) ^ 2 := by
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * z)
  have h1 : (1 + z) ≤ (1 - z) * Real.exp (3 * z) := by
    have h2 : (1 + z) ≤ (1 - z) * (1 + 3 * z + (3 * z) ^ 2 / 2) := by nlinarith [sq_nonneg z]
    exact h2.trans (mul_le_mul_of_nonneg_left hq (by linarith))
  have hpos : 0 < Real.exp (3 * z) := Real.exp_pos _
  have hsq : (1 + z) ^ 2 ≤ (1 - z) ^ 2 * Real.exp (3 * z) ^ 2 := by
    have h0 : (0 : ℝ) ≤ 1 + z := by linarith
    calc (1 + z) ^ 2 ≤ ((1 - z) * Real.exp (3 * z)) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = _ := by ring
  have hexp : Real.exp (3 * z) ^ 2 * Real.exp (-(6 * z)) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    have h0 : ((2 : ℕ) : ℝ) * (3 * z) + -(6 * z) = 0 := by
      push_cast
      ring
    rw [h0, Real.exp_zero]
  calc (1 + z) ^ 2 * Real.exp (-(6 * z))
      ≤ (1 - z) ^ 2 * Real.exp (3 * z) ^ 2 * Real.exp (-(6 * z)) :=
        mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ = (1 - z) ^ 2 := by rw [mul_assoc, hexp, mul_one]

/-- `e^{−2x} ≤ 1 − x` for `0 ≤ x ≤ 1/2`. -/
theorem exp_neg_two_mul_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (-(2 * x)) ≤ 1 - x := by
  have h3 := Real.add_one_le_exp (2 * x)
  have hpos : 0 < Real.exp (2 * x) := Real.exp_pos _
  have h5 : Real.exp (-(2 * x)) * Real.exp (2 * x) = 1 := by
    rw [← Real.exp_add]
    simp
  have h4 : (0 : ℝ) ≤ 1 - x := by linarith
  have h2 : 1 ≤ (1 - x) * Real.exp (2 * x) := by
    have h6 := mul_le_mul_of_nonneg_left h3 h4
    nlinarith [mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ 1 - 2 * x)]
  by_contra hcon
  push Not at hcon
  have h7 := mul_lt_mul_of_pos_right hcon hpos
  linarith

/-- The two-point inequality when the error budget is at least one: the trivial bound. -/
theorem two_point_trivial {A ap am z K : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 1 / 2)
    (hA0 : 0 ≤ A) (hAu : A ≤ 1 + z) (hap : 1 - z ≤ ap) (ham : 1 - z ≤ am) (hK : 1 ≤ K) :
    A ^ 2 * Real.exp (-(6 * z * K)) ≤ ap * am := by
  have hz1 : (0 : ℝ) ≤ 1 - z := by linarith
  have h1 : (1 - z) ^ 2 ≤ ap * am := by
    have := mul_le_mul hap ham hz1 (hz1.trans hap)
    nlinarith
  have h2 : A ^ 2 ≤ (1 + z) ^ 2 := pow_le_pow_left₀ hA0 hAu 2
  have h3 : Real.exp (-(6 * z * K)) ≤ Real.exp (-(6 * z)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc A ^ 2 * Real.exp (-(6 * z * K))
      ≤ (1 + z) ^ 2 * Real.exp (-(6 * z)) :=
        mul_le_mul h2 h3 (Real.exp_pos _).le (by positivity)
    _ ≤ (1 - z) ^ 2 := one_sub_sq_ge_one_add_sq_mul_exp hz0 hz
    _ ≤ _ := h1

/-- The two-point inequality when the error budget is below one, in real variables: `S` is the
second difference and `D` the first difference of the real parts. -/
theorem two_point_perturbative {A S D z k₁ k₂ : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 1 / 2)
    (hk₂ : 0 ≤ k₂) (hA : 1 / 2 ≤ A) (hS : -(k₂ + 2 * k₁ ^ 2) ≤ S)
    (hD : D ^ 2 ≤ 16 * k₁ ^ 2) (hK : 2 * k₂ + 12 * k₁ ^ 2 ≤ 1) :
    A ^ 2 * Real.exp (-(6 * z * (2 * k₂ + 12 * k₁ ^ 2))) ≤
      (A + z * S / 2) ^ 2 - (z * D / 2) ^ 2 := by
  have hA0 : 0 ≤ A := by linarith
  have hm : 0 ≤ k₂ + 2 * k₁ ^ 2 := by positivity
  have hmid : A ^ 2 - A * z * (k₂ + 2 * k₁ ^ 2) ≤ (A + z * S / 2) ^ 2 := by
    have ht : 0 ≤ z * S / 2 + z * (k₂ + 2 * k₁ ^ 2) / 2 := by
      have := mul_le_mul_of_nonneg_left hS hz0
      linarith
    nlinarith [mul_nonneg hA0 ht, sq_nonneg (z * S / 2)]
  have hzD : (z * D / 2) ^ 2 ≤ 4 * z ^ 2 * k₁ ^ 2 := by
    have h1 : (z * D / 2) ^ 2 = z ^ 2 * D ^ 2 / 4 := by ring
    have h2 := mul_le_mul_of_nonneg_left hD (sq_nonneg z)
    rw [h1]
    linarith
  have hc1 : A * z * (k₂ + 2 * k₁ ^ 2) ≤ A ^ 2 * (z * (2 * k₂ + 4 * k₁ ^ 2)) := by
    have hnn : 0 ≤ A * z * (k₂ + 2 * k₁ ^ 2) := mul_nonneg (mul_nonneg hA0 hz0) hm
    have := mul_nonneg hnn (by linarith : (0 : ℝ) ≤ 2 * A - 1)
    nlinarith
  have hc2 : 4 * z ^ 2 * k₁ ^ 2 ≤ A ^ 2 * (z * (8 * k₁ ^ 2)) := by
    have hnn : 0 ≤ z * k₁ ^ 2 := mul_nonneg hz0 (sq_nonneg _)
    have hz2 : 4 * z ^ 2 * k₁ ^ 2 ≤ 2 * (z * k₁ ^ 2) := by
      have := mul_nonneg hnn (by linarith : (0 : ℝ) ≤ 1 - 2 * z)
      nlinarith
    have hA4 : (0 : ℝ) ≤ 4 * A ^ 2 - 1 := by nlinarith
    have := mul_nonneg hnn hA4
    nlinarith
  have hKexp : A ^ 2 * (1 - z * (2 * k₂ + 12 * k₁ ^ 2)) =
      A ^ 2 - A ^ 2 * (z * (2 * k₂ + 4 * k₁ ^ 2)) - A ^ 2 * (z * (8 * k₁ ^ 2)) := by ring
  have hlow : A ^ 2 * (1 - z * (2 * k₂ + 12 * k₁ ^ 2)) ≤
      (A + z * S / 2) ^ 2 - (z * D / 2) ^ 2 := by
    rw [hKexp]
    linarith
  have hK0 : 0 ≤ 2 * k₂ + 12 * k₁ ^ 2 := by positivity
  have hx : z * (2 * k₂ + 12 * k₁ ^ 2) ≤ 1 / 2 := by
    have := mul_le_mul hz hK hK0 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  have hx0 : 0 ≤ z * (2 * k₂ + 12 * k₁ ^ 2) := mul_nonneg hz0 hK0
  have hexpx : Real.exp (-(6 * z * (2 * k₂ + 12 * k₁ ^ 2))) ≤ 1 - z * (2 * k₂ + 12 * k₁ ^ 2) := by
    have h1 : Real.exp (-(6 * z * (2 * k₂ + 12 * k₁ ^ 2))) ≤
        Real.exp (-(2 * (z * (2 * k₂ + 12 * k₁ ^ 2)))) :=
      Real.exp_le_exp.mpr (by linarith)
    exact h1.trans (exp_neg_two_mul_le_one_sub hx0 hx)
  exact (mul_le_mul_of_nonneg_left hexpx (sq_nonneg A)).trans hlow

/-- First difference: `|Re(u₀ e^Δ) − Re u₀| ≤ 2k₁` for `|u₀| ≤ 1`, `|Δ| ≤ k₁ ≤ 1`. -/
theorem abs_re_mul_exp_sub_le {u₀ Δ : ℂ} {k₁ : ℝ} (hu₀ : ‖u₀‖ ≤ 1) (hΔ : ‖Δ‖ ≤ k₁)
    (hk₁ : k₁ ≤ 1) : |(u₀ * Complex.exp Δ).re - u₀.re| ≤ 2 * k₁ := by
  have hexp := Complex.norm_exp_sub_one_sub_id_le (hΔ.trans hk₁)
  have hid : u₀ * Complex.exp Δ - u₀ = u₀ * (Complex.exp Δ - 1 - Δ) + u₀ * Δ := by ring
  have hΔ0 := norm_nonneg Δ
  have hΔsq : ‖Δ‖ ^ 2 ≤ k₁ := by nlinarith
  have ha : ‖u₀ * (Complex.exp Δ - 1 - Δ)‖ ≤ k₁ := by
    rw [norm_mul]
    have := mul_le_mul hu₀ (hexp.trans hΔsq) (norm_nonneg _) zero_le_one
    linarith
  have hb : ‖u₀ * Δ‖ ≤ k₁ := by
    rw [norm_mul]
    have := mul_le_mul hu₀ hΔ (norm_nonneg _) zero_le_one
    linarith
  have hnorm : ‖u₀ * Complex.exp Δ - u₀‖ ≤ 2 * k₁ := by
    rw [hid]
    exact (norm_add_le _ _).trans (by linarith)
  have h := (Complex.abs_re_le_norm (u₀ * Complex.exp Δ - u₀)).trans hnorm
  rwa [Complex.sub_re] at h

/-- Second difference: `Re(u₀ e^{Δ₁}) + Re(u₀ e^{Δ₂}) − 2 Re u₀ ≥ −(k₂ + 2k₁²)`. -/
theorem re_second_difference_ge {u₀ Δp Δm : ℂ} {k₁ k₂ : ℝ} (hu₀ : ‖u₀‖ ≤ 1)
    (hΔp : ‖Δp‖ ≤ k₁) (hΔm : ‖Δm‖ ≤ k₁) (hk₁ : k₁ ≤ 1) (hsum : ‖Δp + Δm‖ ≤ k₂) :
    -(k₂ + 2 * k₁ ^ 2) ≤
      (u₀ * Complex.exp Δp).re + (u₀ * Complex.exp Δm).re - 2 * u₀.re := by
  have hexpp := Complex.norm_exp_sub_one_sub_id_le (hΔp.trans hk₁)
  have hexpm := Complex.norm_exp_sub_one_sub_id_le (hΔm.trans hk₁)
  have hsqp : ‖Δp‖ ^ 2 ≤ k₁ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hΔp 2
  have hsqm : ‖Δm‖ ^ 2 ≤ k₁ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hΔm 2
  have hid : u₀ * Complex.exp Δp + u₀ * Complex.exp Δm - 2 * u₀ = u₀ * (Δp + Δm) +
      u₀ * (Complex.exp Δp - 1 - Δp) + u₀ * (Complex.exp Δm - 1 - Δm) := by ring
  have ha : ‖u₀ * (Δp + Δm)‖ ≤ k₂ := by
    rw [norm_mul]
    have := mul_le_mul hu₀ hsum (norm_nonneg _) zero_le_one
    linarith
  have hb : ‖u₀ * (Complex.exp Δp - 1 - Δp)‖ ≤ k₁ ^ 2 := by
    rw [norm_mul]
    have := mul_le_mul hu₀ (hexpp.trans hsqp) (norm_nonneg _) zero_le_one
    linarith
  have hc : ‖u₀ * (Complex.exp Δm - 1 - Δm)‖ ≤ k₁ ^ 2 := by
    rw [norm_mul]
    have := mul_le_mul hu₀ (hexpm.trans hsqm) (norm_nonneg _) zero_le_one
    linarith
  have hnorm : ‖u₀ * Complex.exp Δp + u₀ * Complex.exp Δm - 2 * u₀‖ ≤ k₂ + 2 * k₁ ^ 2 := by
    rw [hid]
    have h1 := norm_add_le (u₀ * (Δp + Δm) + u₀ * (Complex.exp Δp - 1 - Δp))
      (u₀ * (Complex.exp Δm - 1 - Δm))
    have h2 := norm_add_le (u₀ * (Δp + Δm)) (u₀ * (Complex.exp Δp - 1 - Δp))
    linarith
  have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).1
  have hreq : (u₀ * Complex.exp Δp + u₀ * Complex.exp Δm - 2 * u₀).re =
      (u₀ * Complex.exp Δp).re + (u₀ * Complex.exp Δm).re - 2 * u₀.re := by
    simp
  linarith

/-- **The two-point inequality.** If `u_± = u₀ e^{Δ_±}` have modulus at most one, `|Δ_±| ≤ k₁`,
`|Δ_+ + Δ_-| ≤ k₂` and `0 ≤ z ≤ 1/2`, then
`(1 + z Re u_+)(1 + z Re u_-) ≥ (1 + z Re u₀)² e^{−6z(2k₂ + 12k₁²)}`. -/
theorem two_point_lower_bound {u₀ Δp Δm : ℂ} {z k₁ k₂ : ℝ}
    (hz0 : 0 ≤ z) (hz : z ≤ 1 / 2) (hu₀ : ‖u₀‖ ≤ 1)
    (hup : ‖u₀ * Complex.exp Δp‖ ≤ 1) (hum : ‖u₀ * Complex.exp Δm‖ ≤ 1)
    (hΔp : ‖Δp‖ ≤ k₁) (hΔm : ‖Δm‖ ≤ k₁) (hsum : ‖Δp + Δm‖ ≤ k₂) :
    (1 + z * u₀.re) ^ 2 * Real.exp (-(6 * z * (2 * k₂ + 12 * k₁ ^ 2))) ≤
      (1 + z * (u₀ * Complex.exp Δp).re) * (1 + z * (u₀ * Complex.exp Δm).re) := by
  have hk₁ : 0 ≤ k₁ := (norm_nonneg _).trans hΔp
  have hk₂ : 0 ≤ k₂ := (norm_nonneg _).trans hsum
  have h0 := abs_le.mp ((Complex.abs_re_le_norm u₀).trans hu₀)
  have hp := abs_le.mp ((Complex.abs_re_le_norm _).trans hup)
  have hm := abs_le.mp ((Complex.abs_re_le_norm _).trans hum)
  have hAl : 1 - z ≤ 1 + z * u₀.re := by nlinarith [h0.1]
  have hAu : 1 + z * u₀.re ≤ 1 + z := by nlinarith [h0.2]
  have hap : 1 - z ≤ 1 + z * (u₀ * Complex.exp Δp).re := by nlinarith [hp.1]
  have ham : 1 - z ≤ 1 + z * (u₀ * Complex.exp Δm).re := by nlinarith [hm.1]
  by_cases hbig : 1 ≤ 2 * k₂ + 12 * k₁ ^ 2
  · exact two_point_trivial hz0 hz (by linarith) hAu hap ham hbig
  · push Not at hbig
    have hk₁1 : k₁ ≤ 1 := by nlinarith
    have hS := re_second_difference_ge hu₀ hΔp hΔm hk₁1 hsum
    have hDp := abs_le.mp (abs_re_mul_exp_sub_le hu₀ hΔp hk₁1)
    have hDm := abs_le.mp (abs_re_mul_exp_sub_le hu₀ hΔm hk₁1)
    have hD : ((u₀ * Complex.exp Δp).re - (u₀ * Complex.exp Δm).re) ^ 2 ≤ 16 * k₁ ^ 2 := by
      have h1 : |(u₀ * Complex.exp Δp).re - (u₀ * Complex.exp Δm).re| ≤ 4 * k₁ := by
        rw [abs_le]
        constructor <;> linarith [hDp.1, hDp.2, hDm.1, hDm.2]
      calc _ = |(u₀ * Complex.exp Δp).re - (u₀ * Complex.exp Δm).re| ^ 2 := (sq_abs _).symm
        _ ≤ (4 * k₁) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = 16 * k₁ ^ 2 := by ring
    have hmain := two_point_perturbative (A := 1 + z * u₀.re)
      (S := (u₀ * Complex.exp Δp).re + (u₀ * Complex.exp Δm).re - 2 * u₀.re)
      (D := (u₀ * Complex.exp Δp).re - (u₀ * Complex.exp Δm).re) hz0 hz hk₂ (by linarith) hS hD
      hbig.le
    refine hmain.trans (le_of_eq ?_)
    ring

end

end FroehlichSpencer.FS82.ZN.Torus

end
