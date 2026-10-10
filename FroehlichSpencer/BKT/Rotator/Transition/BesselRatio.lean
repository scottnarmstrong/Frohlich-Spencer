/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.XYDuality

/-!
# The ratio bound `I_{n+1}(b) ≤ (b/2) I_n(b)` for the one-bond Fourier coefficients

Integrating by parts in `(2π)⁻¹ ∫₀^{2π} e^{b cos θ} cos(nθ) dθ` gives the recurrence
`n I_n = (b/2)(I_{n-1} - I_{n+1})`; nonnegativity of the coefficients for `b ≥ 0` then gives the
ratio bound used by the high-temperature current peeling.
-/

@[expose] public section

open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Transition

open FroehlichSpencer.BKT.Rotator.BesselInterp

/-- The three-term recurrence of the Fourier coefficients of `e^{b cos θ}`. -/
theorem besselCoeffRe_recurrence (b : ℝ) (n : ℤ) :
    (n : ℝ) * besselCoeffRe b n = b / 2 * (besselCoeffRe b (n - 1) - besselCoeffRe b (n + 1)) := by
  have hc : ∀ k : ℝ, Continuous fun θ : ℝ => Real.exp (b * Real.cos θ) * Real.cos (k * θ) := by
    intro k; fun_prop
  have hcs : Continuous fun θ : ℝ => Real.exp (b * Real.cos θ) * (Real.sin θ * Real.sin (n * θ)) := by
    fun_prop
  have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (0:ℝ)) (b := 2 * π)
    (u := fun θ => Real.exp (b * Real.cos θ)) (v := fun θ => Real.sin (n * θ))
    (u' := fun θ => -(b * Real.sin θ) * Real.exp (b * Real.cos θ))
    (v' := fun θ => n * Real.cos (n * θ))
    (fun x _ => by
      have := ((Real.hasDerivAt_cos x).const_mul b).exp
      convert this using 1; ring)
    (fun x _ => by
      have := ((hasDerivAt_id' x).const_mul (n : ℝ)).sin
      convert this using 1; ring)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  have hsin : Real.sin ((n : ℝ) * (2 * π)) = 0 := by
    have : (n : ℝ) * (2 * π) = ((2 * n : ℤ) : ℝ) * π := by push_cast; ring
    rw [this]; exact Real.sin_int_mul_pi _
  have h1 : (n : ℝ) * ∫ θ in (0:ℝ)..2 * π, Real.exp (b * Real.cos θ) * Real.cos (n * θ)
      = b * ∫ θ in (0:ℝ)..2 * π, Real.exp (b * Real.cos θ) * (Real.sin θ * Real.sin (n * θ)) := by
    have e1 : ∫ θ in (0:ℝ)..2 * π, Real.exp (b * Real.cos θ) * (n * Real.cos (n * θ))
        = n * ∫ θ in (0:ℝ)..2 * π, Real.exp (b * Real.cos θ) * Real.cos (n * θ) := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; ext θ; ring
    have e2 : ∫ θ in (0:ℝ)..2 * π, -(b * Real.sin θ) * Real.exp (b * Real.cos θ) * Real.sin (n * θ)
        = -(b * ∫ θ in (0:ℝ)..2 * π, Real.exp (b * Real.cos θ) * (Real.sin θ * Real.sin (n * θ))) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
      congr 1; ext θ; ring
    rw [e1, e2, hsin] at hp
    simp at hp
    linarith
  have h2 : (∫ θ in (0:ℝ)..2 * π, Real.exp (b * Real.cos θ) * Real.cos (((n - 1 : ℤ) : ℝ) * θ))
      - (∫ θ in (0:ℝ)..2 * π, Real.exp (b * Real.cos θ) * Real.cos (((n + 1 : ℤ) : ℝ) * θ))
      = 2 * ∫ θ in (0:ℝ)..2 * π, Real.exp (b * Real.cos θ) * (Real.sin θ * Real.sin (n * θ)) := by
    rw [← intervalIntegral.integral_sub ((hc _).intervalIntegrable _ _) ((hc _).intervalIntegrable _ _),
      ← intervalIntegral.integral_const_mul]
    congr 1; ext θ
    push_cast
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    simp only [one_mul]
    ring
  unfold besselCoeffRe
  linear_combination (2 * π)⁻¹ * h1 - b / 2 * (2 * π)⁻¹ * h2

/-- The ratio bound for nonnegative `b`. -/
theorem besselCoeffRe_succ_le {b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    besselCoeffRe b ((n : ℤ) + 1) ≤ b / 2 * besselCoeffRe b n := by
  have hr := besselCoeffRe_recurrence b ((n : ℤ) + 1)
  have h0 := besselCoeffRe_nonneg hb (n : ℤ)
  have h2 := besselCoeffRe_nonneg hb ((n : ℤ) + 1 + 1)
  have h1 := besselCoeffRe_nonneg hb ((n : ℤ) + 1)
  simp only [add_sub_cancel_right] at hr
  have hn : (1 : ℝ) ≤ (((n : ℤ) + 1 : ℤ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have : (((n : ℤ) + 1 : ℤ) : ℝ) * besselCoeffRe b ((n : ℤ) + 1) ≤ b / 2 * besselCoeffRe b n := by
    rw [hr]; nlinarith
  nlinarith

/-- Lowering a positive current value by one costs at most a factor `b/2`. -/
theorem rotatorIReal_le_of_pos {b : ℝ} (hb : 0 ≤ b) {m : ℤ} (hm : 1 ≤ m) :
    rotatorIReal b m ≤ b / 2 * rotatorIReal b (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = (k : ℤ) + 1 := ⟨(m - 1).toNat, by omega⟩
  simpa [rotatorIReal] using besselCoeffRe_succ_le hb k

/-- Raising a negative current value by one costs at most a factor `b/2`. -/
theorem rotatorIReal_le_of_neg {b : ℝ} (hb : 0 ≤ b) {m : ℤ} (hm : m ≤ -1) :
    rotatorIReal b m ≤ b / 2 * rotatorIReal b (m + 1) := by
  have := rotatorIReal_le_of_pos hb (m := -m) (by omega)
  simp only [rotatorIReal, besselCoeffRe_neg] at this ⊢
  have e : -m - 1 = -(m + 1) := by ring
  rwa [e, besselCoeffRe_neg] at this

theorem rotatorIReal_nonneg {b : ℝ} (hb : 0 ≤ b) (m : ℤ) : 0 ≤ rotatorIReal b m := by
  exact besselCoeffRe_nonneg hb m

end FroehlichSpencer.BKT.Rotator.Transition

end
