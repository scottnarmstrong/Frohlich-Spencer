/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Green.CombesThomas
public import FroehlichSpencer.Infra.Spectral.ResolventNorm

/-!
# Combes–Thomas decay from a lower bound, and from a real spectral gap

If `c ‖u‖ ≤ ‖(H_Λ - z) u‖` for all `u`, then the finite-volume resolvent decays exponentially:
`|G_Λ(z; x, y)| ≤ (2/c) exp(-μ d(x, y))`, `μ = log (1 + c / (2 (K + 1)))`, uniformly in `Λ` and
the potential.

For real `E` at distance at least `κ > 0` from the spectrum of `H_Λ` the hypothesis
holds with `c = κ`.

This is the mechanism of Condition A(c) of Fröhlich–Spencer (1983)
(Fröhlich–Spencer (1983)) and of the remark in Appendix B on a gap in the spectrum.
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace FroehlichSpencer.Infra

section Main

variable {X : Type*} [DecidableEq X] {a : X → X → ℂ} {K : ℝ}

theorem norm_resolventColumn_le_exp_of_lower_bound (ha : ∀ x y, a y x = star (a x y))
    (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    {d : X → X → ℝ} (hd : ∀ x y w, d x y ≤ d x w + d w y) (hd0 : ∀ x, d x x = 0)
    (hrange : ∀ x y, a x y ≠ 0 → d x y ≤ 1)
    (v : X → ℝ) (Λ : Finset X) {z : ℂ} {c : ℝ} (hc : 0 < c)
    (hlow : ∀ u : Λ → ℂ, c * ‖WithLp.toLp 2 u‖ ≤
      ‖WithLp.toLp 2 ((restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)) *ᵥ u)‖) (x y : X) :
    ‖resolventColumn a v Λ z y x‖ ≤
      2 / c * Real.exp (-Real.log (1 + c / (2 * (K + 1))) * d x y) := by
  have hinj : Function.Injective
      (restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)).mulVec := by
    intro u w huw
    have h := hlow (u - w)
    rw [Matrix.mulVec_sub, huw, sub_self, WithLp.toLp_zero, norm_zero] at h
    have h0 : ‖WithLp.toLp 2 (u - w)‖ = 0 := by
      have := norm_nonneg (WithLp.toLp 2 (u - w))
      nlinarith only [h, this, hc]
    rw [norm_eq_zero] at h0
    have h1 : u - w = 0 := by
      refine funext fun i => ?_
      have := congrArg (fun t => (WithLp.ofLp t) i) h0
      simpa using this
    exact sub_eq_zero.mp h1
  exact combesThomas_core ha hK hd hd0 hrange v Λ hc
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)) hlow x y

theorem norm_resolventColumn_le_exp_of_gap (ha : ∀ x y, a y x = star (a x y))
    (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    {d : X → X → ℝ} (hd : ∀ x y w, d x y ≤ d x w + d w y) (hd0 : ∀ x, d x x = 0)
    (hrange : ∀ x y, a x y ≠ 0 → d x y ≤ 1) (v : X → ℝ) (Λ : Finset X) {E κ : ℝ} (hκ : 0 < κ)
    (hgap : ∀ i, κ ≤ |(isHermitian_restrictedOp ha v Λ).eigenvalues i - E|) (x y : X) :
    ‖resolventColumn a v Λ (E : ℂ) y x‖ ≤
      2 / κ * Real.exp (-Real.log (1 + κ / (2 * (K + 1))) * d x y) := by
  refine norm_resolventColumn_le_exp_of_lower_bound ha hK hd hd0 hrange v Λ hκ ?_ x y
  intro u
  by_cases hne : Nonempty Λ
  · have hH := isHermitian_restrictedOp ha v Λ
    have hmin : κ ≤ Finset.univ.inf' Finset.univ_nonempty
        (fun i => |hH.eigenvalues i - E|) := Finset.le_inf' _ _ fun i _ => hgap i
    obtain ⟨hU, hinv⟩ := (le_inf'_abs_eigenvalues_sub_iff_norm_inv_le hH E hκ).mp hmin
    set M := restrictedOp a v Λ - (E : ℂ) • (1 : Matrix Λ Λ ℂ) with hM
    have hu : u = M⁻¹ *ᵥ (M *ᵥ u) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
        ((Matrix.isUnit_iff_isUnit_det _).mp hU), Matrix.one_mulVec]
    have h1 := Matrix.l2_opNorm_mulVec M⁻¹ (WithLp.toLp 2 (M *ᵥ u))
    have h2 : ‖WithLp.toLp 2 u‖ ≤ 1 / κ * ‖WithLp.toLp 2 (M *ᵥ u)‖ := by
      calc ‖WithLp.toLp 2 u‖ = ‖WithLp.toLp 2 (M⁻¹ *ᵥ (M *ᵥ u))‖ := by rw [← hu]
        _ ≤ ‖M⁻¹‖ * ‖WithLp.toLp 2 (M *ᵥ u)‖ := h1
        _ ≤ 1 / κ * ‖WithLp.toLp 2 (M *ᵥ u)‖ :=
          mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hκ] at h2
    linarith only [h2]
  · rw [not_nonempty_iff] at hne
    have hu : u = 0 := funext fun i => isEmptyElim i
    subst hu
    rw [Matrix.mulVec_zero, WithLp.toLp_zero, norm_zero, mul_zero]

end Main

end FroehlichSpencer.Infra
