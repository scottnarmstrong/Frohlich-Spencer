/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Tilt.Law
public import FroehlichSpencer.BKT.Generic.Moment.Branch

/-!
# The tilted branch bound (the dipole tilt construction)

The branch bound `integral_shiftProduct_ge` (FS81 (6.28)–(6.39), one ensemble) with the tilt
`e^{⟨∇φ, b⟩}` on the shifted side. The tilt exponent is linear, hence odd, so it joins the
first-order exponent in the symmetrization (`integral_ge_of_odd_exponent`) with prefactor one: the
tilt costs nothing in the branch bound. Its only effect on the moment bound is the phase
`⟨∇a_ρ, b⟩` of the renormalized factors (`rootedD_identity_of_law_phased`), which enters the error
through the phase `s`.

`integral_shiftProduct_tilt_ge`: `e^{−κ‖θ‖² − ∑ err} ∫ ρ₀ Π₀ ≤ ∫ e^{⟨∇φ, b⟩} ρ_θ Π₁`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Tilt

open MeasureTheory
open FroehlichSpencer.BKT.Generic

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

/-- **The tilted branch bound.** The hypotheses are those of `integral_shiftProduct_ge`, plus an
exponential majorant of the weight and `|b| ≤ η/2` (integrability of the tilted density). -/
theorem integral_shiftProduct_tilt_ge (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (v : V) (hw : IsStripWeight w W c) (hW : 0 < W) (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {M : ℝ → ℝ} (hlog : HasLogDerivBounds w W M) {κ : ℝ} (hcurv : HasCurvatureBound w κ)
    {η K : ℝ} (hη : 0 < η) (hexp : HasExpMajorant w W η K) (b : E → ℝ)
    (hb : ∀ e, |b e| ≤ η / 2)
    (N : Finset (V → ℤ)) (bb : (V → ℤ) → E → ℝ) (z : (V → ℤ) → ℝ) (A m : ℝ)
    (hbA : ∀ ϱ ∈ N, ∀ e, |bb ϱ e| ≤ A) (hAW : A ≤ W) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hM : ∀ u : ℝ, |u| ≤ A → M u ≤ m) (hz : ∀ ϱ ∈ N, |z ϱ| ≤ 1 / 8) (θ : E → ℝ)
    (s T : (V → ℤ) → ℝ) (hθT : ∀ ϱ ∈ N, ∀ e, bb ϱ e ≠ 0 → |θ e| ≤ T ϱ) :
    Real.exp (-(κ * ∑ e, θ e ^ 2 + ∑ ϱ ∈ N, 8 * |z ϱ| *
        (s ϱ ^ 2 + (((Finset.univ.filter fun e => bb ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
          ((Finset.univ.filter fun e => bb ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2))) *
        ∫ φ, edgeDensity G w v φ * shiftProduct G w c N bb z θ s 0 φ ≤
      ∫ φ, tiltDensity G w θ b v φ * shiftProduct G w c N bb z θ s 1 φ := by
  have hbW : ∀ ϱ ∈ N, ∀ e, |bb ϱ e| ≤ W := fun ϱ hϱ e => (hbA ϱ hϱ e).trans hAW
  set err : (V → ℤ) → ℝ := fun ϱ => 8 * |z ϱ| *
    (s ϱ ^ 2 + (((Finset.univ.filter fun e => bb ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
      ((Finset.univ.filter fun e => bb ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2) with herr
  refine integral_ge_of_odd_exponent
    (H := fun φ => shiftExponent G w c N bb z θ s φ + tiltExponent (gradLinear G) b φ) _
    (integrable_mul_shiftProduct hw G (integrable_tiltDensity G hG hw hη hexp θ b hb v)
      N bb hbW z hz θ s 1)
    (integrable_mul_shiftProduct hw G (integrable_edgeDensity G hG hw v) N bb hbW z hz θ s 0)
    (fun φ => mul_nonneg (edgeDensity_nonneg G hw v φ)
      (shiftProduct_pos hw G N bb hbW z hz θ s 0 φ).le) ?_
    (fun φ => by
      rw [shiftExponent_neg hw hW G N bb hbW z θ s, tiltExponent_neg, neg_add]) fun φ => ?_
  · filter_upwards [edgeDensity_neg_ae G hw v] with φ hφ
    rw [hφ, shiftProduct_zero_neg hw G N bb hbW z θ s φ]
  -- the pointwise comparison: the edge weights
  have hρ : edgeDensity G w v φ *
      Real.exp (edgeShiftExponent G w θ φ - κ * ∑ e, θ e ^ 2) ≤
      offsetEdgeDensity G w θ v φ := by
    unfold edgeDensity offsetEdgeDensity edgeShiftExponent
    have hind : 0 ≤ (Set.Ico (-Real.pi) Real.pi).indicator (1 : ℝ → ℝ) (φ v) := by
      by_cases h : φ v ∈ Set.Ico (-Real.pi) Real.pi <;> simp [h]
    rw [mul_right_comm]
    exact mul_le_mul_of_nonneg_right (prod_re_shift_ge hw hcurv (G.grad φ) θ) hind
  -- the factors
  have hfac := prod_mul_exp_le_prod N
    (fun ϱ => 1 + z ϱ * lineFactor w c (bb ϱ) (G.grad φ) θ (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) 0)
    (fun ϱ => 1 + z ϱ * lineFactor w c (bb ϱ) (G.grad φ) θ (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) 1)
    (fun ϱ => z ϱ * deriv (lineFactor w c (bb ϱ) (G.grad φ) θ (∑ j, φ j * (ϱ j : ℝ)) (s ϱ)) 0)
    err (fun ϱ hϱ => lt_of_lt_of_le (by norm_num)
      (one_add_mul_lineFactor_ge_seven_eighths hw (bb ϱ) (hbW ϱ hϱ) (hz ϱ hϱ) _ _ _ _ _))
    fun ϱ hϱ => one_add_mul_lineFactor_ge hw hnzero hlog (bb ϱ) (G.grad φ) θ
      (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) (z ϱ) A (T ϱ) m (hbA ϱ hϱ) hAW (hθT ϱ hϱ) hm0 hm1 hM (hz ϱ hϱ)
  have key : Real.exp (-(κ * ∑ e, θ e ^ 2 + ∑ ϱ ∈ N, err ϱ)) *
      (edgeDensity G w v φ * shiftProduct G w c N bb z θ s 0 φ *
        Real.exp (shiftExponent G w c N bb z θ s φ)) ≤
      offsetEdgeDensity G w θ v φ * shiftProduct G w c N bb z θ s 1 φ :=
    exp_mul_le_of_le (edgeDensity_nonneg G hw v φ)
      (shiftProduct_pos hw G N bb hbW z hz θ s 0 φ).le hρ hfac
  have htilt := (Real.exp_pos (tiltExponent (gradLinear G) b φ)).le
  calc Real.exp (-(κ * ∑ e, θ e ^ 2 + ∑ ϱ ∈ N, err ϱ)) *
        (edgeDensity G w v φ * shiftProduct G w c N bb z θ s 0 φ *
          Real.exp (shiftExponent G w c N bb z θ s φ + tiltExponent (gradLinear G) b φ))
      = Real.exp (tiltExponent (gradLinear G) b φ) *
        (Real.exp (-(κ * ∑ e, θ e ^ 2 + ∑ ϱ ∈ N, err ϱ)) *
          (edgeDensity G w v φ * shiftProduct G w c N bb z θ s 0 φ *
            Real.exp (shiftExponent G w c N bb z θ s φ))) := by
        rw [Real.exp_add]; ring
    _ ≤ Real.exp (tiltExponent (gradLinear G) b φ) *
        (offsetEdgeDensity G w θ v φ * shiftProduct G w c N bb z θ s 1 φ) :=
        mul_le_mul_of_nonneg_left key htilt
    _ = tiltDensity G w θ b v φ * shiftProduct G w c N bb z θ s 1 φ := by
        unfold tiltDensity; ring

end FroehlichSpencer.BKT.SOS.Tilt

end
