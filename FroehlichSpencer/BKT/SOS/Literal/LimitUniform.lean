/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.LimitPaths

/-!
# The uniform exponential bound (*) (the comb-inserted SOS construction)

`literal_exp_abs_le`: for `0 ≤ c < β ≤ 1`, every box `L > 1`, every region `A` and all sites `u, v`,

`⟨e^{c|φ(u)−φ(v)|}⟩_{L,A} ≤ 2 (2K₀)^{2‖u−v‖_∞/(1−c²/β²)}`, `K₀ = (β/β_λ) e^{(β−β_λ)√q₀}`,
`β_λ = √(β² − c²)`, `q₀ = β^{−2/3}`.

The bound does not depend on the box or on `A`.

`literal_exp_abs_plane` is the same bound for
plane sites in the centred boxes.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory
open FroehlichSpencer.BKT.Generic.PinnedCharges (SquareZeroBond Site)
open FroehlichSpencer.BKT.SOS.Roughening

variable {L : ℕ}

/-- The constant `(2K₀)^{1/(1−c²/β²)}` of (*). -/
def expBoundBase (β c : ℝ) : ℝ := (2 * tiltK0 β (c ^ 2 / 2)) ^ (1 / (1 - c ^ 2 / β ^ 2))

theorem one_le_two_tiltK0 {β lam : ℝ} (hβ : 0 < β) (hl0 : 0 ≤ lam) (hl : 2 * lam < β ^ 2) :
    1 ≤ 2 * tiltK0 β lam := by
  unfold tiltK0
  have hb := betaLam_pos hl
  have hbβ := betaLam_le hβ hl0
  have h1 : 1 ≤ β / betaLam β lam := by rw [le_div_iff₀ hb]; linarith
  have h2 : 1 ≤ Real.exp ((β - betaLam β lam) * Real.sqrt (mixQ0 β)) :=
    Real.one_le_exp (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
  nlinarith

/-- **(*) in the box**: `⟨e^{c|φ(u)−φ(v)|}⟩ ≤ 2 (2K₀)^{2‖u−v‖_∞/(1−c²/β²)}`. -/
theorem literal_exp_abs_le (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (A : Finset (Site L)) {c : ℝ} (hc0 : 0 ≤ c) (hcβ : c < β) (u v : Site L) :
    ∫⁻ φ, ENNReal.ofReal (Real.exp (c * |φ u - φ v|)) ∂literalState L β A ≤
      ENNReal.ofReal (2 * expBoundBase β c ^ (2 * linfDist u v)) := by
  obtain ⟨P, θ, ⟨hs, hb, hd⟩, hcard⟩ := exists_flow u v
  have hc2 : 2 * (c ^ 2 / 2) < β ^ 2 := by nlinarith
  have hθ1 : 1 - c ^ 2 / β ^ 2 > 0 := by
    rw [gt_iff_lt, sub_pos, div_lt_one (by positivity)]; nlinarith
  have hK := one_le_two_tiltK0 hβ (by positivity) hc2
  have hmono : (2 * tiltK0 β (c ^ 2 / 2)) ^ ((P.card : ℝ) / (1 - c ^ 2 / β ^ 2)) ≤
      expBoundBase β c ^ (2 * linfDist u v) := by
    have heq : expBoundBase β c ^ (2 * linfDist u v) = (2 * tiltK0 β (c ^ 2 / 2)) ^
        (((2 * linfDist u v : ℕ) : ℝ) / (1 - c ^ 2 / β ^ 2)) := by
      unfold expBoundBase
      rw [← Real.rpow_natCast ((2 * tiltK0 β (c ^ 2 / 2)) ^ (1 / (1 - c ^ 2 / β ^ 2)))
        (2 * linfDist u v), ← Real.rpow_mul (by linarith)]
      congr 1
      ring
    rw [heq]
    refine Real.rpow_le_rpow_of_exponent_le hK ?_
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hθ1.le
  have hplus := lintegral_exp_flow_bound hL hβ hβ1 A P hc0 hcβ hs hb
  have hminus := lintegral_exp_flow_bound hL hβ hβ1 A P hc0 hcβ (θ := -θ)
    (fun e he => by simp [hs e he]) (fun e => by simpa using hb e)
  have hg : Continuous (pinnedGrad L) := (pinnedGrad L).continuous_of_finiteDimensional
  have hm : ∀ θ' : SquareZeroBond L → ℝ, Measurable fun φ : Site L → ℝ =>
      ENNReal.ofReal (Real.exp (c * ∑ e, θ' e * pinnedGrad L φ e)) := fun θ' =>
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul
      (continuous_finsetSum _ fun e _ => continuous_const.mul
        ((continuous_apply e).comp hg)))).measurable
  calc ∫⁻ φ, ENNReal.ofReal (Real.exp (c * |φ u - φ v|)) ∂literalState L β A
      ≤ ∫⁻ φ, (ENNReal.ofReal (Real.exp (c * ∑ e, θ e * pinnedGrad L φ e)) +
          ENNReal.ofReal (Real.exp (c * ∑ e, (-θ) e * pinnedGrad L φ e))) ∂literalState L β A := by
        refine lintegral_mono fun φ => ?_
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        have hneg : ∑ e, (-θ) e * pinnedGrad L φ e = -(φ u - φ v) := by
          simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, hd]
        rw [hd, hneg]
        rcases le_or_gt 0 (φ u - φ v) with h | h
        · rw [abs_of_nonneg h]; linarith [Real.exp_pos (c * -(φ u - φ v))]
        · rw [abs_of_neg h]; linarith [Real.exp_pos (c * (φ u - φ v))]
    _ = ∫⁻ φ, ENNReal.ofReal (Real.exp (c * ∑ e, θ e * pinnedGrad L φ e)) ∂literalState L β A +
        ∫⁻ φ, ENNReal.ofReal (Real.exp (c * ∑ e, (-θ) e * pinnedGrad L φ e))
          ∂literalState L β A := lintegral_add_left (hm θ) _
    _ ≤ ENNReal.ofReal ((2 * tiltK0 β (c ^ 2 / 2)) ^ ((P.card : ℝ) / (1 - c ^ 2 / β ^ 2))) +
        ENNReal.ofReal ((2 * tiltK0 β (c ^ 2 / 2)) ^ ((P.card : ℝ) / (1 - c ^ 2 / β ^ 2))) :=
        add_le_add hplus hminus
    _ ≤ ENNReal.ofReal (2 * expBoundBase β c ^ (2 * linfDist u v)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        linarith

/-- **(*) in the plane**: for plane sites `v, w` and every centred box around them,
`⟨e^{c|φ(v)−φ(w)|}⟩ ≤ 2 (2K₀)^{2‖v−w‖_∞/(1−c²/β²)}`, uniformly in the box and the region. -/
theorem literal_exp_abs_plane {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {c : ℝ} (hc0 : 0 ≤ c)
    (hcβ : c < β) (A : Finset (ℤ × ℤ)) (v w : ℤ × ℤ) :
    ∃ L_A : ℕ, ∀ L, L_A ≤ L →
      ∫⁻ φ, ENNReal.ofReal (Real.exp (c * |φ (centeredSite L v) - φ (centeredSite L w)|))
          ∂literalState (L + 1) β (centeredRegion L A) ≤
        ENNReal.ofReal (2 * expBoundBase β c ^ (2 * planeLinf v w)) := by
  set R := max (max v.1.natAbs v.2.natAbs) (max w.1.natAbs w.2.natAbs) with hR
  refine ⟨2 * R + 1, fun L hL => ?_⟩
  have hv1 : v.1.natAbs ≤ R := by rw [hR]; omega
  have hv2 : v.2.natAbs ≤ R := by rw [hR]; omega
  have hw1 : w.1.natAbs ≤ R := by rw [hR]; omega
  have hw2 : w.2.natAbs ≤ R := by rw [hR]; omega
  have hlinf := linfDist_centeredSite hL hv1 hv2 hw1 hw2
  rw [← hlinf]
  exact literal_exp_abs_le (by omega) hβ hβ1 _ hc0 hcβ _ _

end FroehlichSpencer.BKT.SOS.Literal

end
