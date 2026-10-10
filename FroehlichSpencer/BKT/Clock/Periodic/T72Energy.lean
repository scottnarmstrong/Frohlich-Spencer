/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Periodic.ClockWeight
public import FroehlichSpencer.BKT.Generic.SpinWave.Graded
public import FroehlichSpencer.BKT.Generic.Renormalization.Activity

/-!
# The clock specialization of the generic contour-energy bound

The exact clock shift cost is `β (cosh (u / n) - 1)`.

On a contour strip of width `W ≤ n`,
`ClockWeight.lean` gives its quadratic/exponential cost envelope with coefficients
`κ = β / n²` and `κ' = β W² / n²`.

The theorems below specialize the generic graded-wave energy
bound and its gain consequence to that cost.

The edge-count bound, exponential-branch smallness, and lower bounds on the quadratic amplitudes
remain hypotheses.

This module therefore supplies the clock-specific scalar substitution, not the
scale induction or the T7.2 activity estimate.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Periodic

open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.SpinWave

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  {G : Multigraph V E} {N₀ : Finset (V → ℤ)} {centerOf : (V → ℤ) → V} {ρ : V → ℤ}

/-- The generic two-branch energy estimate with the clock shift cost. The clock-specific input is
the envelope coefficient pair `(β / n², β W² / n²)` on a strip `W ≤ n`; all spin-wave and
nonzero-gradient edge-count hypotheses are the generic ones. -/
theorem clock_translationEnergy_envelopeWave_ge (Wv : GradedSpinWave G N₀ centerOf ρ)
    {β n W : ℝ} (hβ : 0 < β) (hn : 1 ≤ n) (hWn : W ≤ n)
    (hK₀ : 0 < Wv.K₀) (hK₁ : 0 < Wv.K₁) {lam : ℝ} (hlam : 0 ≤ lam)
    (hlamW : lam * Wv.K₁ ≤ W) (k₀ : ℕ) {N : ℝ}
    (hcount : ∀ t, Wv.scale t < k₀ →
      ((Finset.univ.filter fun e => G.grad (Wv.piece t) e ≠ 0).card : ℝ) ≤ N) :
    letI := Wv.finite
    (∑ t ∈ Finset.univ.filter (fun t => Wv.scale t < k₀),
        (lam * |Wv.charge t| - N * costMajorant (β / n ^ 2) (β * W ^ 2 / n ^ 2)
          (lam * Wv.K₁))) +
      ∑ t ∈ Finset.univ.filter (fun t => ¬Wv.scale t < k₀),
        quadAmplitude (β / n ^ 2) Wv.K₀ Wv.K₁ (gradExponent Wv.alpha) (Wv.scale t) / 2 ≤
      translationEnergy (clockShiftCost β n) (gradLinear G)
        (envelopeWave Wv (β / n ^ 2) lam k₀) (fun j => (ρ j : ℝ)) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hκ : 0 < β / n ^ 2 := div_pos hβ (sq_pos_of_pos hn0)
  exact Generic.translationEnergy_envelopeWave_ge Wv
    (clockShiftCost_isCostEnvelope hβ.le hn hWn) hκ hK₀ hK₁ hlam hlamW k₀ hcount

/-- The clock-specific gain form of the generic envelope estimate. Once the explicit
exponential-branch smallness and large-scale amplitude hypotheses hold, the clock translation
energy controls the base charges and the number of positive-scale pieces. -/
theorem clock_translationEnergy_envelopeWave_ge_gain (Wv : GradedSpinWave G N₀ centerOf ρ)
    {β n W : ℝ} (hβ : 0 < β) (hn : 1 ≤ n) (hWn : W ≤ n)
    (hK₀ : 0 < Wv.K₀) (hK₁ : 0 < Wv.K₁) {lam : ℝ} (hlam : 0 ≤ lam)
    (hlamW : lam * Wv.K₁ ≤ W) {k₀ : ℕ} (hk₀ : 1 ≤ k₀) {N : ℝ}
    (hcount : ∀ t, Wv.scale t < k₀ →
      ((Finset.univ.filter fun e => G.grad (Wv.piece t) e ≠ 0).card : ℝ) ≤ N)
    (hexp : N * costMajorant (β / n ^ 2) (β * W ^ 2 / n ^ 2)
      (lam * Wv.K₁) ≤ lam / 2)
    (hquad : ∀ s, k₀ ≤ s →
      lam ≤ quadAmplitude (β / n ^ 2) Wv.K₀ Wv.K₁ (gradExponent Wv.alpha) s) :
    letI := Wv.finite
    lam / 2 * ((∑ t ∈ Finset.univ.filter (fun t => Wv.scale t = 0), |Wv.charge t|) +
        ((Finset.univ.filter fun t => 1 ≤ Wv.scale t).card : ℝ)) ≤
      translationEnergy (clockShiftCost β n) (gradLinear G)
        (envelopeWave Wv (β / n ^ 2) lam k₀) (fun j => (ρ j : ℝ)) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hκ : 0 < β / n ^ 2 := div_pos hβ (sq_pos_of_pos hn0)
  exact Generic.translationEnergy_envelopeWave_ge_gain Wv
    (clockShiftCost_isCostEnvelope hβ.le hn hWn) hκ hK₀ hK₁ hlam hlamW hk₀ hcount hexp hquad

end FroehlichSpencer.BKT.Clock.Periodic

end
