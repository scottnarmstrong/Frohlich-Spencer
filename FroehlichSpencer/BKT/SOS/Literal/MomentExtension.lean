/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Extended moment generating functions: log-convexity and the all-`ε` bound (the finite comb construction)

FS81's (7.17) prints no range of `ε`. The moment `⟨e^{εX}⟩` is a genuine `[0, ∞]`-valued lintegral
(`mgfExt`). It is **log-convex** by Hölder's inequality (`mgfExt_le_rpow_mul_rpow`):
`M((1 − t)a + tb) ≤ M(a)^{1−t} M(b)^t`, with `M(0) = 1` for a probability measure.

`le_mgfExt_of_window`: if `M` is even, `M(ε) ≥ e^{aε²}` on `|ε| ≤ ε₁` and `M(ε) = ∞` for
`|ε| ≥ 8ε₁`, then `M(ε) ≥ e^{(a/8)ε²}` for **every** `ε`. In between, log-convexity on `[0, ε]`
gives `log M(ε) ≥ (ε/ε₁) log M(ε₁) ≥ a ε₁ ε ≥ a ε²/8`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The extended moment generating function `M(ε) = ∫⁻ e^{εX} dμ ∈ [0, ∞]`. -/
def mgfExt (μ : Measure Ω) (X : Ω → ℝ) (ε : ℝ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (Real.exp (ε * X ω)) ∂μ

theorem mgfExt_zero (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) :
    mgfExt μ X 0 = 1 := by
  simp [mgfExt]

/-- **Log-convexity** (Hölder). -/
theorem mgfExt_le_rpow_mul_rpow (μ : Measure Ω) {X : Ω → ℝ} (hX : Measurable X) (a b : ℝ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    mgfExt μ X ((1 - t) * a + t * b) ≤ mgfExt μ X a ^ (1 - t) * mgfExt μ X b ^ t := by
  have h1t : 0 < 1 - t := by linarith
  have hpq : Real.HolderConjugate (1 - t)⁻¹ t⁻¹ :=
    ⟨by rw [inv_inv, inv_inv, inv_one]; ring, inv_pos.mpr h1t, inv_pos.mpr ht0⟩
  set f : Ω → ENNReal := fun ω => ENNReal.ofReal (Real.exp ((1 - t) * a * X ω)) with hf
  set g : Ω → ENNReal := fun ω => ENNReal.ofReal (Real.exp (t * b * X ω)) with hg
  have hfm : AEMeasurable f μ :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hX.const_mul _))).aemeasurable
  have hgm : AEMeasurable g μ :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hX.const_mul _))).aemeasurable
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hfm hgm
  have hfg : ∀ ω, (f * g) ω = ENNReal.ofReal (Real.exp (((1 - t) * a + t * b) * X ω)) := by
    intro ω
    simp only [Pi.mul_apply, hf, hg]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  have hfp : ∀ ω, f ω ^ (1 - t)⁻¹ = ENNReal.ofReal (Real.exp (a * X ω)) := by
    intro ω
    simp only [hf]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (inv_pos.mpr h1t).le,
      ← Real.exp_mul]
    congr 2
    field_simp
  have hgq : ∀ ω, g ω ^ t⁻¹ = ENNReal.ofReal (Real.exp (b * X ω)) := by
    intro ω
    simp only [hg]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (inv_pos.mpr ht0).le,
      ← Real.exp_mul]
    congr 2
    field_simp
  simp_rw [hfg, hfp, hgq] at hH
  unfold mgfExt
  simpa only [one_div, inv_inv] using hH

/-- **The all-`ε` bound from a window and divergence** (FS81 (7.17) for every `ε`). -/
theorem le_mgfExt_of_window (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) {a ε₁ : ℝ} (ha : 0 ≤ a) (hε₁ : 0 < ε₁)
    (heven : ∀ ε, mgfExt μ X (-ε) = mgfExt μ X ε)
    (hlow : ∀ ε, |ε| ≤ ε₁ → ENNReal.ofReal (Real.exp (a * ε ^ 2)) ≤ mgfExt μ X ε)
    (hdiv : ∀ ε, 8 * ε₁ ≤ |ε| → mgfExt μ X ε = ⊤) (ε : ℝ) :
    ENNReal.ofReal (Real.exp (a / 8 * ε ^ 2)) ≤ mgfExt μ X ε := by
  -- reduce to `ε ≥ 0`
  have habs : mgfExt μ X ε = mgfExt μ X |ε| := by
    rcases le_or_gt 0 ε with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, heven]
  rw [habs, ← sq_abs ε]
  set e := |ε| with he
  have he0 : 0 ≤ e := abs_nonneg ε
  rcases le_or_gt e ε₁ with h1 | h1
  · refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
      (hlow e (by rw [abs_of_nonneg he0]; exact h1))
    have : 0 ≤ a * e ^ 2 := by positivity
    linarith
  rcases le_or_gt (8 * ε₁) e with h8 | h8
  · rw [hdiv e (by rw [abs_of_nonneg he0]; exact h8)]
    exact le_top
  -- the log-convexity step on `[0, e]`
  set t := ε₁ / e with ht
  have hepos : 0 < e := lt_trans hε₁ h1
  have ht0 : 0 < t := div_pos hε₁ hepos
  have ht1 : t < 1 := (div_lt_one hepos).mpr h1
  have hconv := mgfExt_le_rpow_mul_rpow μ hX 0 e ht0 ht1
  have hpt : (1 - t) * 0 + t * e = ε₁ := by rw [ht]; field_simp; ring
  rw [hpt, mgfExt_zero, ENNReal.one_rpow, one_mul] at hconv
  have hlow1 := (hlow ε₁ (by rw [abs_of_pos hε₁])).trans hconv
  have hraise := ENNReal.rpow_le_rpow hlow1 (inv_pos.mpr ht0).le
  rw [ENNReal.rpow_rpow_inv ht0.ne', ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le
    (inv_pos.mpr ht0).le, ← Real.exp_mul] at hraise
  refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) hraise
  have hinv : a * ε₁ ^ 2 * t⁻¹ = a * ε₁ * e := by rw [ht]; field_simp
  rw [hinv]
  have hle : e / 8 ≤ ε₁ := by linarith
  have : a / 8 * e ^ 2 = a * (e / 8) * e := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle ha) he0

end FroehlichSpencer.BKT.SOS.Literal

end
