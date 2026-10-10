/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Energy.CostEnvelope
public import FroehlichSpencer.BKT.Generic.Instances.SOS
public import FroehlichSpencer.BKT.Generic.StripWeightScaling
public import FroehlichSpencer.BKT.Generic.Renormalization.KPLayer

/-!
# SOS strip data and logarithmic activity for the KP layer

The Appendix C SOS interpolation supplies strip data for the generalized T1.6-NG theorem on KP's
free or even-periodic square domains. After rescaling the argument by `2π`, its cost has both
envelope coefficients equal to `C β^(2/3)`, where `C` is the interpolation constant. The activity
bound of the KP layer then yields the common exponent defined below. This is a KP-square conclusion;
it does not identify that finite carrier with FS81's whole-plane SOS reference law.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Star

open MeasureTheory Complex
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.SOS.Interp
open FroehlichSpencer.BKT.Rotator.Contour

/-- The Appendix C constant chosen from its proved strip-weight instance. -/
def interpolationCostConstant : ℝ := Classical.choose exists_isStripWeight_sosInterp + 1

theorem interpolationCostConstant_spec :
    0 ≤ interpolationCostConstant ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        IsStripWeight (sosInterp β) ((1 / 2 : ℝ) * β ^ (-(1 / 3 : ℝ)))
          (fun u => β ^ (2 / 3 : ℝ) * cEnvelope interpolationCostConstant u) :=
  by
    let C₀ := Classical.choose exists_isStripWeight_sosInterp
    have hC₀ : 0 ≤ C₀ := (Classical.choose_spec exists_isStripWeight_sosInterp).1
    refine ⟨by dsimp [interpolationCostConstant]; linarith, ?_⟩
    intro β hβ hβ1
    have hbase := (Classical.choose_spec exists_isStripWeight_sosInterp).2 β hβ hβ1
    have hmono (u : ℝ) : cEnvelope C₀ u ≤
        cEnvelope interpolationCostConstant u := by
      unfold cEnvelope
      dsimp [interpolationCostConstant, C₀]
      split_ifs
      · exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      · exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    refine ⟨hbase.width_nonneg, hbase.ofReal_im, hbase.ofReal_re_pos,
      hbase.analyticAt, hbase.even, hbase.conj, ?_, hbase.bounded, hbase.majorant, ?_, ?_⟩
    · intro t u hu
      calc
        ‖sosInterp β ((t : ℂ) + (u : ℂ) * I) / sosInterp β t‖ ≤
            Real.exp (β ^ (2 / 3 : ℝ) * cEnvelope C₀ u) := hbase.ratio_le t u hu
        _ ≤ Real.exp (β ^ (2 / 3 : ℝ) * cEnvelope interpolationCostConstant u) :=
          Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (hmono u) (Real.rpow_nonneg hβ.le _))
    · intro u
      simp [cEnvelope_neg]
    · simp [cEnvelope]

private lemma period_pos : 0 < 2 * Real.pi := by positivity

private lemma period_ge_one : 1 ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]

/-- The Appendix C weight, expressed in the integer-frequency convention. -/
theorem sosScaled_isStripWeight {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    IsStripWeight (fun z => sosInterp β (z / ((2 * Real.pi : ℝ) : ℂ)))
      ((2 * Real.pi) * ((1 / 2 : ℝ) * β ^ (-(1 / 3 : ℝ))))
      (fun u => β ^ (2 / 3 : ℝ) *
        cEnvelope interpolationCostConstant (u / (2 * Real.pi))) := by
  have hbase := interpolationCostConstant_spec.2 β hβ hβ1
  have hscaled := IsStripWeight.comp_div hbase period_pos
  change IsStripWeight (fun z => sosInterp β (z / ((2 * Real.pi : ℝ) : ℂ)))
    ((2 * Real.pi) * ((1 / 2 : ℝ) * β ^ (-(1 / 3 : ℝ))))
    (fun u => β ^ (2 / 3 : ℝ) *
      cEnvelope interpolationCostConstant (u / (2 * Real.pi)))
  exact hscaled

/-- The rescaled Appendix C cost has the two-branch envelope required by T1.6-NG. -/
theorem sosScaled_costEnvelope {β : ℝ} (hβ : 0 ≤ β) (W : ℝ) :
    IsCostEnvelope
      (fun u => β ^ (2 / 3 : ℝ) *
        cEnvelope interpolationCostConstant (u / (2 * Real.pi)))
      (interpolationCostConstant * β ^ (2 / 3 : ℝ))
      (interpolationCostConstant * β ^ (2 / 3 : ℝ)) W := by
  let C := interpolationCostConstant
  let b := β ^ (2 / 3 : ℝ)
  have hC : 0 ≤ C := interpolationCostConstant_spec.1
  have hb : 0 ≤ b := Real.rpow_nonneg hβ _
  have hp : 1 ≤ 2 * Real.pi := period_ge_one
  have hp0 : 0 < 2 * Real.pi := period_pos
  have hratio (u : ℝ) : |u / (2 * Real.pi)| ≤ |u| := by
    rw [abs_div, abs_of_pos hp0]
    exact div_le_self (abs_nonneg _) hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [neg_div, cEnvelope_neg]
  · simp [cEnvelope]
  · exact mul_nonneg hC hb
  · exact mul_nonneg hC hb
  · intro u hu
    change b * cEnvelope C (u / (2 * Real.pi)) ≤ (C * b) * u ^ 2
    have hs : |u / (2 * Real.pi)| ≤ 1 := (hratio u).trans hu
    rw [cEnvelope, ite_eq_left hs]
    have hsq : (u / (2 * Real.pi)) ^ 2 ≤ u ^ 2 := by
      calc
        (u / (2 * Real.pi)) ^ 2 = |u / (2 * Real.pi)| ^ 2 := (sq_abs _).symm
        _ ≤ |u| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hratio u) 2
        _ = u ^ 2 := sq_abs _
    calc
      b * (C * (u / (2 * Real.pi)) ^ 2) ≤ b * (C * u ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hC) hb
      _ = (C * b) * u ^ 2 := by ring
  · intro u hu _huW
    change b * cEnvelope C (u / (2 * Real.pi)) ≤ (C * b) * Real.exp (2 * Real.pi * |u|)
    by_cases hs : |u / (2 * Real.pi)| ≤ 1
    · rw [cEnvelope, ite_eq_left hs]
      have hsq : (u / (2 * Real.pi)) ^ 2 ≤ 1 := by
        calc
          (u / (2 * Real.pi)) ^ 2 = |u / (2 * Real.pi)| ^ 2 := (sq_abs _).symm
          _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hs 2
          _ = 1 := by norm_num
      have he : 1 ≤ Real.exp (2 * Real.pi * |u|) :=
        Real.one_le_exp (by positivity)
      calc
        b * (C * (u / (2 * Real.pi)) ^ 2) ≤ b * C := by
          calc
            b * (C * (u / (2 * Real.pi)) ^ 2) ≤ b * (C * 1) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hC) hb
            _ = b * C := by ring
        _ ≤ (C * b) * Real.exp (2 * Real.pi * |u|) := by
          calc
            b * C = (C * b) * 1 := by ring
            _ ≤ (C * b) * Real.exp (2 * Real.pi * |u|) :=
              mul_le_mul_of_nonneg_left he (mul_nonneg hC hb)
    · rw [cEnvelope, ite_eq_right hs]
      have harg : 2 * Real.pi * |u / (2 * Real.pi)| ≤ 2 * Real.pi * |u| :=
        mul_le_mul_of_nonneg_left (hratio u) (by positivity)
      calc
        b * (C * Real.exp (2 * Real.pi * |u / (2 * Real.pi)|)) =
            (C * b) * Real.exp (2 * Real.pi * |u / (2 * Real.pi)|) := by ring
        _ ≤ (C * b) * Real.exp (2 * Real.pi * |u|) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (mul_nonneg hC hb)

/-- Common activity exponent after absorbing the KP cover factor and site-mixture entropy. -/
def sosActivityRate (D₁ a₁ amp : ℝ) : ℝ :=
  amp / (8 * max 1 D₁) - max 200 a₁

/-- The T1.6-NG activity bound gives one exponential rate in charge mass and cover cost, provided
the finite site-mixture product is bounded by its entropy exponential. -/
theorem absorb_kp_activity_rate {D₁ a₁ amp A M Z z : ℝ}
    (hD₁ : 0 < D₁) (_ha₁ : 0 ≤ a₁) (hamp : 0 ≤ amp)
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hz : |z| ≤ Real.exp (200 * A) * Z *
      Real.exp (-(amp / 8 * M) - amp / (8 * D₁) * A))
    (hZ : Z ≤ Real.exp (a₁ * M)) :
    |z| ≤ Real.exp (-sosActivityRate D₁ a₁ amp * M) *
      Real.exp (-sosActivityRate D₁ a₁ amp * A) := by
  have hDmax : D₁ ≤ max 1 D₁ := le_max_right _ _
  have hOne : 1 ≤ max 1 D₁ := le_max_left _ _
  have hdenM : 0 < 8 * max 1 D₁ := by positivity
  have hdenA : 0 < 8 * D₁ := by positivity
  have hfacM : 1 / (8 * max 1 D₁) ≤ 1 / 8 := by
    apply (div_le_div_iff₀ hdenM (by norm_num : (0 : ℝ) < 8)).2
    nlinarith
  have hfacA : 1 / (8 * max 1 D₁) ≤ 1 / (8 * D₁) := by
    apply (div_le_div_iff₀ hdenM hdenA).2
    nlinarith
  have hcoefM : sosActivityRate D₁ a₁ amp ≤ amp / 8 - a₁ := by
    unfold sosActivityRate
    have hdiv : amp / (8 * max 1 D₁) = amp * (1 / (8 * max 1 D₁)) := by ring
    have hdiv8 : amp / 8 = amp * (1 / 8) := by ring
    rw [hdiv, hdiv8]
    have hm := mul_le_mul_of_nonneg_left hfacM hamp
    have ha := le_max_right (200 : ℝ) a₁
    nlinarith
  have hcoefA : sosActivityRate D₁ a₁ amp ≤ amp / (8 * D₁) - 200 := by
    unfold sosActivityRate
    have hdiv : amp / (8 * max 1 D₁) = amp * (1 / (8 * max 1 D₁)) := by ring
    have hdivD : amp / (8 * D₁) = amp * (1 / (8 * D₁)) := by ring
    rw [hdiv, hdivD]
    have hm := mul_le_mul_of_nonneg_left hfacA hamp
    have ha := le_max_left (200 : ℝ) a₁
    nlinarith
  have hmult : 0 ≤ Real.exp (200 * A) * Real.exp (-(amp / 8 * M) - amp / (8 * D₁) * A) :=
    mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
  have hz' : |z| ≤ Real.exp (200 * A) * Real.exp (a₁ * M) *
      Real.exp (-(amp / 8 * M) - amp / (8 * D₁) * A) := by
    calc
      |z| ≤ Real.exp (200 * A) * Z *
          Real.exp (-(amp / 8 * M) - amp / (8 * D₁) * A) := hz
      _ = (Real.exp (200 * A) *
          Real.exp (-(amp / 8 * M) - amp / (8 * D₁) * A)) * Z := by ring
      _ ≤ (Real.exp (200 * A) *
          Real.exp (-(amp / 8 * M) - amp / (8 * D₁) * A)) * Real.exp (a₁ * M) :=
        mul_le_mul_of_nonneg_left hZ hmult
      _ = _ := by ring
  have hcombine : Real.exp (200 * A) * Real.exp (a₁ * M) *
      Real.exp (-(amp / 8 * M) - amp / (8 * D₁) * A) =
      Real.exp ((200 * A + a₁ * M) + (-(amp / 8 * M) - amp / (8 * D₁) * A)) := by
    rw [← Real.exp_add, ← Real.exp_add]
  calc
    |z| ≤ Real.exp ((200 * A + a₁ * M) +
        (-(amp / 8 * M) - amp / (8 * D₁) * A)) := hz'.trans_eq hcombine
    _ ≤ Real.exp (-sosActivityRate D₁ a₁ amp * M +
        -sosActivityRate D₁ a₁ amp * A) := by
          apply Real.exp_le_exp.mpr
          have hm := mul_le_mul_of_nonneg_right
            (show a₁ - amp / 8 ≤ -sosActivityRate D₁ a₁ amp by linarith [hcoefM]) hM
          have hA' := mul_le_mul_of_nonneg_right
            (show 200 - amp / (8 * D₁) ≤ -sosActivityRate D₁ a₁ amp by linarith [hcoefA]) hA
          nlinarith [hm, hA']
    _ = Real.exp (-sosActivityRate D₁ a₁ amp * M) *
        Real.exp (-sosActivityRate D₁ a₁ amp * A) := by rw [Real.exp_add]

/-- If `T=log(1/β)` dominates the fixed cover and mixture losses, the retained T1.6 exponent is
bounded below by a positive multiple of `T`. -/
theorem sos_activity_rate_ge_log {T D₁ a₁ : ℝ} (_hD₁ : 0 < D₁) (_ha₁ : 0 ≤ a₁)
    (hT : 448000 * max 1 D₁ * max 200 a₁ ≤ T) :
    T / (448000 * max 1 D₁) ≤ sosActivityRate D₁ a₁ (T / 28000) := by
  let m := max 1 D₁
  let q := max 200 a₁
  have hm : 1 ≤ m := le_max_left _ _
  have hq : 0 ≤ q := le_trans (by norm_num) (le_max_left _ _)
  have hden : 0 < 448000 * m := by positivity
  have hqle : q ≤ T / (448000 * m) := by
    apply (le_div_iff₀ hden).2
    dsimp [m, q] at hT ⊢
    nlinarith [hT]
  unfold sosActivityRate
  have hfirst : (T / 28000) / (8 * m) = T / (224000 * m) := by ring
  rw [hfirst]
  have hdouble : T / (224000 * m) =
      T / (448000 * m) + T / (448000 * m) := by ring
  rw [hdouble]
  dsimp [q] at hqle
  linarith

end FroehlichSpencer.BKT.SOS.Star

end
