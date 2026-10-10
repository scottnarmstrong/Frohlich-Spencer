/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.AreaLawActivity
public import FroehlichSpencer.FS82.Wilson.AreaLawSource

/-!
# Area extraction from source-constrained Gaussian weights

A source field has coordinate ℓ¹ mass at least the rectangle area. Splitting
the Gaussian weight then extracts an area factor and leaves a smaller
single-plaquette activity.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

theorem dualGaussianProduct_source_l1_bound {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (β : ℝ) (hβ : 0 < β)
    (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT)) :
    dualGaussianProduct β m ≤
      Real.exp (-((L * T : ℝ) / (8 * β))) *
        dualGaussianProduct (4 * β / 3) m := by
  have hmass := areaTestPotential_modeRealL1_lower_bound hL hT m hsource
  have harg :
      Real.exp (-((∑ p : PrimalPlaquettes B, |(m p : ℝ)|) / (8 * β))) ≤
        Real.exp (-((L * T : ℝ) / (8 * β))) := by
    apply Real.exp_le_exp.mpr
    have hdiv := div_le_div_of_nonneg_right hmass (by positivity : 0 ≤ 8 * β)
    linarith
  calc
    dualGaussianProduct β m ≤
        Real.exp (-((∑ p : PrimalPlaquettes B, |(m p : ℝ)|) / (8 * β))) *
          dualGaussianProduct (4 * β / 3) m :=
      dualGaussianProduct_le_residual_of_l1 β hβ m
    _ ≤ Real.exp (-((L * T : ℝ) / (8 * β))) *
          dualGaussianProduct (4 * β / 3) m :=
      mul_le_mul_of_nonneg_right harg
        (dualGaussianProduct_nonneg (4 * β / 3) m)

theorem dualGaussianProduct_source_small_beta_bound {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (β : ℝ) (hβ : 0 < β)
    (hsmall : β ≤ 1 / 80) (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT)) :
    dualGaussianProduct β m ≤
      Real.exp (-10 * (L * T : ℝ)) * dualGaussianProduct (4 * β / 3) m := by
  have hbound := dualGaussianProduct_source_l1_bound hL hT β hβ m hsource
  have hcoef : (10 : ℝ) ≤ 1 / (8 * β) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * β)).2
    nlinarith [hsmall]
  have harea : 0 ≤ (L * T : ℝ) := by positivity
  have hmul : 10 * (L * T : ℝ) ≤ (L * T : ℝ) / (8 * β) := by
    calc
      10 * (L * T : ℝ) ≤ (1 / (8 * β)) * (L * T : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef harea
      _ = (L * T : ℝ) / (8 * β) := by ring
  have harg :
      Real.exp (-((L * T : ℝ) / (8 * β))) ≤ Real.exp (-10 * (L * T : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  exact hbound.trans (mul_le_mul_of_nonneg_right harg
    (dualGaussianProduct_nonneg (4 * β / 3) m))

end FroehlichSpencer.FS82.Wilson

end
