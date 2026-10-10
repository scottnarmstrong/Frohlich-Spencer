/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.StripWeight
public import FroehlichSpencer.BKT.Generic.LocalFactor

/-!
# Compact-periodic analytic edge weights

The clock field in FS81 §7.1 takes values in a compact angle interval.

Its edge weight is periodic
and positive, so it cannot satisfy the real-line tail majorant in `Generic.IsStripWeight`.

This
interface records the analytic and quantitative properties needed for a compact-angle contour
argument: period, nonvanishing, a complex-shift ratio cost, logarithmic-derivative bounds, and
boundedness on compact fundamental rectangles.

It intentionally does not assert a contour-shift
theorem or a probability law.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Periodic

open Complex

/-- A positive analytic edge weight on a compact angle with period `P`.

The shift cost bounds the ratio `w(t + iu) / w(t)`. `M₁` and `M₂` bound the first two logarithmic
derivatives at translated real points. The compact-rectangle bound replaces the real-line decay
majorant used by `Generic.IsStripWeight`; it is the appropriate boundedness condition for a finite
angle contour. -/
structure IsCompactPeriodicWeight (w : ℂ → ℂ) (P : ℝ) (c M₁ M₂ : ℝ → ℝ) : Prop where
  period_pos : 0 < P
  periodic : ∀ z : ℂ, w (z + (P : ℂ)) = w z
  analyticAt : ∀ z : ℂ, AnalyticAt ℂ w z
  nonzero : ∀ z : ℂ, w z ≠ 0
  even : ∀ z : ℂ, w (-z) = w z
  conj : ∀ z : ℂ, (starRingEnd ℂ) (w z) = w ((starRingEnd ℂ) z)
  ofReal_im : ∀ t : ℝ, (w t).im = 0
  ofReal_re_pos : ∀ t : ℝ, 0 < (w t).re
  ratio_le : ∀ t u : ℝ,
    ‖w ((t : ℂ) + (u : ℂ) * I) / w t‖ ≤ Real.exp (c u)
  cost_nonneg : ∀ u, 0 ≤ c u
  cost_even : ∀ u, c (-u) = c u
  cost_zero : c 0 = 0
  logDeriv_le : ∀ t u : ℝ,
    ‖logDeriv w ((t : ℂ) + (u : ℂ) * I)‖ ≤ M₁ u
  deriv_logDeriv_le : ∀ t u : ℝ,
    ‖deriv (logDeriv w) ((t : ℂ) + (u : ℂ) * I)‖ ≤ M₂ u
  M₁_nonneg : ∀ u, 0 ≤ M₁ u
  M₂_nonneg : ∀ u, 0 ≤ M₂ u
  compact_rect_bound : ∀ A : ℝ, 0 ≤ A → ∃ B : ℝ, 0 ≤ B ∧
    ∀ t u : ℝ, |t| ≤ P / 2 → |u| ≤ A →
      ‖w ((t : ℂ) + (u : ℂ) * I)‖ ≤ B

namespace IsCompactPeriodicWeight

variable {w : ℂ → ℂ} {P : ℝ} {c M₁ M₂ : ℝ → ℝ}

/-- The pointwise logarithmic-derivative estimates imply the difference bounds consumed by the
generic real-line Taylor interface. -/
theorem toHasLogDerivBounds (hw : IsCompactPeriodicWeight w P c M₁ M₂) (W : ℝ) :
    Generic.HasLogDerivBounds w W (fun u => M₁ u + M₁ 0 + M₂ u + M₂ 0) := by
  constructor
  · intro t u _
    calc
      ‖logDeriv w ((t : ℂ) + (u : ℂ) * I) - logDeriv w t‖ ≤
          ‖logDeriv w ((t : ℂ) + (u : ℂ) * I)‖ + ‖logDeriv w t‖ := norm_sub_le _ _
      _ ≤ M₁ u + M₁ 0 := by
        refine add_le_add (hw.logDeriv_le t u) ?_
        simpa using hw.logDeriv_le t 0
      _ ≤ M₁ u + M₁ 0 + M₂ u + M₂ 0 := by
        nlinarith [hw.M₂_nonneg u, hw.M₂_nonneg 0]
  · intro t u _
    calc
      ‖deriv (logDeriv w) ((t : ℂ) + (u : ℂ) * I) - deriv (logDeriv w) t‖ ≤
          ‖deriv (logDeriv w) ((t : ℂ) + (u : ℂ) * I)‖ + ‖deriv (logDeriv w) t‖ :=
            norm_sub_le _ _
      _ ≤ M₂ u + M₂ 0 := by
        refine add_le_add (hw.deriv_logDeriv_le t u) ?_
        simpa using hw.deriv_logDeriv_le t 0
      _ ≤ M₁ u + M₁ 0 + M₂ u + M₂ 0 := by
        nlinarith [hw.M₁_nonneg u, hw.M₁_nonneg 0]

/-- The complex local factor has norm at most one whenever the translated edge shifts stay within
the requested contour range. This is the generic FS81 (6.21) estimate and uses only the periodic
weight's ratio bound. -/
theorem norm_localFactor_le_one (hw : IsCompactPeriodicWeight w P c M₁ M₂)
    {E : Type*} [Fintype E] {W : ℝ} (b x : E → ℝ) (hb : ∀ e, |b e| ≤ W) (θ : ℝ) :
    ‖Generic.localFactor w c b x θ‖ ≤ 1 :=
  Generic.norm_localFactor_le_one (fun t u _ => hw.ratio_le t u) b x hb θ

/-- The generic local factor is real for a compact-periodic weight. -/
theorem localFactor_im_eq_zero (hw : IsCompactPeriodicWeight w P c M₁ M₂)
    {E : Type*} [Fintype E] {W : ℝ} (b x : E → ℝ) (hb : ∀ e, |b e| ≤ W) (θ : ℝ) :
    (Generic.localFactor w c b x θ).im = 0 :=
  Generic.localFactor_im_eq_zero (fun z _ => hw.conj z) hw.cost_even b x hb θ

/-- The local-factor parity used by the generic marked comparison. -/
theorem localFactor_neg (hw : IsCompactPeriodicWeight w P c M₁ M₂)
    {E : Type*} [Fintype E] {W : ℝ} (b x : E → ℝ) (hb : ∀ e, |b e| ≤ W) (θ : ℝ) :
    Generic.localFactor w c b (-x) (-θ) = Generic.localFactor w c b x θ :=
  Generic.localFactor_neg (fun z _ => hw.even z) hw.cost_even b x hb θ

end IsCompactPeriodicWeight

end FroehlichSpencer.BKT.Clock.Periodic

end
