/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Periodic.Weight
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Compact-periodic contour shifts

For an entire function with real period `P`, integration over a fundamental interval is unchanged
when the interval is shifted vertically. The vertical sides of the Cauchy rectangle cancel by
periodicity; this replaces the real-line tail argument in the generic edge-law translation.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Periodic

open MeasureTheory
open scoped Interval

/-- A one-variable contour shift on one compact fundamental interval. The two vertical sides of
the rectangle cancel because `f` is `P`-periodic. -/
theorem periodic_intervalIntegral_shift {P t : ℝ} (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hper : ∀ z : ℂ, f (z + (P : ℂ)) = f z) :
    ∫ x in (-P / 2)..(P / 2), f (x : ℂ) =
      ∫ x in (-P / 2)..(P / 2), f ((x : ℂ) + (t : ℂ) * Complex.I) := by
  let a : ℝ := -P / 2
  let b : ℝ := P / 2
  have hab : b - a = P := by dsimp [a, b]; ring
  have hrect := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f (a : ℂ) ((b : ℂ) + (t : ℂ) * Complex.I) ?_ ?_
  · have hside : (∫ y in (0 : ℝ)..t, f ((b : ℂ) + (y : ℂ) * Complex.I)) =
        ∫ y in (0 : ℝ)..t, f ((a : ℂ) + (y : ℂ) * Complex.I) := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hz : (a : ℂ) + (y : ℂ) * Complex.I + (P : ℂ) =
          (b : ℂ) + (y : ℂ) * Complex.I := by
        rw [← hab]
        push_cast
        ring
      have hh := congrArg f hz
      rw [hper] at hh
      simpa only [Complex.I] using hh.symm
    have haR : (a : ℂ).re = a := by simp
    have haI : (a : ℂ).im = 0 := by simp
    have hbR : ((b : ℂ) + (t : ℂ) * Complex.I).re = b := by simp
    have hbI : ((b : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [haR, haI, hbR, hbI] at hrect
    have hrect' :
        (∫ x in a..b, f (x : ℂ)) -
          (∫ x in a..b, f ((x : ℂ) + (t : ℂ) * Complex.I)) +
          Complex.I • (∫ y in (0 : ℝ)..t, f ((b : ℂ) + (y : ℂ) * Complex.I)) -
          Complex.I • (∫ y in (0 : ℝ)..t, f ((a : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
      simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hrect
    rw [hside] at hrect'
    have hrect'' : (∫ x in a..b, f (x : ℂ)) -
        (∫ x in a..b, f ((x : ℂ) + (t : ℂ) * Complex.I)) = 0 := by
      linear_combination hrect'
    have hbottom : (∫ x in a..b, f (x : ℂ)) =
        ∫ x in (-P / 2)..(P / 2), f (x : ℂ) := by simp [a, b]
    have htop : (∫ x in a..b, f ((x : ℂ) + (t : ℂ) * Complex.I)) =
        ∫ x in (-P / 2)..(P / 2), f ((x : ℂ) + (t : ℂ) * Complex.I) := by simp [a, b]
    rw [hbottom, htop] at hrect''
    exact (sub_eq_zero.mp hrect'')
  · exact hf.continuous.continuousOn
  · exact hf.differentiableOn

end FroehlichSpencer.BKT.Clock.Periodic

end
