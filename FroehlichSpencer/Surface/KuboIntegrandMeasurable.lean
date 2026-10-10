/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Surface.GreenFunctionMeasurable
public import FroehlichSpencer.Surface.KuboQuantity
import Mathlib.Tactic

/-! # Measurability of the Kubo integrand -/

public section

open MeasureTheory

namespace FroehlichSpencer

/-- The nonnegative Green-function integrand in (1.15) is measurable; this is
proved from W1 and is not an input to the Kubo definition. -/
theorem measurable_kubo_integrand (ν : ℕ) (hν : 0 < ν) (E : ℝ)
    (ε : {ε : ℝ // ε ≠ 0}) (x : Site ν) :
    Measurable fun v : Configuration ν =>
      ENNReal.ofReal
        (‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
          (by simpa using ε.2) v 0 x‖ ^ 2) := by
  fun_prop (disch := norm_num)

end FroehlichSpencer

end
