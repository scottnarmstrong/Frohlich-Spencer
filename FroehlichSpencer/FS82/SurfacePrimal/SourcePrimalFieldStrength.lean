/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.PrimalPlaquetteCurl
public import FroehlichSpencer.FS82.Surface.PrimalVillainLaw

@[expose] public section
open MeasureTheory Filter Topology
open FroehlichSpencer.FS82.Surface
namespace FroehlichSpencer.FS82.SurfaceInfinite

/-- FS82 (2.89): the Villain field strength on real link angles. -/
noncomputable def sourcePrimalFieldStrength (R : Surface.RectBox4) (β : ℝ)
    (_hβ : 0 < β) (θ : Surface.PrimalLinks R → ℝ)
    (p : Surface.PrimalPlaquettes R) : ℂ :=
  let φ : ℝ → ℝ := fun x => ∑' n : ℤ,
    Real.exp (-(β / 2) * (x + 2 * Real.pi * n) ^ 2)
  (-Complex.I) * ((deriv φ (Surface.primalPlaquetteCurl R θ p) : ℝ) : ℂ) /
    (φ (Surface.primalPlaquetteCurl R θ p) : ℂ)

end FroehlichSpencer.FS82.SurfaceInfinite
end
