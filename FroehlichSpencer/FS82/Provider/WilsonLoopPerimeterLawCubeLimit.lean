/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.PrimalInterface.PerimeterLiteral

/-! Provider of the cube-limit form `fs82WilsonLoopPerimeterLawCubeLimit` of the perimeter law. -/

public section

namespace FroehlichSpencer.FS82.Provider

open Filter

theorem fs82WilsonLoopPerimeterLawCubeLimit :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ (β : ℝ) (hβ : 0 < β), β₀ ≤ β → ∃ d : ℝ, 0 ≤ d ∧
      ∀ L T : ℕ, 1 ≤ L → 1 ≤ T →
        (∃ x : ℝ, MapClusterPt x atTop (Surface.wilsonCubeSequence β hβ L T)) ∧
        (∀ x : ℝ, MapClusterPt x atTop (Surface.wilsonCubeSequence β hβ L T) →
          Real.exp (-(d * ((L : ℝ) + T))) ≤ x) ∧
        Real.exp (-(d * ((L : ℝ) + T))) ≤
          Filter.liminf (Surface.wilsonCubeSequence β hβ L T) atTop ∧
        ∀ w : ℝ, Tendsto (Surface.wilsonCubeSequence β hβ L T) atTop (nhds w) →
          Real.exp (-(d * ((L : ℝ) + T))) ≤ w :=
  PrimalInterface.fs82WilsonLoopPerimeterLawCubeLimit

end FroehlichSpencer.FS82.Provider

end
