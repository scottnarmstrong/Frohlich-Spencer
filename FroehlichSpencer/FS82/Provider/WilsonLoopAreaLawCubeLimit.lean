/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.PrimalInterface.AreaLawLiteral

/-! Provider of the cube-limit form `fs82WilsonLoopAreaLawCubeLimit` of the small-β area law. -/

public section

namespace FroehlichSpencer.FS82.Provider

open Filter

theorem fs82WilsonLoopAreaLawCubeLimit :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ →
      ∀ L T : ℕ, 1 ≤ L → 1 ≤ T →
        (∃ x : ℝ, MapClusterPt x atTop (Surface.wilsonCubeSequence β hβ L T)) ∧
        (∀ x : ℝ, MapClusterPt x atTop (Surface.wilsonCubeSequence β hβ L T) →
          0 ≤ x ∧ x ≤ Real.exp (-(c * ((L : ℝ) * T)))) ∧
        Filter.limsup (Surface.wilsonCubeSequence β hβ L T) atTop ≤
          Real.exp (-(c * ((L : ℝ) * T))) ∧
        ∀ w : ℝ, Tendsto (Surface.wilsonCubeSequence β hβ L T) atTop (nhds w) →
          0 ≤ w ∧ w ≤ Real.exp (-(c * ((L : ℝ) * T))) :=
  PrimalInterface.fs82WilsonLoopAreaLawCubeLimit

end FroehlichSpencer.FS82.Provider

end
