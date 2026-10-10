/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.PrimalInterface.AreaLawLiteral

/-! Provider of the small-β area law root `fs82WilsonLoopAreaLawCube` on centred cubes. -/

public section

namespace FroehlichSpencer.FS82.Provider

theorem fs82WilsonLoopAreaLawCube :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ →
      ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ (N : ℕ) (hN : 0 < N), max L T + 1 ≤ N →
        (Surface.wilsonLoopExpectation (Surface.centredCube N hN) β hβ
          (Surface.rectangularLoop L T)).im = 0 ∧
        0 ≤ (Surface.wilsonLoopExpectation (Surface.centredCube N hN) β hβ
          (Surface.rectangularLoop L T)).re ∧
        (Surface.wilsonLoopExpectation (Surface.centredCube N hN) β hβ
          (Surface.rectangularLoop L T)).re ≤ Real.exp (-(c * ((L : ℝ) * T))) :=
  PrimalInterface.fs82WilsonLoopAreaLawCube

end FroehlichSpencer.FS82.Provider

end
