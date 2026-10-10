/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.PrimalInterface.PerimeterLiteral

/-! Provider of the perimeter root `fs82WilsonLoopPerimeterLawCube`. -/

public section

namespace FroehlichSpencer.FS82.Provider

theorem fs82WilsonLoopPerimeterLawCube :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ (β : ℝ) (hβ : 0 < β), β₀ ≤ β → ∃ d : ℝ, 0 ≤ d ∧
      ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ (N : ℕ) (hN : 0 < N), max L T + 1 ≤ N →
        (Surface.wilsonLoopExpectation (Surface.centredCube N hN) β hβ
          (Surface.rectangularLoop L T)).im = 0 ∧
        Real.exp (-(d * ((L : ℝ) + T))) ≤
          (Surface.wilsonLoopExpectation (Surface.centredCube N hN) β hβ
            (Surface.rectangularLoop L T)).re :=
  PrimalInterface.fs82WilsonLoopPerimeterLawCube

end FroehlichSpencer.FS82.Provider

end
