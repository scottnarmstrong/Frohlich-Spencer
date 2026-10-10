/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.CubeLoopField

/-!
# The loop field and the covariance of the plaquette-loop test

For a 2-form `σ` on a finite exact complex, the test 1-form `d₁† σ` (the restriction of `δσ`)
is co-closed and its quotient covariance is

`Q(d₁† σ) = ‖σ‖² - (ε, ε)`,

with `ε = loopFieldResidual C σ` (``, Proposition 4.1(c); the bridge of ``,
finding 3). For the Wilson sheet on a centred cube this gives
`L T - 6 (L + T) ≤ Q(δσ) ≤ L T`: the covariance of the sheet of plaquette loops is the area up
to a perimeter term.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Moment.SourceConstructor

section Residual

variable {V E P : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

/-- `d₁† σ` is co-closed. -/
theorem adjoint_mem_coClosed (C : ExactOneComplex V E P) (σ : EuclideanSpace ℝ P) :
    C.d₁.adjoint σ ∈ coClosed C := by
  apply LinearMap.mem_ker.mpr
  have hcomp : C.d₀.adjoint.comp C.d₁.adjoint = 0 := by
    rw [← LinearMap.adjoint_comp, C.complex]
    simp
  change (C.d₀.adjoint.comp C.d₁.adjoint) σ = 0
  rw [hcomp]
  simp

/-- `d₁† ε = 0`: the loop field is co-closed as a 2-form. -/
theorem adjoint_loopFieldResidual (C : ExactOneComplex V E P) (σ : EuclideanSpace ℝ P) :
    C.d₁.adjoint (loopFieldResidual C σ) = 0 := by
  refine ext_inner_right ℝ fun α => ?_
  rw [LinearMap.adjoint_inner_left, inner_zero_left]
  exact loopFieldResidual_inner_exact C σ α


end Residual


end FroehlichSpencer.FS82.Wilson

end
