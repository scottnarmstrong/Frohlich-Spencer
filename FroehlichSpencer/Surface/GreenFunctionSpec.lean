/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Surface.GreenFunction

/-! # Characterization of the infinite-volume Green function -/

public section

namespace FroehlichSpencer

/-- The Green function is the unique square-summable solution of the pointwise
lattice equation with source at y. -/
theorem greenFunction_spec (ν : ℕ) (hν : 0 < ν) (z : ℂ) (hz : z.im ≠ 0)
    (v : Site ν → ℝ) (y : Site ν) :
    ∀ ψ : Site ν → ℂ,
      (Summable (fun x => ‖ψ x‖ ^ 2) ∧
        ∀ x, -(latticeLaplacian ν ψ x) + ((v x : ℂ) - z) * ψ x =
          if x = y then 1 else 0) ↔
      ψ = fun x => greenFunction ν hν z hz v x y := by
  intro ψ
  let hsol := existsUnique_squareSummable_greenSolution ν hν z hz v y
  have hG :
      Summable (fun x => ‖(fun x => greenFunction ν hν z hz v x y) x‖ ^ 2) ∧
        ∀ x,
          -(latticeLaplacian ν (fun x => greenFunction ν hν z hz v x y) x) +
              ((v x : ℂ) - z) * (fun x => greenFunction ν hν z hz v x y) x =
            if x = y then 1 else 0 := by
    simpa [greenFunction, hsol] using Classical.choose_spec hsol.exists
  constructor
  · intro hψ
    simpa [greenFunction] using hsol.unique hψ hG
  · intro hEq
    rw [hEq]
    exact hG

end FroehlichSpencer

end
