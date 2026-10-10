/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Basic.Complex.Basic
public import FroehlichSpencer.Surface.Hamiltonian

/-! # Finite-volume Green function -/

open scoped Matrix

public section

namespace FroehlichSpencer

/-- The finite-volume Green entry, defined on its source domain `ε ≠ 0`. -/
@[expose] noncomputable def finiteGreen (ν : ℕ) (Λ : Finset (Site ν))
    (v : Site ν → ℝ) (E ε : ℝ) (_hε : ε ≠ 0)
    (x y : {x : Site ν // x ∈ Λ}) : ℂ :=
  ((hamiltonian ν Λ v - ((E : ℂ) + (ε : ℂ) * Complex.I) •
      (1 : Matrix {x : Site ν // x ∈ Λ} {x : Site ν // x ∈ Λ} ℂ))⁻¹) x y

end FroehlichSpencer


end
