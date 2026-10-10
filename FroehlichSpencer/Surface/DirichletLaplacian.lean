/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import FroehlichSpencer.Surface.Site

/-! # Dirichlet finite-difference Laplacian -/

public section

open scoped Matrix

namespace FroehlichSpencer

/-- The Dirichlet restriction of the lattice Laplacian to a finite set. -/
@[expose] noncomputable def dirichletLaplacian (ν : ℕ) (Λ : Finset (Site ν)) :
    Matrix {x : Site ν // x ∈ Λ} {x : Site ν // x ∈ Λ} ℂ := by
  classical
  let forward : Matrix {x : Site ν // x ∈ Λ} {x : Site ν // x ∈ Λ} ℂ := fun x y =>
    ∑ k : Fin ν, if y.1 = x.1 + Pi.single k (1 : ℤ) then 1 else 0
  exact
    forward + forwardᴴ - ((2 * ν : ℕ) : ℂ) •
      (1 : Matrix {x : Site ν // x ∈ Λ} {x : Site ν // x ∈ Λ} ℂ)

end FroehlichSpencer


end
