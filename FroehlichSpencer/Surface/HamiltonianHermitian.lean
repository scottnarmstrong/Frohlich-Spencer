/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Surface.Hamiltonian

/-! # Hermitian property of finite-volume Hamiltonians -/

open scoped Matrix

public section

namespace FroehlichSpencer

theorem hamiltonian_isHermitian (ν : ℕ) (Λ : Finset (Site ν)) (v : Site ν → ℝ) :
    (hamiltonian ν Λ v).IsHermitian := by
  classical
  unfold hamiltonian dirichletLaplacian
  let forward : Matrix {x : Site ν // x ∈ Λ} {x : Site ν // x ∈ Λ} ℂ := fun x y =>
    ∑ k : Fin ν, if y.1 = x.1 + Pi.single k (1 : ℤ) then 1 else 0
  have hforward : (forward + forwardᴴ).IsHermitian := Matrix.isHermitian_add_transpose_self forward
  have hscalar :
      (((2 * ν : ℕ) : ℂ) •
        (1 : Matrix {x : Site ν // x ∈ Λ} {x : Site ν // x ∈ Λ} ℂ)).IsHermitian := by
    apply Matrix.IsHermitian.smul Matrix.isHermitian_one
    change star (((2 * ν : ℕ) : ℂ)) = ((2 * ν : ℕ) : ℂ)
    simp
  have hDelta :
      (forward + forwardᴴ - ((2 * ν : ℕ) : ℂ) •
        (1 : Matrix {x : Site ν // x ∈ Λ} {x : Site ν // x ∈ Λ} ℂ)).IsHermitian :=
    hforward.sub hscalar
  have hV : (Matrix.diagonal (fun x : {x : Site ν // x ∈ Λ} => (v x.1 : ℂ))).IsHermitian := by
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    funext x
    simp
  exact hDelta.neg.add hV

end FroehlichSpencer


end
