/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.CoulombPotential
import FroehlichSpencer.BKT.Coulomb.PotentialKernel

/-! # The lattice Coulomb potential is a Green's function of `-Δ` on `ℤ²` -/

public section

namespace FroehlichSpencer.BKT

/-- `coulombPotential` is a Green's function of the finite difference Laplacian on `ℤ²`
(FS81 J p. 529 (i)): `-Δ C = δ₀`, i.e.
`4 C(x) - C(x + (1, 0)) - C(x - (1, 0)) - C(x + (0, 1)) - C(x - (0, 1)) = 𝟙[x = 0]`, with the
normalization `C(0) = 0`. -/
theorem coulombPotential_laplacian :
    (∀ x : ℤ × ℤ, 4 * coulombPotential x - coulombPotential (x + (1, 0)) -
        coulombPotential (x - (1, 0)) - coulombPotential (x + (0, 1)) -
        coulombPotential (x - (0, 1)) = if x = 0 then 1 else 0) ∧
      coulombPotential 0 = 0 := by
  have hC : ∀ x, coulombPotential x = -Coulomb.potentialKernelInternal x := fun _ => rfl
  refine ⟨fun x => ?_, ?_⟩
  · simp only [hC]
    rw [← Coulomb.potentialKernel_laplacian x]
    ring
  · rw [hC, Coulomb.potentialKernel_zero, neg_zero]

end FroehlichSpencer.BKT

end
