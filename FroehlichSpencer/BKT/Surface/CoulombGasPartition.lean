/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import FroehlichSpencer.BKT.Surface.CoulombGasSummable

/-! # The partition function of a lattice Coulomb gas with free boundary conditions -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The partition function `Z_Λ = ∑_{q_Λ} exp[-β E(q_Λ)] ∏_{j ∈ Λ} λ(q(j))` (FS81 (1.8), J p. 530)
of the Coulomb gas with a priori weights `λ` in a finite region `Λ ⊂ ℤ²` with free boundary
conditions: the sum of the weights `coulombGasWeight β λ Λ` over the charge configurations
`q : Λ → ℤ`, on the domain `IsCoulombGasSummable β λ`, where the series converges. -/
noncomputable def coulombGasPartition (β : ℝ) (lam : ℤ → ℝ) (_hS : IsCoulombGasSummable β lam)
    (Λ : Finset (ℤ × ℤ)) : ℝ :=
  ∑' q : Λ → ℤ, coulombGasWeight β lam Λ q

end FroehlichSpencer.BKT

end
