/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.Pi
public import FroehlichSpencer.BKT.Surface.CoulombPotential

/-! # The Boltzmann weights of a lattice Coulomb gas with free boundary conditions -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The weight of a charge configuration `q : Λ → ℤ` of the Coulomb gas with a priori weights `λ`
in a finite region `Λ ⊂ ℤ²` with free boundary conditions (FS81 J p. 529 (i)) at inverse
temperature `β`: the a priori weight `∏_{j ∈ Λ} λ(q(j))` (1.6) times the Boltzmann factor
`exp[-β E(q)]` (1.5), with the energy (1.4) `E(q) = ½ ∑_{i, j ∈ Λ} q(i) q(j) C(i - j)`,
`C = coulombPotential`, if the total charge `∑_j q(j)` is `0`, and `0` otherwise: with free
boundary conditions a configuration of nonzero total charge has infinite energy ((1.14), J p. 531).
(For `β ≤ 0` the restriction to neutral configurations is a convention of the formula's
extension; FS81's inverse temperature is `β > 0`.) -/
noncomputable def coulombGasWeight (β : ℝ) (lam : ℤ → ℝ) (Λ : Finset (ℤ × ℤ)) (q : Λ → ℤ) : ℝ :=
  if ∑ j, q j = 0 then
    (∏ j, lam (q j)) *
      Real.exp (-β * ((∑ i, ∑ j, (q i : ℝ) * (q j : ℝ) * coulombPotential ((i : ℤ × ℤ) - j)) / 2))
  else 0

end FroehlichSpencer.BKT

end
