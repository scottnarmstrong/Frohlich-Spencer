/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import FroehlichSpencer.BKT.Surface.CoulombGasPartition

/-! # The fractional-charge correlation of a lattice Coulomb gas -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- FS81 (1.23) (J p. 532) for the Coulomb gas with a priori weights `λ`: the correlation of two
opposite fractional charges `±ξ` at the sites `a, b` of a finite region `Λ ⊂ ℤ²` with free
boundary conditions (J p. 529 (i)),
`G_{ξ,Λ}(a, b) = Z_Λ⁻¹ ∑_{q_Λ} exp[-β E(q_Λ + ξ(δ_a - δ_b))] ∏_{j ∈ Λ} λ(q(j))`. The sum runs over
the charge configurations `q : Λ → ℤ` of total charge `0` ((1.14), as in `coulombGasWeight`), `E` is
(1.4) with `C = coulombPotential`, and `Z_Λ` is (1.8) (`coulombGasPartition`). It is defined for a
positive measure `dλ` (1.6), `λ ≥ 0`, with a vacancy `λ(0) > 0`, so that
`Z_Λ > 0` (`coulombGasPartition_pos`), and on the domain `IsCoulombGasSummable β λ`, where both
series converge. The positive vacancy assumption is implicit in the printed argument. -/
noncomputable def conditionLambdaFracCorrelation (β : ℝ) (lam : ℤ → ℝ) (_hlam : ∀ q, 0 ≤ lam q)
    (_hlam0 : 0 < lam 0) (hS : IsCoulombGasSummable β lam) (ξ : ℝ) (Λ : Finset (ℤ × ℤ))
    (a b : Λ) : ℝ :=
  let E : (Λ → ℝ) → ℝ := fun ρ =>
    (∑ i, ∑ j, ρ i * ρ j * coulombPotential ((i : ℤ × ℤ) - j)) / 2
  let f : Λ → ℝ := fun j => (if j = a then ξ else 0) - (if j = b then ξ else 0)
  (∑' q : Λ → ℤ, (if ∑ j, q j = 0 then ∏ j, lam (q j) else 0) *
      Real.exp (-β * E (fun j => (q j : ℝ) + f j))) /
    coulombGasPartition β lam hS Λ

end FroehlichSpencer.BKT

end
