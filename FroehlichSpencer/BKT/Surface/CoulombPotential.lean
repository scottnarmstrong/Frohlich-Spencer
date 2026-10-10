/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # The two-dimensional lattice Coulomb potential with free boundary conditions -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- FS81's Coulomb potential with free boundary conditions (J p. 529 (i)): `C(i, j) = C(i - j)`,
the Green's function of the finite difference Laplacian on `ℤ²`, normalized by `C(0) = 0`
(in two dimensions the Green's function is determined only up to an additive constant, which
does not enter the energy of a neutral charge distribution, (1.14), J p. 531):
`C(x) = -(2π)⁻² ∫_{[0, 2π)²} (1 - cos (k₁ x₁ + k₂ x₂)) / (2 (1 - cos k₁) + 2 (1 - cos k₂)) dk`,
minus the potential kernel of the square lattice. The integrand is bounded by `x₁² + x₂²`; its
value at the single point `k = 0`, where the denominator vanishes, does not affect the integral. -/
noncomputable def coulombPotential (x : ℤ × ℤ) : ℝ :=
  -(((2 * Real.pi) ^ 2)⁻¹ *
    ∫ k in Set.Ico 0 (2 * Real.pi) ×ˢ Set.Ico 0 (2 * Real.pi),
      (1 - Real.cos (k.1 * x.1 + k.2 * x.2)) /
        (2 * (1 - Real.cos k.1) + 2 * (1 - Real.cos k.2)))

end FroehlichSpencer.BKT

end
