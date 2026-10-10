/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import FroehlichSpencer.BKT.Surface.SquareZero

/-! # The plane rotator model with Villain interaction -/

open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The Villain model `μ^Vil_{β,Λ_L^zero}` (KP p. 4) on `Λ_L^zero` at inverse temperature
`β > 0`, normalized to equal `0` at the wired vertex `z = none`: the measure on
`θ : Option (Fin L × Fin L) → ℝ` with density
`∏_{j ∼ ℓ} ∑_{m ∈ ℤ} exp (-(β / 2) (θ j - θ ℓ + 2π m)²)` (product over the edges of `Λ_L^zero`,
with multiplicity) with respect to `δ₀(θ z) ∏_{j ≠ z} 𝟙_{[-π, π)}(θ j) dθ j`, divided by its
total mass `Z^Vil`. -/
noncomputable def villainLaw (L : ℕ) (β : ℝ) (_hβ : 0 < β) :
    Measure (Option (Fin L × Fin L) → ℝ) :=
  let μ : Measure (Option (Fin L × Fin L) → ℝ) :=
    (Measure.pi fun j =>
        if j = none then Measure.dirac 0
        else volume.restrict (Set.Ico (-Real.pi) Real.pi)).withDensity
      fun θ => ∏ e, ∑' m : ℤ,
        ENNReal.ofReal (Real.exp (-(β / 2) *
          (θ ((squareZero L).src e) - θ ((squareZero L).tgt e) + 2 * Real.pi * m) ^ 2))
  (μ Set.univ)⁻¹ • μ

end FroehlichSpencer.BKT

end
