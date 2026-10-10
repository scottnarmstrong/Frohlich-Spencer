/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # The Villain model in a finite region of `ℤ²` with free boundary conditions -/

open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The Villain state `⟨·⟩_Λ(β)` (FS81 (1.26) with the periodized Gaussian
`v_β(θ) = ∑_{m ∈ ℤ} exp (-(β/2) (θ + 2πm)²)`, (1.27), J p. 533) in a finite region `Λ ⊂ ℤ²` at
inverse temperature `β > 0`: the measure on angle configurations `θ : Λ → ℝ` with density
`∏_{(ij) ⊂ Λ} v_β(θ_i - θ_j)` with respect to `∏_{j ∈ Λ} 𝟙_{[-π, π)}(θ_j) dθ_j`, divided by its
total mass `Z_Λ`. The product runs over the nearest-neighbour pairs of `Λ` (free boundary
conditions), each listed once, as the ordered pair `(i, j)` with `j = i + (1, 0)` or
`j = i + (0, 1)`, exactly as in `planeRotatorLaw`. -/
noncomputable def freeVillainLaw (β : ℝ) (_hβ : 0 < β) (Λ : Finset (ℤ × ℤ)) : Measure (Λ → ℝ) :=
  let μ : Measure (Λ → ℝ) :=
    (Measure.pi fun _ : Λ => volume.restrict (Set.Ico (-Real.pi) Real.pi)).withDensity
      fun θ => ∏ b ∈ (Finset.univ : Finset (Λ × Λ)).filter (fun b : Λ × Λ =>
          (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨ (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1)),
        ∑' m : ℤ, ENNReal.ofReal (Real.exp (-(β / 2) * (θ b.1 - θ b.2 + 2 * Real.pi * m) ^ 2))
  (μ Set.univ)⁻¹ • μ

end FroehlichSpencer.BKT

end
