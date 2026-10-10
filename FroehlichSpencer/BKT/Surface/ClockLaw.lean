/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # The `ℤ_n` clock model in a finite region of `ℤ²` -/

open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The `ℤ_n` clock state `⟨·⟩_Λ^{(n)}(β)` (`n ≥ 1`) in a finite region `Λ ⊂ ℤ²` with free boundary
conditions (FS81 (7.1)–(7.2), J pp. 584–585): the measure on angle configurations `θ : Λ → ℝ` with
density `∏_{(ij) ⊂ Λ} exp (β cos (θ_i - θ_j))` with respect to
`∏_{j ∈ Λ} ∑_{k=0}^{n-1} δ_{2πk/n}(dθ_j)` (the angles `2πk/n` of the comb (7.2), each atom with unit
mass), divided by its total mass. The bonds are those of `planeRotatorLaw`: each nearest-neighbour
pair of `Λ` once, as `(i, j)` with `j = i + (1, 0)` or `j = i + (0, 1)`. For `β > 0` this is the
`h → ∞` limit of the finite-volume states of (1.39)–(1.40) (Remark 1, J p. 585). At `β = 0` the
field term `βh cos (nθ)` of (1.39) vanishes; the comb (7.2), which does not depend on `β`, is then
the chosen infinite-temperature clock state. For `β < 0` the formula is only an extension: the
`h → ∞` limit of (1.39) would select the angles `(2k + 1)π/n` instead. -/
noncomputable def clockLaw (n : ℕ) (_hn : 0 < n) (β : ℝ) (Λ : Finset (ℤ × ℤ)) :
    Measure (Λ → ℝ) :=
  let μ : Measure (Λ → ℝ) :=
    (Measure.pi fun _ : Λ => ∑ k : Fin n, Measure.dirac (2 * Real.pi * (k : ℝ) / n)).withDensity
      fun θ => ∏ b ∈ (Finset.univ : Finset (Λ × Λ)).filter (fun b : Λ × Λ =>
          (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨ (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1)),
        ENNReal.ofReal (Real.exp (β * Real.cos (θ b.1 - θ b.2)))
  (μ Set.univ)⁻¹ • μ

end FroehlichSpencer.BKT

end
