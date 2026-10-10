/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Sum
public import FroehlichSpencer.BKT.Surface.SquareZero

/-! # The solid-on-solid model in a square box with Dirichlet boundary conditions -/

open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.BKT

/--
The solid-on-solid model in the box `Λ = {0, …, L - 1}²` with Dirichlet boundary conditions
`φ = 0` off `Λ` (FS81 §7.2, J p. 590: "(The results and proofs which follow could be extended to
Dirichlet and periodic b.c., as well.)").

It is FS81's state (7.16) for the region `A = Λ` in the
zero-exterior measure `dμ_{I_β,Λ}`: the comb `∏_{j ∈ Λ}[1 + 2 ∑_{q ≥ 1} cos (2πq φ(j))]` makes every
height an integer, and on integers `I_β(n) = e^{-β|n|}` (condition (a)).

So it is the measure on
integer heights `n : Fin L × Fin L → ℤ` giving `n` the mass
`∏_e exp (-β |n(src e) - n(tgt e)|)`, divided by the total mass: the product runs over the edges
of the wired box `squareZero L` (each nearest-neighbour pair `|i - j| = 1`, `i ∈ Λ`, once),
and the wired vertex `none` carries the height `0`.
-/
noncomputable def sosDirichletLaw (L : ℕ) (β : ℝ) (_hβ : 0 < β) : Measure (Fin L × Fin L → ℤ) :=
  let μ : Measure (Fin L × Fin L → ℤ) := Measure.sum fun n : Fin L × Fin L → ℤ =>
    ENNReal.ofReal (∏ e, Real.exp (-(β * |((((squareZero L).src e).elim 0 n -
      ((squareZero L).tgt e).elim 0 n : ℤ) : ℝ)|))) • Measure.dirac n
  (μ Set.univ)⁻¹ • μ

end FroehlichSpencer.BKT

end
