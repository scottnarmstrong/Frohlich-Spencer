/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.WithDensity
public import FroehlichSpencer.BKT.Surface.MultigraphSimpleGraph

/-! # The integer-valued discrete Gaussian free field -/

open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.BKT

universe u v

/-- The integer-valued discrete Gaussian free field `μ^IV_{β,Λ,v}` (KP p. 3) on a finite connected
multigraph `G` at inverse temperature `β > 0`, normalized to equal `0` at `v`: the measure on
`m : V → ℤ` with density `exp (-(β / 2) ∑_{j ∼ ℓ} (m j - m ℓ)²)` (each edge counted once) with
respect to `δ₀(m v) ∏_{j ≠ v} count(m j)`, divided by its total mass `Z^IV_{β,Λ,v}`. -/
noncomputable def integerGFFLaw {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (_hG : G.toSimpleGraph.Connected) (β : ℝ)
    (_hβ : 0 < β) (v : V) : Measure (V → ℤ) :=
  let μ : Measure (V → ℤ) :=
    (Measure.pi fun j => if j = v then Measure.dirac 0 else Measure.count).withDensity
      fun m => ENNReal.ofReal (Real.exp (-(β / 2) * ∑ e, ((m (G.src e) : ℝ) - m (G.tgt e)) ^ 2))
  (μ Set.univ)⁻¹ • μ

end FroehlichSpencer.BKT

end
