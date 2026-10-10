/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import FroehlichSpencer.BKT.Surface.MultigraphSimpleGraph

/-! # The discrete Gaussian free field normalized to `[-π, π)` at a vertex -/

open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.BKT

universe u v

/-- The discrete Gaussian free field `μ^GFF_{β,Λ,v}` (KP (1.3), p. 2) on a finite connected
multigraph `G` at inverse temperature `β > 0`, normalized to take values in `[-π, π)` at `v`:
the measure on `φ : V → ℝ` with density
`exp (-(β / 2) ∑_{j ∼ ℓ} (φ j - φ ℓ)²) · 𝟙_{[-π, π)} (φ v)` (each edge counted once) with respect
to Lebesgue measure `∏ j, dφ j`, divided by its total mass `Z^GFF_{β,Λ,v}`. -/
noncomputable def gffLaw {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    (G : Multigraph V E) (_hG : G.toSimpleGraph.Connected) (β : ℝ) (_hβ : 0 < β) (v : V) :
    Measure (V → ℝ) :=
  let μ : Measure (V → ℝ) :=
    (Measure.pi fun _ : V => (volume : Measure ℝ)).withDensity fun φ =>
      ENNReal.ofReal (Real.exp (-(β / 2) * ∑ e, (φ (G.src e) - φ (G.tgt e)) ^ 2) *
        (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v))
  (μ Set.univ)⁻¹ • μ

end FroehlichSpencer.BKT

end
