/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.RectBox4
public import FroehlichSpencer.FS82.Surface.LatticeCoord
public import FroehlichSpencer.FS82.Surface.LatticeCell
public import FroehlichSpencer.FS82.Surface.LatticeChain
public import FroehlichSpencer.FS82.Surface.LatticeIsEdge
public import FroehlichSpencer.FS82.Surface.LatticeRankBefore
public import FroehlichSpencer.FS82.Surface.LatticeBasis
public import FroehlichSpencer.FS82.Surface.LatticeUpperFace
public import FroehlichSpencer.FS82.Surface.LatticeLowerFace
public import FroehlichSpencer.FS82.Surface.LatticeBoundaryBasis
public import FroehlichSpencer.FS82.Surface.PrimalCoord
public import FroehlichSpencer.FS82.Surface.PrimalCell
public import FroehlichSpencer.FS82.Surface.PrimalCellDegree
public import FroehlichSpencer.FS82.Surface.PrimalLinks
public import FroehlichSpencer.FS82.Surface.PrimalLinksFintype
public import FroehlichSpencer.FS82.Surface.PrimalPlaquettes
public import FroehlichSpencer.FS82.Surface.PrimalPlaquettesFintype
public import FroehlichSpencer.FS82.Surface.PrimalCellEmbedding
public import FroehlichSpencer.FS82.Surface.PrimalPlaquetteCurl

/-! FS82 perimeter surface definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

/-- FS82 (2.2)–(2.4): the Villain measure
`dμ_β(θ_Λ) = Ẑ_Λ⁻¹ ∏_{p ⊂ Λ} φ_β(dθ_p) ∏_{xy ⊂ Λ} dθ_xy` of the `U(1)` lattice gauge theory in the
box `Λ` of `R`, at `β > 0`, with `φ_β(θ) = ∑_{n ∈ ℤ} exp (-(β/2) (θ + 2πn)²)`: the measure on the
angle configurations `θ : PrimalLinks R → ℝ` with density `∏_p φ_β(dθ_p)` with respect to
`∏_{xy} 𝟙_{[-π, π)}(θ_xy) dθ_xy`, divided by its total mass `Ẑ_Λ`. -/
noncomputable def primalVillainLaw (R : RectBox4) (β : ℝ) (_hβ : 0 < β) :
    MeasureTheory.Measure (PrimalLinks R → ℝ) :=
  let μ : MeasureTheory.Measure (PrimalLinks R → ℝ) :=
    (MeasureTheory.Measure.pi fun _ : PrimalLinks R =>
        MeasureTheory.volume.restrict (Set.Ico (-Real.pi) Real.pi)).withDensity
      fun θ => ∏ p : PrimalPlaquettes R,
        ∑' n : ℤ, ENNReal.ofReal
          (Real.exp (-(β / 2) * (primalPlaquetteCurl R θ p + 2 * Real.pi * n) ^ 2))
  (μ Set.univ)⁻¹ • μ

end FroehlichSpencer.FS82.Surface

end
