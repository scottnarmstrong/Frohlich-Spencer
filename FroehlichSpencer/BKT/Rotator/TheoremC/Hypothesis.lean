/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.TheoremC.Defs
public import FroehlichSpencer.BKT.Generic.Rooted.Layer
public import FroehlichSpencer.BKT.Surface.SquareZero

/-!
# The pinned charge-layer hypothesis of FS81 Theorem C

FS81 Theorem C for the plane rotator is assembled in this directory **conditional on one
explicit hypothesis**: the FS81 Appendix D charge layer of the pinned finite carrier (FS81 (1.35),
zero exterior heights; J pp. 603–606), read on the augmented graph `squareZero L` rooted at its
wired vertex `none` (the terminal decomposition's `Generic/PinnedCharges/WiredAdapter.lean`), in the restricted-domain form
consumed by `integral_shift_ge_of_rootedLayer` (`Generic/Rooted/Moment.lean`).

For every large box `L` and comb cutoff `N`, a `PinnedLayerWitness` provides
* a `RootedChargeLayer (squareZero L) none (pinnedCombLam L N) centerOf A Zent D₁ D₂ α K₀ K₁`:
  the convex character expansion of the root-relative comb `∏_x D_N(ψ_x − ψ_root)` on fields with
  `ψ root = 0`, all densities neutral (charges neutralized at the wired vertex), the entropy bound
  `|K| ≤ e^{D₂ A} Z`, and graded spin waves with the spin-wave clauses whose pieces have their gradients on
  the local edge sets `S_i(ϱ)`;
* its local geometry `IsLocal dsc Kv Kov`: a size `dsc(ϱ) ≥ 1` (Appendix D's `d_Λ`), local edge
  counts `|S_i(ϱ)| ≤ Kv (dsc + 1)²`, an integer routing of `ϱ` inside `S_i(ϱ)`, bounded same-band
  overlap, and the cover bound `log₂(dsc + 1) ≤ A(ϱ)`;
* the exponential entropy bound `Z(ϱ) ≤ e^{a₁ ∑|ϱ| + a₂ A(ϱ)}`.

`PinnedLayerHypothesis` asks for such witnesses with constants uniform in `L` and `N`. It is the
only input of `theoremC_of_pinnedLayer` beyond theorems. The square-domain volume hypothesis
`hvol` is deliberately not used: on `squareZero L` the wired root has degree `4L`, and the graph
balls `densityDomain` around boundary faces contain it, so a uniform `hvol` is false there.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.TheoremC

open FroehlichSpencer.BKT.Generic

/-- The Appendix D data on one augmented box `squareZero L` at comb cutoff `N`, with constants
`D₁ D₂ α K₀ K₁` (layer), `Kv Kov` (locality) and `a₁ a₂` (entropy). -/
structure PinnedLayerWitness (L N : ℕ) (D₁ D₂ α K₀ K₁ Kv a₁ a₂ : ℝ) (Kov : ℕ) where
  /-- The density centers. -/
  centerOf : (RotatorDualFace L → ℤ) → RotatorDualFace L
  /-- The cover cost `A(ϱ)`. -/
  A : (RotatorDualFace L → ℤ) → ℝ
  /-- The entropy factor `Z(ϱ)`. -/
  Zent : (RotatorDualFace L → ℤ) → ℝ
  /-- The rooted charge layer of the root-relative comb. -/
  layer : RootedChargeLayer (squareZero L) none (pinnedCombLam L N) centerOf A Zent
    D₁ D₂ α K₀ K₁
  /-- The density sizes (Appendix D's `d_Λ`). -/
  dsc : (RotatorDualFace L → ℤ) → ℕ
  /-- The local geometry. -/
  isLocal : layer.IsLocal dsc Kv Kov
  /-- The exponential entropy bound. -/
  entropy_exp : ∀ ϱ : RotatorDualFace L → ℤ,
    Zent ϱ ≤ Real.exp (a₁ * ∑ j, |(ϱ j : ℝ)| + a₂ * A ϱ)

/-- **The pinned charge-layer hypothesis** (FS81 Appendix D on the augmented carrier): witnesses
for every box `L ≥ L₀` and every comb cutoff `N ≥ 1`, with uniform constants. -/
def PinnedLayerHypothesis : Prop :=
  ∃ (D₁ D₂ α K₀ K₁ Kv a₁ a₂ : ℝ) (Kov L₀ : ℕ),
    1 < α ∧ 0 < K₀ ∧ 0 < K₁ ∧ 0 < D₁ ∧ 0 ≤ Kv ∧
    ∀ L : ℕ, L₀ ≤ L → ∀ N : ℕ, 1 ≤ N →
      Nonempty (PinnedLayerWitness L N D₁ D₂ α K₀ K₁ Kv a₁ a₂ Kov)

end FroehlichSpencer.BKT.Rotator.TheoremC

end
