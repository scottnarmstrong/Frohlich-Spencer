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
public import FroehlichSpencer.FS82.Surface.PrimalCoord
public import FroehlichSpencer.FS82.Surface.PrimalCell
public import FroehlichSpencer.FS82.Surface.PrimalCellDegree
public import FroehlichSpencer.FS82.Surface.PrimalLinks
public import FroehlichSpencer.FS82.Surface.PrimalLinksFintype
public import FroehlichSpencer.FS82.Surface.PrimalCellEmbedding

/-! FS82 perimeter surface definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

/-- FS82 (2.5): the Wilson loop `W(ℒ) = ∏_{xy ∈ ℒ} e^{iθ_xy}` of an integer lattice chain `loop`,
on the angle configurations of the box of `R`. A link of the box enters with the power that `loop`
gives it; a link outside the box does not enter. -/
noncomputable def wilsonLoopObservable (R : RectBox4) (loop : LatticeChain)
    (θ : PrimalLinks R → ℝ) : ℂ :=
  ∏ ℓ : PrimalLinks R,
    Complex.exp (Complex.I * (((loop (primalCellEmbedding R ℓ.1) : ℤ) : ℝ) * θ ℓ : ℝ))

end FroehlichSpencer.FS82.Surface

end
