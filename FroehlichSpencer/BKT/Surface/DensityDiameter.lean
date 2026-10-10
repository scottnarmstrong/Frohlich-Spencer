/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Basic
public import FroehlichSpencer.BKT.Surface.MultigraphSimpleGraph

/-! # The diameter `d(ϱ)` of a charge density (KP §1.7.1) -/

@[expose] public section

namespace FroehlichSpencer.BKT

universe u v

/-- The diameter `d(ϱ) = max_{i, j ∈ supp ϱ} dist (i, j)` (KP p. 5) of `ϱ : V → ℤ`, with `dist` the
graph distance of `G`. KP define it for densities (`ϱ ≠ 0`, so `supp ϱ` is nonempty); the same
formula gives `0` at `ϱ = 0`. -/
noncomputable def Multigraph.densityDiameter {V : Type u} {E : Type v} [Fintype V] (G : Multigraph V E)
    (ϱ : V → ℤ) : ℕ :=
  ((Finset.univ.filter fun j => ϱ j ≠ 0) ×ˢ (Finset.univ.filter fun j => ϱ j ≠ 0)).sup
    fun p => G.toSimpleGraph.dist p.1 p.2

end FroehlichSpencer.BKT

end
