/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.DensityDiameter

/-! # Admissible centers of a charge density (KP §1.7.1) -/

@[expose] public section

namespace FroehlichSpencer.BKT

universe u v

/-- `j` is an admissible center of `ϱ` (KP p. 5): `j ∈ supp ϱ` and there is `k ∈ supp ϱ` with
`d(ϱ) = dist (j, k)`. KP choose one admissible center per density "in some fixed arbitrary way". -/
def Multigraph.IsDensityCenter {V : Type u} {E : Type v} [Fintype V] (G : Multigraph V E)
    (ϱ : V → ℤ) (j : V) : Prop :=
  ϱ j ≠ 0 ∧ ∃ k : V, ϱ k ≠ 0 ∧ G.densityDiameter ϱ = G.toSimpleGraph.dist j k

end FroehlichSpencer.BKT

end
