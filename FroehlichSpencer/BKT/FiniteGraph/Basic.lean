/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Basic.Real.Basic
public import FroehlichSpencer.BKT.Surface.Laplacian
public import FroehlichSpencer.BKT.Surface.MultigraphSimpleGraph

/-!
The carrier `Multigraph` (`src`, `tgt`, `src_ne_tgt`), its underlying simple graph
`Multigraph.toSimpleGraph` and the finite-difference Laplacian `Multigraph.laplacian` (KP (1.1))
are statement in `FroehlichSpencer/BKT/Surface/`; this file re-exports them and adds the
internal API.

A sum over `E` counts each edge exactly once with its multiplicity (KP (1.3), p. 2).
-/

@[expose] public section

namespace FroehlichSpencer.BKT

universe u v

namespace Multigraph

variable {V : Type u} {E : Type v} (G : Multigraph V E)

/-- Two vertices are adjacent when some edge joins them. -/
def Adj (j ℓ : V) : Prop :=
  ∃ e, (G.src e = j ∧ G.tgt e = ℓ) ∨ (G.src e = ℓ ∧ G.tgt e = j)

/--
The underlying simple graph is `SimpleGraph.fromRel G.Adj`.
-/
theorem toSimpleGraph_eq_fromRel_adj : G.toSimpleGraph = SimpleGraph.fromRel G.Adj := rfl

/-- A multigraph is connected when its underlying simple graph is (in particular `V` is
nonempty). -/
def Connected : Prop := G.toSimpleGraph.Connected

/-- The gradient of `f` along an edge, `f (src e) - f (tgt e)`. -/
def grad {R : Type*} [Sub R] (f : V → R) (e : E) : R := f (G.src e) - f (G.tgt e)

/-- The Dirichlet energy `∑_e (f (src e) - f (tgt e))^2`, each edge counted once (KP (1.3)). -/
def energy [Fintype E] (f : V → ℝ) : ℝ := ∑ e, G.grad f e ^ 2

/-- The pairing `⟨f, g⟩ = ∑_j f j * g j` of KP p. 2. -/
def pairing [Fintype V] {R : Type*} [CommRing R] (f g : V → R) : R := ∑ j, f j * g j

end Multigraph

end FroehlichSpencer.BKT

end
