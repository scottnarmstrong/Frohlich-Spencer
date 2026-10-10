/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import FroehlichSpencer.BKT.Surface.Multigraph

/-! # The simple graph underlying a multigraph -/

@[expose] public section

namespace FroehlichSpencer.BKT

universe u v

/-- The simple graph underlying a multigraph: distinct vertices `j`, `ℓ` are adjacent
(`j ∼ ℓ`, KP p. 2) when some edge joins them. KP's graph distance `dist` and connectedness are
those of this graph; edge multiplicities play no role in them. -/
def Multigraph.toSimpleGraph {V : Type u} {E : Type v} (G : Multigraph V E) : SimpleGraph V :=
  SimpleGraph.fromRel fun j ℓ => ∃ e, (G.src e = j ∧ G.tgt e = ℓ) ∨ (G.src e = ℓ ∧ G.tgt e = j)

end FroehlichSpencer.BKT

end
