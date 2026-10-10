/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import FroehlichSpencer.BKT.Surface.Multigraph

/-! # The finite-difference Laplacian -/

@[expose] public section

namespace FroehlichSpencer.BKT

universe u v

/-- The finite-difference Laplacian of KP (1.1): `(Δ f)(j) = ∑_{ℓ ∼ j} (f ℓ - f j)`, both terms
inside the sum, the sum running over the edges at `j` counted with multiplicity. -/
def Multigraph.laplacian {V : Type u} {E : Type v} (G : Multigraph V E) [Fintype E]
    [DecidableEq V] {R : Type*} [AddCommGroup R] (f : V → R) (j : V) : R :=
  ∑ e, ((if G.src e = j then f (G.tgt e) - f j else 0) +
    (if G.tgt e = j then f (G.src e) - f j else 0))

end FroehlichSpencer.BKT

end
