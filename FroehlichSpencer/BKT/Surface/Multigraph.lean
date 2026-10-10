/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Init

/-! # Finite oriented multigraphs -/

public section

namespace FroehlichSpencer.BKT

universe u v

/-- A multigraph with vertex type `V` and edge type `E` (KP p. 2): each edge has two distinct
endpoints `src e` and `tgt e`, listed in an arbitrary orientation. Parallel edges are distinct
elements of `E`, so a sum or product over `E` counts each edge exactly once, with multiplicity. -/
structure Multigraph (V : Type u) (E : Type v) where
  /-- The first endpoint of an edge (in the chosen orientation). -/
  src : E → V
  /-- The second endpoint of an edge (in the chosen orientation). -/
  tgt : E → V
  /-- Edges are not loops. -/
  src_ne_tgt : ∀ e, src e ≠ tgt e

end FroehlichSpencer.BKT

end
