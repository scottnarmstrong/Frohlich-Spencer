/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.Multigraph
public import FroehlichSpencer.BKT.Surface.SquareFreeEdge

/-! # The free square domain `Λ_L^free` -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The square domain `Λ_L^free` with free boundary conditions (KP p. 2): vertices
`{0, …, L - 1}²`, edges `SquareFreeEdge L`, each oriented from its lexicographically smaller
endpoint. KP take `L > 1`. -/
def squareFree (L : ℕ) : Multigraph (Fin L × Fin L) (SquareFreeEdge L) where
  src e := e.1.1
  tgt e := e.1.2
  src_ne_tgt e h := lt_irrefl (toLex e.1.2) (h ▸ e.2.1)

end FroehlichSpencer.BKT

end
