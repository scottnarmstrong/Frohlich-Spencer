/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import FroehlichSpencer.BKT.Surface.SquareFree

/-! # The wired square domain `Λ_L^zero` -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The square domain `Λ_L^zero` with zero (wired) boundary conditions (KP p. 2): the vertices
of `Λ_L^free` together with the wired vertex `z = none`; the edges of `Λ_L^free` (left summand),
and, for each vertex `j` of `Λ_L^free`, `4 - deg j` parallel edges `{j, z}` (right summand), where
`deg j` is the degree of `j` in `Λ_L^free`. KP take `L > 1`. -/
def squareZero (L : ℕ) : Multigraph (Option (Fin L × Fin L))
    (SquareFreeEdge L ⊕ Σ j : Fin L × Fin L,
      Fin (4 - (Finset.univ.filter fun e : SquareFreeEdge L =>
        (squareFree L).src e = j ∨ (squareFree L).tgt e = j).card)) where
  src := Sum.elim (fun e => some ((squareFree L).src e)) (fun b => some b.1)
  tgt := Sum.elim (fun e => some ((squareFree L).tgt e)) (fun _ => none)
  src_ne_tgt
    | .inl e => Option.some_injective _ |>.ne ((squareFree L).src_ne_tgt e)
    | .inr _ => Option.some_ne_none _

end FroehlichSpencer.BKT

end
