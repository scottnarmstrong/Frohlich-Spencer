/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.EdgeLaw.Defs

/-! # The pinned-gradient mismatch in the current `ChargeLayer` API

`ChargeLayer` and `HasLayerWave` take a `Multigraph` gradient on a freely
varying vertex field. A boundary edge of a `PinnedGraph` has a nonzero linear
gradient on constant fields. Thus the pinned gradient cannot be identified
with a `Multigraph.grad` on the same vertex carrier when a boundary edge is
present.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator.Contour

theorem no_multigraph_grad_eq_pinnedGradLinear_of_boundaryEdge
    {V E : Type*} [Fintype V] [DecidableEq V]
    (P : PinnedGraph V E) (G : Multigraph V E)
    (e : E) (he : P.tail e = none) :
    ¬ ∀ a : V → ℝ, ∀ f : E, G.grad a f = pinnedGradLinear P a f := by
  intro h
  have hconst := h (fun _ : V => (1 : ℝ)) e
  have hpinned : pinnedGradLinear P (fun _ : V => (1 : ℝ)) e = 1 := by
    simp [pinnedGradLinear, he]
  have hgraph : G.grad (fun _ : V => (1 : ℝ)) e = 0 := by
    simp [Multigraph.grad]
  have hzeroone : (0 : ℝ) = 1 := by
    calc
      0 = G.grad (fun _ : V => (1 : ℝ)) e := hgraph.symm
      _ = pinnedGradLinear P (fun _ => 1) e := hconst
      _ = 1 := hpinned
  norm_num at hzeroone

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
