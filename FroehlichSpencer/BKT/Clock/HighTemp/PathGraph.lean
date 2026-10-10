/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.HighTemp.PathTools
public import FroehlichSpencer.BKT.Clock.Compact.Theorem71

/-! # The full free-box selected-bond graph -/

@[expose] public section

namespace FroehlichSpencer.BKT.Clock.HighTemp

open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.SpinWaves

/-- The graph containing every oriented internal bond of the free square. -/
abbrev fullBondGraph (L : ℕ) :=
  selectedBondGraph L (Finset.univ : Finset (RotatorInternalBond L))

/-- The selected bond labels used by a path in the full graph. -/
def pathBondSet {L : ℕ} {u v : RotatorSpinSite L}
    (p : (fullBondGraph L).Path u v) : Finset (RotatorInternalBond L) :=
  selectedPathBondFinset (Finset.univ : Finset (RotatorInternalBond L)) p.1

/-- Full-graph distance on the free square is its Manhattan radius. -/
theorem fullBondGraph_dist_eq_freeRadius (L : ℕ) (a b : RotatorSpinSite L) :
    (fullBondGraph L).dist a b = freeRadius a b := by
  cases L with
  | zero =>
      have hab : a = b := by
        apply Prod.ext
        · apply Fin.ext
          omega
        · apply Fin.ext
          omega
      subst b
      simp [fullBondGraph, freeRadius]
  | succ L =>
      change (selectedBondGraph (L + 1)
        (Finset.univ : Finset (RotatorInternalBond (L + 1)))).dist a b = _
      rw [selectedBondGraph_univ_eq_toSimpleGraph]
      rw [rotatorFreeGraph]
      let I := FroehlichSpencer.BKT.squareFreeGraphIsomorphism (L + 1 + 1)
      calc
        (squareFreeGraph (L + 1 + 1)).toSimpleGraph.dist a b =
            (FroehlichSpencer.BKT.squareFree (L + 1 + 1)).toSimpleGraph.dist a b :=
              (Multigraph.Isomorphism.dist_transport I a b).symm
        _ = freeRadius a b := squareFree_dist_eq_freeRadius (by simp) a b

end FroehlichSpencer.BKT.Clock.HighTemp

end
