/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import FroehlichSpencer.BKT.Surface.MultigraphSimpleGraph
public import FroehlichSpencer.BKT.Charges.Squares

/-! # Distances for finite square domains

KP §2 uses the nearest-neighbor graph distance on the free box and its quotient
distance on the periodic box (KP p. 2). On the square lattice these are the
Manhattan distance and the sum of the two cyclic coordinate distances. -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The nearest-neighbor graph distance on the free or periodic square domain. -/
noncomputable def latticeDistance (boundary : SquareBoundary) (L : ℕ)
    (x y : Fin L × Fin L) : ℕ :=
  match boundary with
  | .free => (squareFree L).toSimpleGraph.dist x y
  | .periodic => (squarePeriodic L).toSimpleGraph.dist x y

/-- The distance between two finite vertex sets, with value zero when one set
is empty. Applications to separated cover squares use nonempty sets. -/
noncomputable def squareDistance (boundary : SquareBoundary) (L : ℕ)
    (s t : Finset (Fin L × Fin L)) : ℕ :=
  if h : (s.product t).Nonempty then
    ((s.product t).image fun p => latticeDistance boundary L p.1 p.2).min'
      (Finset.image_nonempty.mpr h)
  else 0

/-- The diameter of a finite vertex set, with value zero for the empty set. -/
noncomputable def squareDiameter (boundary : SquareBoundary) (L : ℕ)
    (s : Finset (Fin L × Fin L)) : ℕ :=
  if h : (s.product s).Nonempty then
    ((s.product s).image fun p => latticeDistance boundary L p.1 p.2).max'
      (Finset.image_nonempty.mpr h)
  else 0

end FroehlichSpencer.BKT

end
