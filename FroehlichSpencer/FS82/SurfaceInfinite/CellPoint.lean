/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import FroehlichSpencer.FS82.Surface.LatticeCoord
public import FroehlichSpencer.FS82.Surface.LatticeCell
public import FroehlichSpencer.FS82.SurfaceInfinite.LatticePoint
public import FroehlichSpencer.FS82.SurfaceInfinite.CellBaseCoordinate

@[expose] public section

open MeasureTheory
open Filter Topology
open scoped ComplexConjugate

open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.SurfaceInfinite

noncomputable section

def cellPoint (c : LatticeCell) : LatticePoint :=
  (cellBaseCoordinate c 0,
    (cellBaseCoordinate c 1,
      (cellBaseCoordinate c 2, cellBaseCoordinate c 3)))

end
end FroehlichSpencer.FS82.SurfaceInfinite

end
