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
public import FroehlichSpencer.FS82.Surface.LatticeIsEdge
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalPlaquetteAxes
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalPlaquette
public import FroehlichSpencer.FS82.SurfaceInfinite.LatticePoint
public import FroehlichSpencer.FS82.SurfaceInfinite.SourcePointCoordinate
public import FroehlichSpencer.FS82.SurfaceInfinite.DualCurvatureCell

@[expose] public section

open MeasureTheory
open Filter Topology
open scoped ComplexConjugate

open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.SurfaceInfinite

noncomputable section

noncomputable def dualCurvatureAt (x : LatticePoint) : GlobalPlaquette := by
  refine ⟨dualCurvatureCell x, ?_⟩
  classical
  have haxes : globalPlaquetteAxes (dualCurvatureCell x) = {0, 1} := by
    classical
    ext i
    change i ∈ Finset.univ.filter (fun j : Fin 4 =>
      latticeIsEdge (dualCurvatureCell x j)) ↔ i ∈ ({0, 1} : Finset (Fin 4))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    by_cases hi : i = 0 ∨ i = 1
    · simp [dualCurvatureCell, hi, latticeIsEdge]
    · simp [dualCurvatureCell, hi, latticeIsEdge]
  rw [haxes]
  decide

end
end FroehlichSpencer.FS82.SurfaceInfinite

end
