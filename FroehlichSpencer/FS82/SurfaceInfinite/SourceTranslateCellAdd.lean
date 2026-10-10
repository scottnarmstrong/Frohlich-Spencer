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
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceLatticeShift
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslateCoordinate
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslateCell

@[expose] public section

open MeasureTheory
open Filter Topology
open scoped ComplexConjugate

open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.SurfaceInfinite

noncomputable section

theorem sourceTranslateCell_add (a b : SourceLatticeShift) (c : LatticeCell) :
    sourceTranslateCell a (sourceTranslateCell b c) = sourceTranslateCell (a + b) c := by
  funext i
  cases hc : c i <;>
    simp [sourceTranslateCell, sourceTranslateCoordinate, hc, Pi.add_apply,
      add_left_comm, add_comm]

end
end FroehlichSpencer.FS82.SurfaceInfinite

end
