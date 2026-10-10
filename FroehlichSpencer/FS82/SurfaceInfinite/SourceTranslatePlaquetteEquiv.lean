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
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceLatticeShift
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslateCoordinate
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslateCell
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslateCellAdd
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslateCellZero
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceGlobalPlaquetteAxesTranslate

@[expose] public section

open MeasureTheory
open Filter Topology
open scoped ComplexConjugate

open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.SurfaceInfinite

noncomputable section

noncomputable def sourceTranslatePlaquetteEquiv (a : SourceLatticeShift) :
    GlobalPlaquette ≃ GlobalPlaquette where
  toFun p := ⟨sourceTranslateCell a p.1, by
    rw [sourceGlobalPlaquetteAxes_translate]
    exact p.2⟩
  invFun p := ⟨sourceTranslateCell (-a) p.1, by
    rw [sourceGlobalPlaquetteAxes_translate]
    exact p.2⟩
  left_inv p := by
    apply Subtype.ext
    change sourceTranslateCell (-a) (sourceTranslateCell a p.1) = p.1
    rw [sourceTranslateCell_add]
    simp [sourceTranslateCell_zero]
  right_inv p := by
    apply Subtype.ext
    change sourceTranslateCell a (sourceTranslateCell (-a) p.1) = p.1
    rw [sourceTranslateCell_add]
    simp [sourceTranslateCell_zero]

end
end FroehlichSpencer.FS82.SurfaceInfinite

end
