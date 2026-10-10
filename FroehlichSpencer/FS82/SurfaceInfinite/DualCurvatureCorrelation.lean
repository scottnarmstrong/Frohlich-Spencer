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
public import FroehlichSpencer.FS82.SurfaceInfinite.DualCurvatureAt
public import FroehlichSpencer.FS82.SurfaceInfinite.PairPlaquettes
public import FroehlichSpencer.FS82.SurfaceInfinite.PairProduct
public import FroehlichSpencer.FS82.SurfaceInfinite.CurvatureCylinderState

@[expose] public section

open MeasureTheory
open Filter Topology
open scoped ComplexConjugate

open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.SurfaceInfinite

noncomputable section

noncomputable def dualCurvatureCorrelation
    (S : CurvatureCylinderState) (d : LatticePoint) : ℝ :=
  ∫ ω, pairProduct 0 d ω ∂ (S.law (pairPlaquettes 0 d)).toMeasure

end
end FroehlichSpencer.FS82.SurfaceInfinite

end
