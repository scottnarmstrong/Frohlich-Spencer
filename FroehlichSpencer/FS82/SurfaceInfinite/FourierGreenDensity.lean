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
public import FroehlichSpencer.FS82.Surface.RealLatticeChain
public import FroehlichSpencer.FS82.Surface.LatticeIsEdge
public import FroehlichSpencer.FS82.SurfaceInfinite.LatticePoint
public import FroehlichSpencer.FS82.SurfaceInfinite.Torus4
public import FroehlichSpencer.FS82.SurfaceInfinite.CellDegree
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalLinkField
public import FroehlichSpencer.FS82.SurfaceInfinite.CellBaseCoordinate
public import FroehlichSpencer.FS82.SurfaceInfinite.CellPoint
public import FroehlichSpencer.FS82.SurfaceInfinite.LinkAxisCell
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalLinkAxisSupport
public import FroehlichSpencer.FS82.SurfaceInfinite.LatticeCharacter
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalLinkFourierComponent
public import FroehlichSpencer.FS82.SurfaceInfinite.FourierLaplacianSymbol

@[expose] public section

open MeasureTheory
open Filter Topology
open scoped ComplexConjugate

open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.SurfaceInfinite

noncomputable section

def fourierGreenDensity (μ : GlobalLinkField) (k : Torus4) : ℝ :=
  ∑ i : Fin 4,
    ‖globalLinkFourierComponent μ i k‖ ^ 2 / fourierLaplacianSymbol k

end
end FroehlichSpencer.FS82.SurfaceInfinite

end
